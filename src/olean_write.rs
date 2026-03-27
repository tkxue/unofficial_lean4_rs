//! Write .olean files — serialize Environment to Lean's compact binary format.

use std::collections::HashMap;
use std::path::Path;

use crate::env::*;
use crate::expr::*;
use crate::level::Level;
use crate::name::Name;
use crate::olean::ModuleData;

// ============================================================================
// Object Compactor — builds a byte buffer with Lean object layout
// ============================================================================

pub struct Compactor {
    buf: Vec<u8>,
    base_addr: u64,
    // Dedup: track already-written objects by identity
    name_offsets: HashMap<u64, u64>,  // name hash → offset
    level_offsets: HashMap<u64, u64>,
    expr_offsets: HashMap<u64, u64>,
    string_offsets: HashMap<String, u64>,
}

const TAG_STRING: u8 = 249;
const TAG_ARRAY: u8 = 246;

impl Compactor {
    pub fn new(base_addr: u64) -> Self {
        Compactor {
            buf: Vec::with_capacity(1024 * 1024),
            base_addr,
            name_offsets: HashMap::new(),
            level_offsets: HashMap::new(),
            expr_offsets: HashMap::new(),
            string_offsets: HashMap::new(),
        }
    }

    fn alloc(&mut self, size: usize) -> usize {
        let rem = size % 8;
        let aligned = if rem == 0 { size } else { size + 8 - rem };
        let offset = self.buf.len();
        self.buf.resize(offset + aligned, 0);
        offset
    }

    fn offset_to_ptr(&self, offset: usize) -> u64 {
        self.base_addr + offset as u64
    }

    fn write_u64(&mut self, offset: usize, val: u64) {
        self.buf[offset..offset+8].copy_from_slice(&val.to_le_bytes());
    }

    fn write_u32(&mut self, offset: usize, val: u32) {
        self.buf[offset..offset+4].copy_from_slice(&val.to_le_bytes());
    }

    fn write_u16(&mut self, offset: usize, val: u16) {
        self.buf[offset..offset+2].copy_from_slice(&val.to_le_bytes());
    }

    fn write_u8(&mut self, offset: usize, val: u8) {
        self.buf[offset] = val;
    }

    /// Write a non-heap object header.
    /// m_rc=0, m_cs_sz=byte_size, m_other=num_objs, m_tag=tag
    fn write_header(&mut self, offset: usize, byte_size: u16, num_objs: u8, tag: u8) {
        self.write_u32(offset, 0);          // m_rc = 0 (non-heap)
        self.write_u16(offset + 4, byte_size);
        self.write_u8(offset + 6, num_objs);
        self.write_u8(offset + 7, tag);
    }

    fn scalar_ptr(val: u64) -> u64 {
        (val << 1) | 1
    }

    // -- String --------------------------------------------------------------

    fn write_string(&mut self, s: &str) -> u64 {
        if let Some(&ptr) = self.string_offsets.get(s) { return ptr; }
        let bytes = s.as_bytes();
        let size = bytes.len() + 1; // include null terminator
        let obj_size = 32 + size;
        let offset = self.alloc(obj_size);
        // header: tag=249 (string), other=0
        self.write_header(offset, 1, 0, TAG_STRING); // cs_sz=1 for big objects
        self.write_u64(offset + 8, size as u64);      // m_size
        self.write_u64(offset + 16, size as u64);     // m_capacity
        self.write_u64(offset + 24, s.chars().count() as u64); // m_length (char count)
        self.buf[offset + 32..offset + 32 + bytes.len()].copy_from_slice(bytes);
        self.buf[offset + 32 + bytes.len()] = 0; // null terminator
        let ptr = self.offset_to_ptr(offset);
        self.string_offsets.insert(s.to_string(), ptr);
        ptr
    }

    // -- Name ----------------------------------------------------------------

    pub fn write_name(&mut self, name: &Name) -> u64 {
        if name.is_anonymous() { return Self::scalar_ptr(0); }
        let key = name.hash();
        if let Some(&ptr) = self.name_offsets.get(&key) { return ptr; }
        let prefix_ptr = self.write_name(name.get_prefix());
        let (tag, field1_ptr, hash) = if name.is_string() {
            let str_ptr = self.write_string(name.get_string());
            (1u8, str_ptr, name.hash())
        } else {
            let n = name.get_numeral();
            (2u8, Self::scalar_ptr(n), name.hash())
        };
        // Name.str/num: 2 obj fields [prefix, string/nat] + u64 hash scalar
        let byte_size = 8 + 2 * 8 + 8; // header + 2 ptrs + hash
        let offset = self.alloc(byte_size as usize);
        self.write_header(offset, byte_size as u16, 2, tag);
        self.write_u64(offset + 8, prefix_ptr);
        self.write_u64(offset + 16, field1_ptr);
        self.write_u64(offset + 24, hash);
        let ptr = self.offset_to_ptr(offset);
        self.name_offsets.insert(key, ptr);
        ptr
    }

    // -- Level ---------------------------------------------------------------

    pub fn write_level(&mut self, level: &Level) -> u64 {
        if level.is_zero() { return Self::scalar_ptr(0); }
        let key = level.hash();
        if let Some(&ptr) = self.level_offsets.get(&key) { return ptr; }
        let ptr = match level.kind() {
            crate::level::LevelKind::Succ => {
                let inner = self.write_level(level.succ_of());
                let offset = self.alloc(24); // header + 1 ptr + data u64
                self.write_header(offset, 24, 1, 1);
                self.write_u64(offset + 8, inner);
                self.write_u64(offset + 16, level.hash()); // data
                self.offset_to_ptr(offset)
            }
            crate::level::LevelKind::Max => {
                let lhs = self.write_level(level.max_lhs());
                let rhs = self.write_level(level.max_rhs());
                let offset = self.alloc(32);
                self.write_header(offset, 32, 2, 2);
                self.write_u64(offset + 8, lhs);
                self.write_u64(offset + 16, rhs);
                self.write_u64(offset + 24, level.hash());
                self.offset_to_ptr(offset)
            }
            crate::level::LevelKind::IMax => {
                let lhs = self.write_level(level.max_lhs());
                let rhs = self.write_level(level.max_rhs());
                let offset = self.alloc(32);
                self.write_header(offset, 32, 2, 3);
                self.write_u64(offset + 8, lhs);
                self.write_u64(offset + 16, rhs);
                self.write_u64(offset + 24, level.hash());
                self.offset_to_ptr(offset)
            }
            crate::level::LevelKind::Param => {
                let name = self.write_name(level.param_name());
                let offset = self.alloc(24);
                self.write_header(offset, 24, 1, 4);
                self.write_u64(offset + 8, name);
                self.write_u64(offset + 16, level.hash());
                self.offset_to_ptr(offset)
            }
            crate::level::LevelKind::MVar => {
                let name = self.write_name(level.param_name());
                // LMVarId wrapper: 1 obj field [name]
                let mvarid_offset = self.alloc(16);
                self.write_header(mvarid_offset, 16, 1, 0);
                self.write_u64(mvarid_offset + 8, name);
                let mvarid_ptr = self.offset_to_ptr(mvarid_offset);
                let offset = self.alloc(24);
                self.write_header(offset, 24, 1, 5);
                self.write_u64(offset + 8, mvarid_ptr);
                self.write_u64(offset + 16, level.hash());
                self.offset_to_ptr(offset)
            }
            _ => Self::scalar_ptr(0),
        };
        self.level_offsets.insert(key, ptr);
        ptr
    }

    // -- Expr ----------------------------------------------------------------

    pub fn write_expr(&mut self, expr: &Expr) -> u64 {
        let data = expr.hash() as u64; // simplified data packing
        match expr.kind() {
            ExprKind::BVar => {
                let idx = expr.bvar_idx();
                let offset = self.alloc(24);
                self.write_header(offset, 24, 1, 0);
                self.write_u64(offset + 8, Self::scalar_ptr(idx));
                self.write_u64(offset + 16, data);
                self.offset_to_ptr(offset)
            }
            ExprKind::Sort => {
                let lvl = self.write_level(expr.sort_level());
                let offset = self.alloc(24);
                self.write_header(offset, 24, 1, 3);
                self.write_u64(offset + 8, lvl);
                self.write_u64(offset + 16, data);
                self.offset_to_ptr(offset)
            }
            ExprKind::Const => {
                let name = self.write_name(expr.const_name());
                let levels = self.write_level_list(expr.const_levels());
                let offset = self.alloc(32);
                self.write_header(offset, 32, 2, 4);
                self.write_u64(offset + 8, name);
                self.write_u64(offset + 16, levels);
                self.write_u64(offset + 24, data);
                self.offset_to_ptr(offset)
            }
            ExprKind::App => {
                let f = self.write_expr(expr.app_fn());
                let a = self.write_expr(expr.app_arg());
                let offset = self.alloc(32);
                self.write_header(offset, 32, 2, 5);
                self.write_u64(offset + 8, f);
                self.write_u64(offset + 16, a);
                self.write_u64(offset + 24, data);
                self.offset_to_ptr(offset)
            }
            ExprKind::Lambda | ExprKind::Pi => {
                let tag = if expr.is_lambda() { 6 } else { 7 };
                let name = self.write_name(expr.binding_name());
                let ty = self.write_expr(expr.binding_domain());
                let body = self.write_expr(expr.binding_body());
                let offset = self.alloc(40);
                self.write_header(offset, 40, 3, tag);
                self.write_u64(offset + 8, name);
                self.write_u64(offset + 16, ty);
                self.write_u64(offset + 24, body);
                self.write_u64(offset + 32, data); // data + binder_info packed
                self.offset_to_ptr(offset)
            }
            _ => {
                // Placeholder for other expr kinds
                let offset = self.alloc(16);
                self.write_header(offset, 16, 0, 0);
                self.write_u64(offset + 8, data);
                self.offset_to_ptr(offset)
            }
        }
    }

    fn write_level_list(&mut self, levels: &[Level]) -> u64 {
        let mut ptr = Self::scalar_ptr(0); // nil
        for lvl in levels.iter().rev() {
            let head = self.write_level(lvl);
            let offset = self.alloc(24);
            self.write_header(offset, 24, 2, 1); // List.cons
            self.write_u64(offset + 8, head);
            self.write_u64(offset + 16, ptr);
            ptr = self.offset_to_ptr(offset);
        }
        ptr
    }

    fn write_name_list(&mut self, names: &[Name]) -> u64 {
        let mut ptr = Self::scalar_ptr(0);
        for name in names.iter().rev() {
            let head = self.write_name(name);
            let offset = self.alloc(24);
            self.write_header(offset, 24, 2, 1);
            self.write_u64(offset + 8, head);
            self.write_u64(offset + 16, ptr);
            ptr = self.offset_to_ptr(offset);
        }
        ptr
    }

    fn write_array(&mut self, ptrs: &[u64]) -> u64 {
        let obj_size = 24 + ptrs.len() * 8;
        let offset = self.alloc(obj_size);
        self.write_header(offset, 1, 0, TAG_ARRAY); // big object marker
        self.write_u64(offset + 8, ptrs.len() as u64);
        self.write_u64(offset + 16, ptrs.len() as u64);
        for (i, &p) in ptrs.iter().enumerate() {
            self.write_u64(offset + 24 + i * 8, p);
        }
        self.offset_to_ptr(offset)
    }

    // -- ModuleData ----------------------------------------------------------

    pub fn write_module_data(&mut self, md: &ModuleData, constants: &[ConstantInfo]) -> u64 {
        // Write imports array
        let import_ptrs: Vec<u64> = md.imports.iter().map(|imp| {
            let name = self.write_name(&imp.module);
            let offset = self.alloc(16);
            self.write_header(offset, 16, 1, 0);
            self.write_u64(offset + 8, name);
            self.write_u8(offset + 16, imp.is_exported as u8);
            self.offset_to_ptr(offset)
        }).collect();
        let imports_arr = self.write_array(&import_ptrs);

        // Write constNames array
        let name_ptrs: Vec<u64> = constants.iter().map(|ci| self.write_name(&ci.name)).collect();
        let names_arr = self.write_array(&name_ptrs);

        // Write constants array (simplified — just types, skip values)
        let const_ptrs: Vec<u64> = constants.iter().map(|ci| {
            self.write_constant_info(ci)
        }).collect();
        let consts_arr = self.write_array(&const_ptrs);

        // Write extraConstNames (empty)
        let extra_arr = self.write_array(&[]);

        // Write entries (empty)
        let entries_arr = self.write_array(&[]);

        // Root: ModuleData constructor (tag 0, 5 obj fields, 8 scalar bytes)
        let offset = self.alloc(56); // 8 + 5*8 + 8
        self.write_header(offset, 56, 5, 0);
        self.write_u64(offset + 8, imports_arr);
        self.write_u64(offset + 16, names_arr);
        self.write_u64(offset + 24, consts_arr);
        self.write_u64(offset + 32, extra_arr);
        self.write_u64(offset + 40, entries_arr);
        self.write_u8(offset + 48, 1); // isModule = true
        self.offset_to_ptr(offset)
    }

    fn write_constant_info(&mut self, ci: &ConstantInfo) -> u64 {
        // ConstantVal: 3 obj fields [name, lparams, type]
        let name = self.write_name(&ci.name);
        let lparams = self.write_name_list(&ci.lparams);
        let type_ = self.write_expr(&ci.type_);
        let cv_offset = self.alloc(32);
        self.write_header(cv_offset, 32, 3, 0);
        self.write_u64(cv_offset + 8, name);
        self.write_u64(cv_offset + 16, lparams);
        self.write_u64(cv_offset + 24, type_);
        let cv_ptr = self.offset_to_ptr(cv_offset);

        // Wrap in the appropriate ConstantInfo variant
        let tag = match &ci.kind {
            ConstantInfoKind::Axiom { .. } => 0,
            ConstantInfoKind::Definition { .. } => 1,
            ConstantInfoKind::Theorem { .. } => 2,
            ConstantInfoKind::Opaque { .. } => 3,
            ConstantInfoKind::Quot { .. } => 4,
            ConstantInfoKind::Inductive { .. } => 5,
            ConstantInfoKind::Constructor { .. } => 6,
            ConstantInfoKind::Recursor { .. } => 7,
        };

        // Simplified: just wrap ConstantVal in the variant
        // Real format has extra fields per variant — we write minimal valid objects
        let inner_offset = self.alloc(24);
        self.write_header(inner_offset, 24, 1, 0); // inner val wrapper
        self.write_u64(inner_offset + 8, cv_ptr);
        let inner_ptr = self.offset_to_ptr(inner_offset);

        let ci_offset = self.alloc(16);
        self.write_header(ci_offset, 16, 1, tag);
        self.write_u64(ci_offset + 8, inner_ptr);
        self.offset_to_ptr(ci_offset)
    }

    pub fn finish(self) -> Vec<u8> { self.buf }
    pub fn base_addr(&self) -> u64 { self.base_addr }
}

// ============================================================================
// Write .olean file
// ============================================================================

pub fn write_olean(
    path: &Path,
    module_name: &Name,
    imports: &[crate::olean::Import],
    constants: &[ConstantInfo],
) -> Result<(), String> {
    let base_addr = module_name.hash() % 0x7f0000000000 & !0xFFFF;
    let mut compactor = Compactor::new(base_addr);

    // Reserve space for olean header (88 bytes)
    compactor.alloc(88);

    // Allocate root pointer slot
    let root_slot = compactor.alloc(8);

    // Write module data
    let md = ModuleData {
        is_module: true,
        imports: imports.to_vec(),
        const_names: constants.iter().map(|c| c.name.clone()).collect(),
        constants: constants.to_vec(),
        extra_const_names: vec![],
    };
    let root_ptr = compactor.write_module_data(&md, constants);

    // Write root pointer
    let buf = compactor.finish();
    let base = Compactor::new(base_addr).base_addr(); // just to get base_addr

    // Build final file
    let mut file = Vec::with_capacity(buf.len());
    // Header
    file.extend_from_slice(b"olean");   // magic
    file.push(2);                        // version
    file.push(0);                        // flags
    let ver = b"4.25.0-rust\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0";
    file.extend_from_slice(&ver[..33]);  // lean_version (33 bytes)
    file.extend_from_slice(&[0u8; 40]); // githash (40 bytes)
    file.extend_from_slice(&base_addr.to_le_bytes()); // base_addr
    // Data (skip the header we reserved in the compactor)
    file.extend_from_slice(&buf[88..]);
    // Fix root pointer
    let root_offset_in_file = root_slot - 88 + 88; // = root_slot
    file[88..96].copy_from_slice(&root_ptr.to_le_bytes());

    std::fs::write(path, &file).map_err(|e| format!("write {}: {}", path.display(), e))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_and_read_back() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let ci = ConstantInfo {
            name: Name::str("myConst"),
            lparams: vec![],
            type_: nat,
            kind: ConstantInfoKind::Axiom { is_unsafe: false },
        };
        let imports = vec![];
        let path = std::path::PathBuf::from("/tmp/test_rust.olean");
        write_olean(&path, &Name::str("Test"), &imports, &[ci]).unwrap();

        // Read back
        let olean = crate::olean::OleanFile::read(&path).unwrap();
        let hdr = olean.header();
        assert_eq!(hdr.version, 2);
        assert!(hdr.lean_version.starts_with("4.25"));
        eprintln!("Wrote and read back .olean: version={}", hdr.version);
    }
}
