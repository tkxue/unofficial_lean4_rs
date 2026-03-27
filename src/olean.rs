//! Stage 12: .olean binary parser.
//!
//! Parses Lean 4's compacted object region format to load ModuleData.

use std::collections::{HashMap as StdHashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::expr::{BinderInfo, Expr, Literal};
use crate::env::*;
use crate::level::Level;
use crate::name::Name;

// ============================================================================
// Constants
// ============================================================================

const OLEAN_MAGIC: &[u8; 5] = b"olean";
const OLEAN_VERSION: u8 = 2;
const HEADER_SIZE: usize = 88; // 5+1+1+33+40+8

// Lean object tags for "big" (non-constructor) objects
const LEAN_MAX_CTOR_TAG: u8 = 243;
const TAG_ARRAY: u8 = 246;
const TAG_STRUCT_ARRAY: u8 = 247;
const TAG_SCALAR_ARRAY: u8 = 248;
const TAG_STRING: u8 = 249;
const TAG_MPZ: u8 = 250;
const TAG_THUNK: u8 = 251;

// ============================================================================
// OleanFile
// ============================================================================

pub struct OleanFile {
    data: Vec<u8>,
    base_addr: u64,
    name_cache: std::cell::RefCell<StdHashMap<u64, Name>>,
    level_cache: std::cell::RefCell<StdHashMap<u64, Level>>,
    expr_cache: std::cell::RefCell<StdHashMap<u64, Expr>>,
}

#[derive(Debug)]
pub struct OleanHeader {
    pub version: u8,
    pub flags: u8,
    pub lean_version: String,
    pub githash: String,
    pub base_addr: u64,
}

/// Parsed module data.
#[derive(Debug)]
pub struct ModuleData {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<Name>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<Name>,
}

#[derive(Debug, Clone)]
pub struct Import {
    pub module: Name,
    pub is_exported: bool,
}

impl OleanFile {
    pub fn read(path: &Path) -> Result<Self, String> {
        let data = std::fs::read(path).map_err(|e| format!("failed to read {}: {}", path.display(), e))?;
        if data.len() < HEADER_SIZE + 8 {
            return Err("file too small for olean header".into());
        }
        if &data[..5] != OLEAN_MAGIC {
            return Err("invalid olean magic".into());
        }
        if data[5] != OLEAN_VERSION {
            return Err(format!("unsupported olean version: {} (expected {})", data[5], OLEAN_VERSION));
        }
        let base_addr = u64::from_le_bytes(data[80..88].try_into().unwrap());
        Ok(OleanFile {
            data,
            base_addr,
            name_cache: std::cell::RefCell::new(StdHashMap::new()),
            level_cache: std::cell::RefCell::new(StdHashMap::new()),
            expr_cache: std::cell::RefCell::new(StdHashMap::new()),
        })
    }

    pub fn header(&self) -> OleanHeader {
        let lean_version = String::from_utf8_lossy(&self.data[7..40])
            .trim_end_matches('\0').to_string();
        let githash = String::from_utf8_lossy(&self.data[40..80])
            .trim_end_matches('\0').to_string();
        OleanHeader {
            version: self.data[5],
            flags: self.data[6],
            lean_version,
            githash,
            base_addr: self.base_addr,
        }
    }

    /// Resolve a stored pointer to a file offset.
    fn fix_ptr(&self, stored: u64) -> Option<usize> {
        if stored & 1 == 1 {
            return None; // scalar
        }
        let offset = stored.wrapping_sub(self.base_addr) as usize;
        if offset >= self.data.len() {
            return None;
        }
        Some(offset)
    }

    fn is_scalar(ptr: u64) -> bool {
        ptr & 1 == 1
    }

    fn unbox(ptr: u64) -> u64 {
        ptr >> 1
    }

    fn read_u8(&self, off: usize) -> u8 { self.data[off] }
    fn read_u16(&self, off: usize) -> u16 { u16::from_le_bytes(self.data[off..off+2].try_into().unwrap()) }
    fn read_u32(&self, off: usize) -> u32 { u32::from_le_bytes(self.data[off..off+4].try_into().unwrap()) }
    fn read_u64(&self, off: usize) -> u64 { u64::from_le_bytes(self.data[off..off+8].try_into().unwrap()) }

    // Object header: [m_rc:i32, m_cs_sz:u16, m_other:u8, m_tag:u8]
    // For non-heap (compacted) objects, m_cs_sz = total byte size of object.
    fn obj_tag(&self, off: usize) -> u8 { self.data[off + 7] }
    fn obj_other(&self, off: usize) -> u8 { self.data[off + 6] }
    fn obj_byte_size(&self, off: usize) -> usize { self.read_u16(off + 4) as usize }
    fn obj_num_objs(&self, off: usize) -> usize { self.obj_other(off) as usize }
    fn obj_field(&self, off: usize, i: usize) -> u64 { self.read_u64(off + 8 + i * 8) }
    fn obj_scalar_start(&self, off: usize) -> usize { off + 8 + self.obj_num_objs(off) * 8 }
    fn obj_scalar_u8(&self, off: usize, i: usize) -> u8 { self.data[self.obj_scalar_start(off) + i] }
    fn obj_scalar_u64(&self, off: usize, i: usize) -> u64 { self.read_u64(self.obj_scalar_start(off) + i) }

    // -- Array parsing -------------------------------------------------------

    fn read_array_ptrs(&self, off: usize) -> Vec<u64> {
        assert_eq!(self.obj_tag(off), TAG_ARRAY, "expected array, got tag {}", self.obj_tag(off));
        let size = self.read_u64(off + 8) as usize;
        let mut ptrs = Vec::with_capacity(size);
        for i in 0..size {
            ptrs.push(self.read_u64(off + 24 + i * 8));
        }
        ptrs
    }

    // -- String parsing ------------------------------------------------------

    fn read_string(&self, off: usize) -> String {
        let tag = self.obj_tag(off);
        if tag != TAG_STRING {
            // Could be an MPZ or other object — return empty
            return String::new();
        }
        let size = self.read_u64(off + 8) as usize; // includes null terminator
        if size == 0 { return String::new(); }
        let start = off + 32; // header(8) + size(8) + capacity(8) + length(8) = 32
        if start + size - 1 > self.data.len() { return String::new(); }
        String::from_utf8_lossy(&self.data[start..start + size - 1]).to_string()
    }

    // -- Name parsing --------------------------------------------------------

    fn read_name(&self, ptr: u64) -> Name {
        if Self::is_scalar(ptr) {
            return Name::anonymous();
        }
        if let Some(cached) = self.name_cache.borrow().get(&ptr) {
            return cached.clone();
        }
        let off = match self.fix_ptr(ptr) {
            Some(o) => o,
            None => return Name::anonymous(),
        };
        let tag = self.obj_tag(off);
        let result = match tag {
            1 => {
                let prefix_ptr = self.obj_field(off, 0);
                let string_ptr = self.obj_field(off, 1);
                let prefix = self.read_name(prefix_ptr);
                let s = match self.fix_ptr(string_ptr) {
                    Some(s_off) => self.read_string(s_off),
                    None => String::new(),
                };
                Name::mk_string(&prefix, &s)
            }
            2 => {
                let prefix_ptr = self.obj_field(off, 0);
                let nat_ptr = self.obj_field(off, 1);
                let prefix = self.read_name(prefix_ptr);
                let n = if Self::is_scalar(nat_ptr) { Self::unbox(nat_ptr) } else { 0 };
                Name::mk_numeral(&prefix, n)
            }
            _ => Name::anonymous(),
        };
        self.name_cache.borrow_mut().insert(ptr, result.clone());
        result
    }

    // -- Level parsing -------------------------------------------------------

    fn read_level(&self, ptr: u64) -> Level {
        if Self::is_scalar(ptr) {
            return Level::zero();
        }
        if let Some(cached) = self.level_cache.borrow().get(&ptr) {
            return cached.clone();
        }
        let off = match self.fix_ptr(ptr) {
            Some(o) => o,
            None => return Level::zero(),
        };
        let tag = self.obj_tag(off);
        let result = match tag {
            1 => { let inner = self.read_level(self.obj_field(off, 0)); Level::mk_succ(&inner) }
            2 => { let l = self.read_level(self.obj_field(off, 0)); let r = self.read_level(self.obj_field(off, 1)); Level::mk_max_core(&l, &r) }
            3 => { let l = self.read_level(self.obj_field(off, 0)); let r = self.read_level(self.obj_field(off, 1)); Level::mk_imax_core(&l, &r) }
            4 => { let name = self.read_name(self.obj_field(off, 0)); Level::mk_param(&name) }
            5 => { let p = self.obj_field(off, 0); let po = self.fix_ptr(p).expect("mvar id"); let name = self.read_name(self.obj_field(po, 0)); Level::mk_mvar(&name) }
            _ => Level::zero(),
        };
        self.level_cache.borrow_mut().insert(ptr, result.clone());
        result
    }

    fn read_levels(&self, ptr: u64) -> Vec<Level> {
        // List Level: scalar = nil, ctor tag 1 = cons(head, tail)
        let mut levels = Vec::new();
        let mut cur = ptr;
        loop {
            if Self::is_scalar(cur) { break; } // nil
            let off = match self.fix_ptr(cur) {
                Some(o) => o,
                None => break,
            };
            let tag = self.obj_tag(off);
            if tag != 1 { break; } // not cons
            let head = self.read_level(self.obj_field(off, 0));
            levels.push(head);
            cur = self.obj_field(off, 1);
        }
        levels
    }

    // -- Expr parsing --------------------------------------------------------

    fn read_expr(&self, ptr: u64) -> Expr {
        if Self::is_scalar(ptr) {
            return Expr::mk_bvar(Self::unbox(ptr));
        }
        if let Some(cached) = self.expr_cache.borrow().get(&ptr) {
            return cached.clone();
        }
        let off = match self.fix_ptr(ptr) {
            Some(o) => o,
            None => return Expr::mk_bvar(0),
        };
        let tag = self.obj_tag(off);
        let result = match tag {
            0 => {
                // Expr.bvar: 1 obj [Nat], scalar: data_u64
                let nat_ptr = self.obj_field(off, 0);
                let idx = if Self::is_scalar(nat_ptr) { Self::unbox(nat_ptr) } else { 0 };
                Expr::mk_bvar(idx)
            }
            1 => {
                // Expr.fvar: 1 obj [FVarId], scalar: data_u64
                let fvarid_ptr = self.obj_field(off, 0);
                let fvarid_off = self.fix_ptr(fvarid_ptr).expect("fvar id");
                let name = self.read_name(self.obj_field(fvarid_off, 0));
                Expr::mk_fvar(&name)
            }
            2 => {
                // Expr.mvar: 1 obj [MVarId]
                let mvarid_ptr = self.obj_field(off, 0);
                let mvarid_off = self.fix_ptr(mvarid_ptr).expect("mvar id");
                let name = self.read_name(self.obj_field(mvarid_off, 0));
                Expr::mk_mvar(&name)
            }
            3 => {
                // Expr.sort: 1 obj [Level]
                let level = self.read_level(self.obj_field(off, 0));
                Expr::mk_sort(&level)
            }
            4 => {
                // Expr.const: 2 objs [Name, List Level]
                let name = self.read_name(self.obj_field(off, 0));
                let levels = self.read_levels(self.obj_field(off, 1));
                Expr::mk_const(&name, &levels)
            }
            5 => {
                // Expr.app: 2 objs [fn, arg]
                let f = self.read_expr(self.obj_field(off, 0));
                let a = self.read_expr(self.obj_field(off, 1));
                Expr::mk_app(&f, &a)
            }
            6 => {
                // Expr.lam: 3 objs [name, type, body], scalar: data_u64 + binder_info_u8
                let name = self.read_name(self.obj_field(off, 0));
                let ty = self.read_expr(self.obj_field(off, 1));
                let body = self.read_expr(self.obj_field(off, 2));
                let bi = self.read_binder_info(off);
                Expr::mk_lambda(&name, bi, &ty, &body)
            }
            7 => {
                // Expr.forallE: 3 objs [name, type, body], scalar: data_u64 + binder_info_u8
                let name = self.read_name(self.obj_field(off, 0));
                let ty = self.read_expr(self.obj_field(off, 1));
                let body = self.read_expr(self.obj_field(off, 2));
                let bi = self.read_binder_info(off);
                Expr::mk_pi(&name, bi, &ty, &body)
            }
            8 => {
                // Expr.letE: 4 objs [name, type, value, body], scalar: data_u64 + nondep_u8
                let name = self.read_name(self.obj_field(off, 0));
                let ty = self.read_expr(self.obj_field(off, 1));
                let val = self.read_expr(self.obj_field(off, 2));
                let body = self.read_expr(self.obj_field(off, 3));
                let nondep = self.obj_scalar_u8(off, 8) != 0;
                Expr::mk_let(&name, &ty, &val, &body, nondep)
            }
            9 => {
                // Expr.lit: 1 obj [Literal]
                let lit = self.read_literal(self.obj_field(off, 0));
                Expr::mk_lit(lit)
            }
            10 => {
                // Expr.mdata: 2 objs [MData/KVMap, Expr]
                let inner = self.read_expr(self.obj_field(off, 1));
                Expr::mk_mdata(&inner)
            }
            11 => {
                // Expr.proj: 3 objs [Name, Nat, Expr]
                let sname = self.read_name(self.obj_field(off, 0));
                let idx_ptr = self.obj_field(off, 1);
                let idx = if Self::is_scalar(idx_ptr) { Self::unbox(idx_ptr) } else { 0 };
                let e = self.read_expr(self.obj_field(off, 2));
                Expr::mk_proj(&sname, idx, &e)
            }
            _ => Expr::mk_bvar(0),
        };
        self.expr_cache.borrow_mut().insert(ptr, result.clone());
        result
    }

    fn read_binder_info(&self, obj_off: usize) -> BinderInfo {
        // BinderInfo is stored as u8 after the data_u64 scalar
        let bi_byte = self.obj_scalar_u8(obj_off, 8);
        match bi_byte {
            0 => BinderInfo::Default,
            1 => BinderInfo::Implicit,
            2 => BinderInfo::StrictImplicit,
            3 => BinderInfo::InstImplicit,
            _ => BinderInfo::Default,
        }
    }

    fn read_literal(&self, ptr: u64) -> Literal {
        if Self::is_scalar(ptr) {
            return Literal::Nat(0);
        }
        let off = self.fix_ptr(ptr).expect("literal pointer");
        let tag = self.obj_tag(off);
        match tag {
            0 => {
                // Literal.natVal: 1 obj [Nat]
                let nat_ptr = self.obj_field(off, 0);
                let n = if Self::is_scalar(nat_ptr) { Self::unbox(nat_ptr) } else { 0 };
                Literal::Nat(n)
            }
            1 => {
                // Literal.strVal: 1 obj [String]
                let s_ptr = self.obj_field(off, 0);
                let s_off = self.fix_ptr(s_ptr).expect("literal string");
                let s = self.read_string(s_off);
                Literal::Str(s)
            }
            _ => Literal::Nat(0),
        }
    }

    // -- Names list (List Name) -------------------------------------------

    fn read_names_list(&self, ptr: u64) -> Vec<Name> {
        let mut names = Vec::new();
        let mut cur = ptr;
        loop {
            if Self::is_scalar(cur) { break; }
            let off = match self.fix_ptr(cur) { Some(o) => o, None => break };
            if self.obj_tag(off) != 1 { break; } // not List.cons
            names.push(self.read_name(self.obj_field(off, 0)));
            cur = self.obj_field(off, 1);
        }
        names
    }

    // -- ConstantInfo parsing -----------------------------------------------

    fn read_constant_val(&self, off: usize) -> (Name, Vec<Name>, Expr) {
        // ConstantVal: 3 objs [name, levelParams (List Name), type]
        let name = self.read_name(self.obj_field(off, 0));
        let lparams = self.read_names_list(self.obj_field(off, 1));
        let type_ = self.read_expr(self.obj_field(off, 2));
        (name, lparams, type_)
    }

    fn read_constant_info(&self, ptr: u64) -> Option<ConstantInfo> {
        let off = self.fix_ptr(ptr)?;
        let tag = self.obj_tag(off);
        match tag {
            0 => {
                // AxiomInfo: 1 obj [AxiomVal]
                let av_off = self.fix_ptr(self.obj_field(off, 0))?;
                let cv_off = self.fix_ptr(self.obj_field(av_off, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv_off);
                let is_unsafe = self.obj_scalar_u8(av_off, 0) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Axiom { is_unsafe } })
            }
            1 => {
                // DefnInfo: 1 obj [DefinitionVal]
                let dv_off = self.fix_ptr(self.obj_field(off, 0))?;
                let cv_off = self.fix_ptr(self.obj_field(dv_off, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv_off);
                let value = self.read_expr(self.obj_field(dv_off, 1));
                let hints = self.read_reducibility_hints(self.obj_field(dv_off, 2));
                let safety_byte = self.obj_scalar_u8(dv_off, 0);
                let safety = match safety_byte {
                    0 => DefinitionSafety::Unsafe,
                    1 => DefinitionSafety::Safe,
                    2 => DefinitionSafety::Partial,
                    _ => DefinitionSafety::Safe,
                };
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Definition { value, hints, safety } })
            }
            2 => {
                // ThmInfo: 1 obj [TheoremVal]
                let tv_off = self.fix_ptr(self.obj_field(off, 0))?;
                let cv_off = self.fix_ptr(self.obj_field(tv_off, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv_off);
                let value = self.read_expr(self.obj_field(tv_off, 1));
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Theorem { value } })
            }
            3 => {
                // OpaqueInfo: 1 obj [OpaqueVal]
                let ov_off = self.fix_ptr(self.obj_field(off, 0))?;
                let cv_off = self.fix_ptr(self.obj_field(ov_off, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv_off);
                let value = self.read_expr(self.obj_field(ov_off, 1));
                let is_unsafe = self.obj_scalar_u8(ov_off, 0) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Opaque { value, is_unsafe } })
            }
            4 => {
                // QuotInfo: 1 obj [QuotVal]
                let qv_off = self.fix_ptr(self.obj_field(off, 0))?;
                let cv_off = self.fix_ptr(self.obj_field(qv_off, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv_off);
                let kind_byte = self.obj_scalar_u8(qv_off, 0);
                let kind = match kind_byte {
                    0 => QuotKind::Type, 1 => QuotKind::Mk,
                    2 => QuotKind::Lift, 3 => QuotKind::Ind,
                    _ => QuotKind::Type,
                };
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Quot { kind } })
            }
            5 => {
                // InductInfo: 1 obj [InductiveVal]
                let iv_off = self.fix_ptr(self.obj_field(off, 0))?;
                let cv_off = self.fix_ptr(self.obj_field(iv_off, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv_off);
                // InductiveVal fields: cval, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive
                let nparams_ptr = self.obj_field(iv_off, 1);
                let nparams = if Self::is_scalar(nparams_ptr) { Self::unbox(nparams_ptr) as u32 } else { 0 };
                let nindices_ptr = self.obj_field(iv_off, 2);
                let nindices = if Self::is_scalar(nindices_ptr) { Self::unbox(nindices_ptr) as u32 } else { 0 };
                let all = self.read_names_list(self.obj_field(iv_off, 3));
                let ctors = self.read_names_list(self.obj_field(iv_off, 4));
                let nnested_ptr = self.obj_field(iv_off, 5);
                let nnested = if Self::is_scalar(nnested_ptr) { Self::unbox(nnested_ptr) as u32 } else { 0 };
                let is_rec = self.obj_scalar_u8(iv_off, 0) != 0;
                let is_unsafe = self.obj_scalar_u8(iv_off, 1) != 0;
                let is_reflexive = self.obj_scalar_u8(iv_off, 2) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Inductive {
                    nparams, nindices, all, ctors, nnested, is_rec, is_unsafe, is_reflexive,
                }})
            }
            6 => {
                // CtorInfo: 1 obj [ConstructorVal]
                let ctv_off = self.fix_ptr(self.obj_field(off, 0))?;
                let cv_off = self.fix_ptr(self.obj_field(ctv_off, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv_off);
                let induct_name = self.read_name(self.obj_field(ctv_off, 1));
                let cidx_ptr = self.obj_field(ctv_off, 2);
                let cidx = if Self::is_scalar(cidx_ptr) { Self::unbox(cidx_ptr) as u32 } else { 0 };
                let nparams_ptr = self.obj_field(ctv_off, 3);
                let nparams = if Self::is_scalar(nparams_ptr) { Self::unbox(nparams_ptr) as u32 } else { 0 };
                let nfields_ptr = self.obj_field(ctv_off, 4);
                let nfields = if Self::is_scalar(nfields_ptr) { Self::unbox(nfields_ptr) as u32 } else { 0 };
                let is_unsafe = self.obj_scalar_u8(ctv_off, 0) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Constructor {
                    induct_name, cidx, nparams, nfields, is_unsafe,
                }})
            }
            7 => {
                // RecInfo: 1 obj [RecursorVal]
                let rv_off = self.fix_ptr(self.obj_field(off, 0))?;
                let cv_off = self.fix_ptr(self.obj_field(rv_off, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv_off);
                let all = self.read_names_list(self.obj_field(rv_off, 1));
                let nparams_ptr = self.obj_field(rv_off, 2);
                let nparams = if Self::is_scalar(nparams_ptr) { Self::unbox(nparams_ptr) as u32 } else { 0 };
                let nindices_ptr = self.obj_field(rv_off, 3);
                let nindices = if Self::is_scalar(nindices_ptr) { Self::unbox(nindices_ptr) as u32 } else { 0 };
                let nmotives_ptr = self.obj_field(rv_off, 4);
                let nmotives = if Self::is_scalar(nmotives_ptr) { Self::unbox(nmotives_ptr) as u32 } else { 0 };
                let nminors_ptr = self.obj_field(rv_off, 5);
                let nminors = if Self::is_scalar(nminors_ptr) { Self::unbox(nminors_ptr) as u32 } else { 0 };
                let rules = self.read_recursor_rules(self.obj_field(rv_off, 6));
                let k = self.obj_scalar_u8(rv_off, 0) != 0;
                let is_unsafe = self.obj_scalar_u8(rv_off, 1) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Recursor {
                    all, nparams, nindices, nmotives, nminors, rules, k, is_unsafe,
                }})
            }
            _ => None,
        }
    }

    fn read_reducibility_hints(&self, ptr: u64) -> ReducibilityHints {
        if Self::is_scalar(ptr) {
            let v = Self::unbox(ptr);
            return match v {
                0 => ReducibilityHints::Opaque,
                1 => ReducibilityHints::Abbreviation,
                _ => ReducibilityHints::Opaque,
            };
        }
        let off = match self.fix_ptr(ptr) { Some(o) => o, None => return ReducibilityHints::Opaque };
        let tag = self.obj_tag(off);
        if tag == 2 {
            // Regular: 1 obj [UInt32 as scalar in Nat box]
            let height_ptr = self.obj_field(off, 0);
            let height = if Self::is_scalar(height_ptr) { Self::unbox(height_ptr) as u32 } else { 0 };
            ReducibilityHints::Regular(height)
        } else {
            ReducibilityHints::Opaque
        }
    }

    fn read_recursor_rules(&self, ptr: u64) -> Vec<RecursorRule> {
        let mut rules = Vec::new();
        let mut cur = ptr;
        loop {
            if Self::is_scalar(cur) { break; }
            let off = match self.fix_ptr(cur) { Some(o) => o, None => break };
            if self.obj_tag(off) != 1 { break; }
            let rule_ptr = self.obj_field(off, 0);
            if let Some(rule_off) = self.fix_ptr(rule_ptr) {
                let ctor_name = self.read_name(self.obj_field(rule_off, 0));
                let nfields_ptr = self.obj_field(rule_off, 1);
                let nfields = if Self::is_scalar(nfields_ptr) { Self::unbox(nfields_ptr) as u32 } else { 0 };
                let rhs = self.read_expr(self.obj_field(rule_off, 2));
                rules.push(RecursorRule { ctor_name, nfields, rhs });
            }
            cur = self.obj_field(off, 1);
        }
        rules
    }

    // -- Import parsing ------------------------------------------------------

    fn read_import(&self, ptr: u64) -> Option<Import> {
        let off = self.fix_ptr(ptr)?;
        // Import: objs [module: Name], scalars [isExported: Bool, ...]
        let module = self.read_name(self.obj_field(off, 0));
        let is_exported = self.obj_scalar_u8(off, 0) != 0;
        Some(Import { module, is_exported })
    }

    // -- Top-level parse -----------------------------------------------------

    pub fn parse_module_data(&self) -> Result<ModuleData, String> {
        // Root pointer at file offset 88
        let root_ptr = self.read_u64(HEADER_SIZE);
        let root_off = self.fix_ptr(root_ptr)
            .ok_or("root pointer out of bounds")?;

        // ModuleData: tag 0, 5 obj fields [imports, constNames, constants, extraConstNames, entries]
        // scalar: isModule (u8)
        let is_module = self.obj_scalar_u8(root_off, 0) != 0;

        // Field 0: imports (Array Import)
        let imports_arr_off = self.fix_ptr(self.obj_field(root_off, 0))
            .ok_or("imports array pointer")?;
        let import_ptrs = self.read_array_ptrs(imports_arr_off);
        let imports: Vec<Import> = import_ptrs.iter()
            .filter_map(|&p| self.read_import(p))
            .collect();

        // Field 1: constNames (Array Name)
        let names_arr_off = self.fix_ptr(self.obj_field(root_off, 1))
            .ok_or("constNames array pointer")?;
        let name_ptrs = self.read_array_ptrs(names_arr_off);
        let const_names: Vec<Name> = name_ptrs.iter()
            .map(|&p| self.read_name(p))
            .collect();

        // Field 2: constants (Array ConstantInfo)
        let consts_arr_off = self.fix_ptr(self.obj_field(root_off, 2))
            .ok_or("constants array pointer")?;
        let const_ptrs = self.read_array_ptrs(consts_arr_off);
        let constants: Vec<ConstantInfo> = const_ptrs.iter()
            .filter_map(|&p| self.read_constant_info(p))
            .collect();

        // Field 3: extraConstNames (Array Name)
        let extra_arr_off = self.fix_ptr(self.obj_field(root_off, 3))
            .ok_or("extraConstNames array pointer")?;
        let extra_ptrs = self.read_array_ptrs(extra_arr_off);
        let extra_const_names: Vec<Name> = extra_ptrs.iter()
            .map(|&p| self.read_name(p))
            .collect();

        // Field 4: entries — skip for now (env extensions)

        Ok(ModuleData {
            is_module,
            imports,
            const_names,
            constants,
            extra_const_names,
        })
    }
}

// ============================================================================
// Multi-module loader
// ============================================================================

/// Resolve a module name to its .olean file path.
/// `Init.Data.Nat.Basic` → `<search_path>/Init/Data/Nat/Basic.olean`
pub fn resolve_module(module: &Name, search_paths: &[PathBuf]) -> Option<PathBuf> {
    let rel = module.to_string_with_sep("/") + ".olean";
    for sp in search_paths {
        let full = sp.join(&rel);
        if full.exists() {
            return Some(full);
        }
    }
    None
}

/// Result of loading an entire module tree.
pub struct LoadedEnvironment {
    pub env: Environment,
    pub modules_loaded: Vec<Name>,
    pub total_constants: usize,
}

/// Load a module and all its transitive dependencies.
pub fn load_module_tree(
    root_module: &Name,
    search_paths: &[PathBuf],
) -> Result<LoadedEnvironment, String> {
    let mut loaded: StdHashMap<String, Arc<ModuleData>> = StdHashMap::new();
    let mut load_order: Vec<Name> = Vec::new();
    let mut visited: HashSet<String> = HashSet::new();

    load_recursive(root_module, search_paths, &mut loaded, &mut load_order, &mut visited)?;

    // Build environment in load order — use bulk insert for speed
    let mut all_constants: StdHashMap<Name, Arc<ConstantInfo>> = StdHashMap::new();
    let mut total = 0usize;
    for mod_name in &load_order {
        let key = mod_name.to_string();
        let md = loaded.get(&key).unwrap();
        for ci in &md.constants {
            all_constants.entry(ci.name.clone()).or_insert_with(|| Arc::new(ci.clone()));
        }
        total += md.constants.len();
    }
    let env = Environment::from_constants(all_constants, 0);

    Ok(LoadedEnvironment {
        env,
        modules_loaded: load_order,
        total_constants: total,
    })
}

fn load_recursive(
    module: &Name,
    search_paths: &[PathBuf],
    loaded: &mut StdHashMap<String, Arc<ModuleData>>,
    load_order: &mut Vec<Name>,
    visited: &mut HashSet<String>,
) -> Result<(), String> {
    let key = module.to_string();
    if visited.contains(&key) { return Ok(()); }
    visited.insert(key.clone());

    let path = resolve_module(module, search_paths)
        .ok_or_else(|| format!("module not found: {}", module))?;
    let olean = OleanFile::read(&path)?;
    let md = olean.parse_module_data()
        .map_err(|e| format!("parsing {}: {}", module, e))?;
    eprintln!("  loaded {} ({} constants, {} imports)", module, md.constants.len(), md.imports.len());

    // Load dependencies first
    for imp in &md.imports {
        load_recursive(&imp.module, search_paths, loaded, load_order, visited)?;
    }

    load_order.push(module.clone());
    loaded.insert(key, Arc::new(md));
    Ok(())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    const PRELUDE_PATH: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean/Init/Prelude.olean";

    #[test]
    fn test_read_header() {
        let olean = OleanFile::read(Path::new(PRELUDE_PATH)).unwrap();
        let hdr = olean.header();
        assert_eq!(hdr.version, 2);
        assert!(hdr.lean_version.starts_with("4.25"));
        eprintln!("olean header: version={} lean={} base_addr=0x{:x}",
            hdr.version, hdr.lean_version, hdr.base_addr);
    }

    #[test]
    fn test_parse_prelude() {
        let olean = OleanFile::read(Path::new(PRELUDE_PATH)).unwrap();
        let md = olean.parse_module_data().unwrap();
        eprintln!("Prelude: is_module={} imports={} const_names={} constants={} extra={}",
            md.is_module, md.imports.len(), md.const_names.len(),
            md.constants.len(), md.extra_const_names.len());
        assert!(md.is_module);
        assert_eq!(md.imports.len(), 0); // Prelude has no imports
        assert!(md.const_names.len() > 1000, "expected >1000 constants, got {}", md.const_names.len());
        assert_eq!(md.const_names.len(), md.constants.len());
    }

    #[test]
    fn test_prelude_has_nat() {
        let olean = OleanFile::read(Path::new(PRELUDE_PATH)).unwrap();
        let md = olean.parse_module_data().unwrap();
        let nat_found = md.constants.iter().any(|c| c.name == Name::str("Nat"));
        assert!(nat_found, "Nat not found in Prelude constants");
    }

    #[test]
    fn test_prelude_name_hashes() {
        let olean = OleanFile::read(Path::new(PRELUDE_PATH)).unwrap();
        let md = olean.parse_module_data().unwrap();
        // Verify some known name hashes
        let known: &[(&str, u64)] = &[
            ("Nat", 11442535297760353691),
            ("Bool", 12882480457794858234),
            ("True", 11870096045526947150),
        ];
        for &(name_str, expected_hash) in known {
            let found = md.constants.iter().find(|c| c.name == Name::str(name_str));
            assert!(found.is_some(), "{} not found", name_str);
            assert_eq!(found.unwrap().name.hash(), expected_hash,
                "Name hash mismatch for {}", name_str);
        }
    }

    #[test]
    fn test_prelude_type_hashes() {
        let olean = OleanFile::read(Path::new(PRELUDE_PATH)).unwrap();
        let md = olean.parse_module_data().unwrap();
        // Verify type expression hashes for known constants
        // Nat : Type = Sort 1 → hash 3931117990
        let nat = md.constants.iter().find(|c| c.name == Name::str("Nat")).unwrap();
        assert_eq!(nat.type_.hash(), 3931117990, "Nat type hash");
        // True : Prop = Sort 0 → hash 3944470172
        let true_ = md.constants.iter().find(|c| c.name == Name::str("True")).unwrap();
        assert_eq!(true_.type_.hash(), 3944470172, "True type hash");
        // Nat.zero : Nat → hash 421340980
        let zero = md.constants.iter().find(|c| c.name == Name::str("Nat.zero")).unwrap();
        assert_eq!(zero.type_.hash(), 421340980, "Nat.zero type hash");
    }

    #[test]
    fn test_prelude_constant_kinds() {
        let olean = OleanFile::read(Path::new(PRELUDE_PATH)).unwrap();
        let md = olean.parse_module_data().unwrap();
        let nat = md.constants.iter().find(|c| c.name == Name::str("Nat")).unwrap();
        assert!(nat.is_inductive(), "Nat should be inductive");
        let zero = md.constants.iter().find(|c| c.name == Name::str("Nat.zero")).unwrap();
        assert!(zero.is_constructor(), "Nat.zero should be constructor");
        let succ = md.constants.iter().find(|c| c.name == Name::str("Nat.succ")).unwrap();
        assert!(succ.is_constructor(), "Nat.succ should be constructor");
    }

    #[test]
    fn test_prelude_all_name_hashes_match() {
        let olean = OleanFile::read(Path::new(PRELUDE_PATH)).unwrap();
        let md = olean.parse_module_data().unwrap();
        // Compare every parsed name with the name hash from the Lean dump
        let hash_file = "/r/tmp/lean4/all_hashes.txt";
        let content = match std::fs::read_to_string(hash_file) {
            Ok(c) => c,
            Err(_) => { eprintln!("SKIP: {} not found", hash_file); return; }
        };
        // Build lookup: name_str → expected_hash
        let mut expected: std::collections::HashMap<String, u64> = std::collections::HashMap::new();
        for line in content.lines() {
            if line.starts_with("TOTAL") || line.contains("warning") || line.contains("Note:") || line.is_empty() { continue; }
            let parts: Vec<&str> = line.rsplitn(3, ' ').collect();
            if parts.len() < 3 { continue; }
            let name_str = parts[2];
            if let Ok(h) = parts[1].parse::<u64>() {
                expected.insert(name_str.to_string(), h);
            }
        }
        let mut matched = 0u64;
        let mut mismatched = 0u64;
        for ci in &md.constants {
            let name_str = ci.name.to_string();
            if let Some(&exp) = expected.get(&name_str) {
                if ci.name.hash() == exp {
                    matched += 1;
                } else {
                    mismatched += 1;
                    if mismatched <= 5 {
                        eprintln!("NAME MISMATCH: {} got {} expected {}", name_str, ci.name.hash(), exp);
                    }
                }
            }
        }
        eprintln!("Prelude name hash check: matched={} mismatched={} (of {} parsed)",
            matched, mismatched, md.constants.len());
        assert_eq!(mismatched, 0, "{} name hashes mismatched", mismatched);
    }

    // -- Multi-module tests -------------------------------------------------

    const LEAN_LIB: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean";

    #[test]
    fn test_resolve_module() {
        let sp = vec![PathBuf::from(LEAN_LIB)];
        let path = resolve_module(&Name::str("Init.Prelude"), &sp);
        assert!(path.is_some(), "Init.Prelude not found");
        assert!(path.unwrap().exists());
    }

    #[test]
    fn test_load_init_prelude_tree() {
        let sp = vec![PathBuf::from(LEAN_LIB)];
        let loaded = load_module_tree(&Name::str("Init.Prelude"), &sp).unwrap();
        eprintln!("Init.Prelude tree: {} modules, {} constants, env={}",
            loaded.modules_loaded.len(), loaded.total_constants, loaded.env.num_constants());
        assert_eq!(loaded.modules_loaded.len(), 1);
        assert_eq!(loaded.env.num_constants(), loaded.total_constants);
    }

    #[test]
    fn test_load_full_init() {
        let sp = vec![PathBuf::from(LEAN_LIB)];
        let loaded = load_module_tree(&Name::str("Init"), &sp).unwrap();
        eprintln!("Full Init: {} modules, {} constants, env={}",
            loaded.modules_loaded.len(), loaded.total_constants, loaded.env.num_constants());
        // Init should have many modules and ~53K constants
        assert!(loaded.modules_loaded.len() > 40, "expected >40 modules, got {}", loaded.modules_loaded.len());
        assert!(loaded.env.num_constants() > 40000, "expected >40K constants, got {}", loaded.env.num_constants());
        // Verify key constants are present
        assert!(loaded.env.find(&Name::str("Nat")).is_some(), "Nat missing");
        assert!(loaded.env.find(&Name::str("Nat.add")).is_some(), "Nat.add missing");
        assert!(loaded.env.find(&Name::str("List")).is_some(), "List missing");
        assert!(loaded.env.find(&Name::str("String")).is_some(), "String missing");
        assert!(loaded.env.find(&Name::str("IO")).is_some(), "IO missing");
    }
}
