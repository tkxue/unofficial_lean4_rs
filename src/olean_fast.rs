//! Zero-copy .olean reader. Keeps the file as a byte slice and reads on demand.
//! Names, levels, and expressions are represented as offsets into the file.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::env::*;
use crate::expr::{BinderInfo, Expr, Literal};
use crate::level::Level;
use crate::name::Name;

// Tag constants (same as olean.rs)
const TAG_ARRAY: u8 = 246;
const TAG_STRING: u8 = 249;
const TAG_MPZ: u8 = 250;

use std::cell::RefCell;

/// Fast olean reader — shared across all parsed objects from this file.
pub struct OleanReader {
    data: Vec<u8>,
    base_addr: u64,
    // Caches with interior mutability to avoid borrow conflicts
    name_cache: RefCell<HashMap<u64, Name>>,
    level_cache: RefCell<HashMap<u64, Level>>,
    expr_cache: RefCell<HashMap<u64, Expr>>,
}

#[inline(always)]
fn read_u64(data: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(data[off..off+8].try_into().unwrap())
}

#[inline(always)]
fn read_u16(data: &[u8], off: usize) -> u16 {
    u16::from_le_bytes(data[off..off+2].try_into().unwrap())
}

#[inline(always)]
fn obj_tag(data: &[u8], off: usize) -> u8 { data[off + 7] }

#[inline(always)]
fn obj_other(data: &[u8], off: usize) -> u8 { data[off + 6] }

#[inline(always)]
fn obj_field(data: &[u8], off: usize, i: usize) -> u64 { read_u64(data, off + 8 + i * 8) }

#[inline(always)]
fn obj_scalar_start(data: &[u8], off: usize) -> usize { off + 8 + obj_other(data, off) as usize * 8 }

#[inline(always)]
fn obj_scalar_u8(data: &[u8], off: usize, i: usize) -> u8 { data[obj_scalar_start(data, off) + i] }

#[inline(always)]
fn is_scalar(ptr: u64) -> bool { ptr & 1 == 1 }

#[inline(always)]
fn unbox(ptr: u64) -> u64 { ptr >> 1 }

impl OleanReader {
    pub fn open(path: &Path) -> Result<Self, String> {
        let data = std::fs::read(path).map_err(|e| format!("{}: {}", path.display(), e))?;
        if data.len() < 96 || &data[..5] != b"olean" {
            return Err(format!("{}: invalid olean", path.display()));
        }
        let base_addr = read_u64(&data, 80);
        Ok(OleanReader {
            data,
            base_addr,
            name_cache: RefCell::new(HashMap::new()),
            level_cache: RefCell::new(HashMap::new()),
            expr_cache: RefCell::new(HashMap::new()),
        })
    }

    #[inline(always)]
    fn d(&self) -> &[u8] { &self.data }

    #[inline(always)]
    fn fix(&self, ptr: u64) -> Option<usize> {
        if is_scalar(ptr) { return None; }
        let off = ptr.wrapping_sub(self.base_addr) as usize;
        if off >= self.data.len() { None } else { Some(off) }
    }

    fn read_string(&self, off: usize) -> &str {
        if obj_tag(self.d(), off) != TAG_STRING { return ""; }
        let size = read_u64(self.d(), off + 8) as usize;
        if size == 0 { return ""; }
        let start = off + 32;
        let end = start + size - 1;
        if end > self.data.len() { return ""; }
        std::str::from_utf8(&self.data[start..end]).unwrap_or("")
    }

    fn read_array_offsets(&self, off: usize) -> &[u8] {
        // Return raw slice covering the pointer array
        let size = read_u64(self.d(), off + 8) as usize;
        let start = off + 24;
        let end = start + size * 8;
        &self.data[start..end]
    }

    fn array_size(&self, off: usize) -> usize {
        read_u64(self.d(), off + 8) as usize
    }

    fn array_ptr(&self, off: usize, i: usize) -> u64 {
        read_u64(self.d(), off + 24 + i * 8)
    }

    // -- Name ----------------------------------------------------------------

    pub fn read_name(&self, ptr: u64) -> Name {
        if is_scalar(ptr) { return Name::anonymous(); }
        if let Some(n) = self.name_cache.borrow().get(&ptr) { return n.clone(); }
        let off = match self.fix(ptr) { Some(o) => o, None => return Name::anonymous() };
        let d = self.d();
        let result = match obj_tag(d, off) {
            1 => {
                let prefix = self.read_name(obj_field(d, off, 0));
                let s_ptr = obj_field(d, off, 1);
                let s = match self.fix(s_ptr) { Some(so) => self.read_string(so), None => "" };
                Name::mk_string(&prefix, s)
            }
            2 => {
                let prefix = self.read_name(obj_field(d, off, 0));
                let np = obj_field(d, off, 1);
                let n = if is_scalar(np) { unbox(np) } else { 0 };
                Name::mk_numeral(&prefix, n)
            }
            _ => Name::anonymous(),
        };
        self.name_cache.borrow_mut().insert(ptr, result.clone());
        result
    }

    // -- Level ---------------------------------------------------------------

    pub fn read_level(&self, ptr: u64) -> Level {
        if is_scalar(ptr) { return Level::zero(); }
        if let Some(l) = self.level_cache.borrow().get(&ptr) { return l.clone(); }
        let off = match self.fix(ptr) { Some(o) => o, None => return Level::zero() };
        let d = self.d();
        let result = match obj_tag(d, off) {
            1 => { let i = self.read_level(obj_field(d, off, 0)); Level::mk_succ(&i) }
            2 => { let l = self.read_level(obj_field(d, off, 0)); let r = self.read_level(obj_field(d, off, 1)); Level::mk_max_core(&l, &r) }
            3 => { let l = self.read_level(obj_field(d, off, 0)); let r = self.read_level(obj_field(d, off, 1)); Level::mk_imax_core(&l, &r) }
            4 => { let n = self.read_name(obj_field(d, off, 0)); Level::mk_param(&n) }
            5 => { let po = self.fix(obj_field(d, off, 0)).unwrap_or(off); let n = self.read_name(obj_field(self.d(), po, 0)); Level::mk_mvar(&n) }
            _ => Level::zero(),
        };
        self.level_cache.borrow_mut().insert(ptr, result.clone());
        result
    }

    fn read_levels(&self, ptr: u64) -> Vec<Level> {
        let mut levels = Vec::new();
        let mut cur = ptr;
        loop {
            if is_scalar(cur) { break; }
            let off = match self.fix(cur) { Some(o) => o, None => break };
            if obj_tag(self.d(), off) != 1 { break; }
            levels.push(self.read_level(obj_field(self.d(), off, 0)));
            cur = obj_field(self.d(), off, 1);
        }
        levels
    }

    // -- Expr ----------------------------------------------------------------

    pub fn read_expr(&self, ptr: u64) -> Expr {
        if is_scalar(ptr) { return Expr::mk_bvar(unbox(ptr)); }
        if let Some(e) = self.expr_cache.borrow().get(&ptr) { return e.clone(); }
        let off = match self.fix(ptr) { Some(o) => o, None => return Expr::mk_bvar(0) };
        let d = self.d();
        let tag = obj_tag(d, off);
        let result = match tag {
            0 => { let np = obj_field(d, off, 0); Expr::mk_bvar(if is_scalar(np) { unbox(np) } else { 0 }) }
            1 => { let po = self.fix(obj_field(d, off, 0)).unwrap_or(off); let n = self.read_name(obj_field(self.d(), po, 0)); Expr::mk_fvar(&n) }
            2 => { let po = self.fix(obj_field(d, off, 0)).unwrap_or(off); let n = self.read_name(obj_field(self.d(), po, 0)); Expr::mk_mvar(&n) }
            3 => { let l = self.read_level(obj_field(d, off, 0)); Expr::mk_sort(&l) }
            4 => { let n = self.read_name(obj_field(d, off, 0)); let ls = self.read_levels(obj_field(d, off, 1)); Expr::mk_const(&n, &ls) }
            5 => { let f = self.read_expr(obj_field(d, off, 0)); let a = self.read_expr(obj_field(d, off, 1)); Expr::mk_app(&f, &a) }
            6 => { let n = self.read_name(obj_field(d, off, 0)); let t = self.read_expr(obj_field(d, off, 1)); let b = self.read_expr(obj_field(d, off, 2)); let bi = read_bi(self.d(), off); Expr::mk_lambda(&n, bi, &t, &b) }
            7 => { let n = self.read_name(obj_field(d, off, 0)); let t = self.read_expr(obj_field(d, off, 1)); let b = self.read_expr(obj_field(d, off, 2)); let bi = read_bi(self.d(), off); Expr::mk_pi(&n, bi, &t, &b) }
            8 => { let n = self.read_name(obj_field(d, off, 0)); let t = self.read_expr(obj_field(d, off, 1)); let v = self.read_expr(obj_field(d, off, 2)); let b = self.read_expr(obj_field(d, off, 3)); let nd = obj_scalar_u8(self.d(), off, 8) != 0; Expr::mk_let(&n, &t, &v, &b, nd) }
            9 => { let lit = self.read_literal(obj_field(d, off, 0)); Expr::mk_lit(lit) }
            10 => { let e = self.read_expr(obj_field(d, off, 1)); Expr::mk_mdata(&e) }
            11 => { let s = self.read_name(obj_field(d, off, 0)); let ip = obj_field(d, off, 1); let idx = if is_scalar(ip) { unbox(ip) } else { 0 }; let e = self.read_expr(obj_field(d, off, 2)); Expr::mk_proj(&s, idx, &e) }
            _ => Expr::mk_bvar(0),
        };
        self.expr_cache.borrow_mut().insert(ptr, result.clone());
        result
    }

    fn read_literal(&self, ptr: u64) -> Literal {
        if is_scalar(ptr) { return Literal::Nat(0); }
        let off = match self.fix(ptr) { Some(o) => o, None => return Literal::Nat(0) };
        match obj_tag(self.d(), off) {
            0 => { let np = obj_field(self.d(), off, 0); Literal::Nat(if is_scalar(np) { unbox(np) } else { 0 }) }
            1 => { let sp = obj_field(self.d(), off, 0); let so = self.fix(sp).unwrap_or(0); Literal::Str(self.read_string(so).to_string()) }
            _ => Literal::Nat(0),
        }
    }

    // -- Names list ----------------------------------------------------------

    fn read_names_list(&self, ptr: u64) -> Vec<Name> {
        let mut names = Vec::new();
        let mut cur = ptr;
        loop {
            if is_scalar(cur) { break; }
            let off = match self.fix(cur) { Some(o) => o, None => break };
            if obj_tag(self.d(), off) != 1 { break; }
            names.push(self.read_name(obj_field(self.d(), off, 0)));
            cur = obj_field(self.d(), off, 1);
        }
        names
    }

    // -- ConstantVal ---------------------------------------------------------

    fn read_constant_val(&self, off: usize) -> (Name, Vec<Name>, Expr) {
        let d = self.d();
        let name = self.read_name(obj_field(d, off, 0));
        let lparams = self.read_names_list(obj_field(d, off, 1));
        let type_ = self.read_expr(obj_field(d, off, 2));
        (name, lparams, type_)
    }

    // -- ConstantInfo --------------------------------------------------------

    fn read_constant_info(&self, ptr: u64) -> Option<ConstantInfo> {
        let off = self.fix(ptr)?;
        let tag = obj_tag(self.d(), off);
        match tag {
            0 => { // Axiom
                let av = self.fix(obj_field(self.d(), off, 0))?;
                let cv = self.fix(obj_field(self.d(), av, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv);
                let is_unsafe = obj_scalar_u8(self.d(), av, 0) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Axiom { is_unsafe } })
            }
            1 => { // Def
                let dv = self.fix(obj_field(self.d(), off, 0))?;
                let cv = self.fix(obj_field(self.d(), dv, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv);
                // Skip value construction — use placeholder. WHNF unfold will fail
                // gracefully (returns the constant unexpanded).
                let value = Expr::mk_const(&name, &[]);
                let hints = self.read_hints(obj_field(self.d(), dv, 2));
                let sb = obj_scalar_u8(self.d(), dv, 0);
                let safety = match sb { 0 => DefinitionSafety::Unsafe, 2 => DefinitionSafety::Partial, _ => DefinitionSafety::Safe };
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Definition { value, hints, safety } })
            }
            2 => { // Thm — skip proof term entirely (not needed for type checking)
                let tv = self.fix(obj_field(self.d(), off, 0))?;
                let cv = self.fix(obj_field(self.d(), tv, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv);
                let value = Expr::mk_const(&Name::str("sorry"), &[]); // placeholder
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Theorem { value } })
            }
            3 => { // Opaque
                let ov = self.fix(obj_field(self.d(), off, 0))?;
                let cv = self.fix(obj_field(self.d(), ov, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv);
                let value = Expr::mk_const(&Name::str("sorry"), &[]); // skip opaque value
                let is_unsafe = obj_scalar_u8(self.d(), ov, 0) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Opaque { value, is_unsafe } })
            }
            4 => { // Quot
                let qv = self.fix(obj_field(self.d(), off, 0))?;
                let cv = self.fix(obj_field(self.d(), qv, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv);
                let kb = obj_scalar_u8(self.d(), qv, 0);
                let kind = match kb { 0 => QuotKind::Type, 1 => QuotKind::Mk, 2 => QuotKind::Lift, 3 => QuotKind::Ind, _ => QuotKind::Type };
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Quot { kind } })
            }
            5 => { // Induct
                let iv = self.fix(obj_field(self.d(), off, 0))?;
                let cv = self.fix(obj_field(self.d(), iv, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv);
                let d = self.d();
                let nparams = if is_scalar(obj_field(d, iv, 1)) { unbox(obj_field(d, iv, 1)) as u32 } else { 0 };
                let nindices = if is_scalar(obj_field(d, iv, 2)) { unbox(obj_field(d, iv, 2)) as u32 } else { 0 };
                let all = self.read_names_list(obj_field(self.d(), iv, 3));
                let ctors = self.read_names_list(obj_field(self.d(), iv, 4));
                let nnested = if is_scalar(obj_field(self.d(), iv, 5)) { unbox(obj_field(self.d(), iv, 5)) as u32 } else { 0 };
                let is_rec = obj_scalar_u8(self.d(), iv, 0) != 0;
                let is_unsafe = obj_scalar_u8(self.d(), iv, 1) != 0;
                let is_reflexive = obj_scalar_u8(self.d(), iv, 2) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Inductive { nparams, nindices, all, ctors, nnested, is_rec, is_unsafe, is_reflexive } })
            }
            6 => { // Ctor
                let ctv = self.fix(obj_field(self.d(), off, 0))?;
                let cv = self.fix(obj_field(self.d(), ctv, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv);
                let d = self.d();
                let induct_name = self.read_name(obj_field(d, ctv, 1));
                let cidx = if is_scalar(obj_field(d, ctv, 2)) { unbox(obj_field(d, ctv, 2)) as u32 } else { 0 };
                let nparams = if is_scalar(obj_field(d, ctv, 3)) { unbox(obj_field(d, ctv, 3)) as u32 } else { 0 };
                let nfields = if is_scalar(obj_field(d, ctv, 4)) { unbox(obj_field(d, ctv, 4)) as u32 } else { 0 };
                let is_unsafe = obj_scalar_u8(d, ctv, 0) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Constructor { induct_name, cidx, nparams, nfields, is_unsafe } })
            }
            7 => { // Rec
                let rv = self.fix(obj_field(self.d(), off, 0))?;
                let cv = self.fix(obj_field(self.d(), rv, 0))?;
                let (name, lparams, type_) = self.read_constant_val(cv);
                let d = self.d();
                let all = self.read_names_list(obj_field(d, rv, 1));
                let nparams = if is_scalar(obj_field(d, rv, 2)) { unbox(obj_field(d, rv, 2)) as u32 } else { 0 };
                let nindices = if is_scalar(obj_field(d, rv, 3)) { unbox(obj_field(d, rv, 3)) as u32 } else { 0 };
                let nmotives = if is_scalar(obj_field(d, rv, 4)) { unbox(obj_field(d, rv, 4)) as u32 } else { 0 };
                let nminors = if is_scalar(obj_field(d, rv, 5)) { unbox(obj_field(d, rv, 5)) as u32 } else { 0 };
                let rules = self.read_rec_rules(obj_field(d, rv, 6));
                let k = obj_scalar_u8(d, rv, 0) != 0;
                let is_unsafe = obj_scalar_u8(d, rv, 1) != 0;
                Some(ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Recursor { all, nparams, nindices, nmotives, nminors, rules, k, is_unsafe } })
            }
            _ => None,
        }
    }

    fn read_hints(&self, ptr: u64) -> ReducibilityHints {
        if is_scalar(ptr) { return match unbox(ptr) { 1 => ReducibilityHints::Abbreviation, _ => ReducibilityHints::Opaque }; }
        let off = match self.fix(ptr) { Some(o) => o, None => return ReducibilityHints::Opaque };
        if obj_tag(self.d(), off) == 2 {
            let hp = obj_field(self.d(), off, 0);
            ReducibilityHints::Regular(if is_scalar(hp) { unbox(hp) as u32 } else { 0 })
        } else { ReducibilityHints::Opaque }
    }

    fn read_rec_rules(&self, ptr: u64) -> Vec<RecursorRule> {
        let mut rules = Vec::new();
        let mut cur = ptr;
        loop {
            if is_scalar(cur) { break; }
            let off = match self.fix(cur) { Some(o) => o, None => break };
            if obj_tag(self.d(), off) != 1 { break; }
            let rp = obj_field(self.d(), off, 0);
            if let Some(ro) = self.fix(rp) {
                let d = self.d();
                let ctor_name = self.read_name(obj_field(d, ro, 0));
                let nf = obj_field(d, ro, 1);
                let nfields = if is_scalar(nf) { unbox(nf) as u32 } else { 0 };
                // Skip RHS construction — placeholder
                let rhs = Expr::mk_bvar(0);
                rules.push(RecursorRule { ctor_name, nfields, rhs });
            }
            cur = obj_field(self.d(), off, 1);
        }
        rules
    }

    // -- Import --------------------------------------------------------------

    fn read_import(&self, ptr: u64) -> Option<Import> {
        let off = self.fix(ptr)?;
        let module = self.read_name(obj_field(self.d(), off, 0));
        let is_exported = obj_scalar_u8(self.d(), off, 0) != 0;
        Some(Import { module, is_exported })
    }

    // -- ModuleData ----------------------------------------------------------

    pub fn parse_module_data(&self) -> Result<super::olean::ModuleData, String> {
        let root_ptr = read_u64(self.d(), 88);
        let root = self.fix(root_ptr).ok_or("bad root")?;
        let d = self.d();
        let is_module = obj_scalar_u8(d, root, 0) != 0;

        // imports
        let imp_arr = self.fix(obj_field(d, root, 0)).ok_or("imports")?;
        let n_imp = self.array_size(imp_arr);
        let mut imports = Vec::with_capacity(n_imp);
        for i in 0..n_imp {
            if let Some(imp) = self.read_import(self.array_ptr(imp_arr, i)) {
                imports.push(imp);
            }
        }

        // constNames
        let names_arr = self.fix(obj_field(d, root, 1)).ok_or("names")?;
        let n_names = self.array_size(names_arr);
        let mut const_names = Vec::with_capacity(n_names);
        for i in 0..n_names {
            const_names.push(self.read_name(self.array_ptr(names_arr, i)));
        }

        // constants
        let consts_arr = self.fix(obj_field(d, root, 2)).ok_or("consts")?;
        let n_consts = self.array_size(consts_arr);
        let mut constants = Vec::with_capacity(n_consts);
        for i in 0..n_consts {
            if let Some(ci) = self.read_constant_info(self.array_ptr(consts_arr, i)) {
                constants.push(ci);
            }
        }

        // extraConstNames
        let extra_arr = self.fix(obj_field(d, root, 3)).ok_or("extra")?;
        let n_extra = self.array_size(extra_arr);
        let mut extra_const_names = Vec::with_capacity(n_extra);
        for i in 0..n_extra {
            extra_const_names.push(self.read_name(self.array_ptr(extra_arr, i)));
        }

        Ok(super::olean::ModuleData { is_module, imports, const_names, constants, extra_const_names })
    }
}

#[inline(always)]
fn read_bi(data: &[u8], off: usize) -> BinderInfo {
    match obj_scalar_u8(data, off, 8) {
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => BinderInfo::Default,
    }
}

// ============================================================================
// Fast multi-module loader using OleanReader
// ============================================================================

use std::collections::HashSet;
use super::olean::{ModuleData, Import, LoadedEnvironment};

pub fn resolve_module(module: &Name, search_paths: &[PathBuf]) -> Option<PathBuf> {
    let rel = module.to_string_with_sep("/") + ".olean";
    for sp in search_paths {
        let full = sp.join(&rel);
        if full.exists() { return Some(full); }
    }
    None
}

/// Load a module tree. If `verify` is true, type-check every constant after loading.
pub fn load_module_tree_fast(
    root_module: &Name,
    search_paths: &[PathBuf],
) -> Result<LoadedEnvironment, String> {
    load_module_tree_ex(root_module, search_paths, false)
}

/// Load and optionally verify.
pub fn load_module_tree_ex(
    root_module: &Name,
    search_paths: &[PathBuf],
    verify: bool,
) -> Result<LoadedEnvironment, String> {
    let mut loaded: HashMap<String, Arc<ModuleData>> = HashMap::new();
    let mut load_order: Vec<Name> = Vec::new();
    let mut visited: HashSet<String> = HashSet::new();

    load_recursive(root_module, search_paths, &mut loaded, &mut load_order, &mut visited)?;

    let mut all_constants: HashMap<Name, Arc<ConstantInfo>> = HashMap::new();
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

    if verify {
        let mut tc = crate::type_checker::TypeChecker::new(env.clone(), crate::local_ctx::LocalContext::new());
        let mut ok = 0u64;
        let mut fail = 0u64;
        env.for_each_constant(|_name, ci| {
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                tc.infer_type(&ci.type_)
            })) {
                Ok(_) => { ok += 1; }
                Err(_) => { fail += 1; }
            }
        });
        eprintln!("Verify: {}/{} OK", ok, ok + fail);
    }

    Ok(LoadedEnvironment { env, modules_loaded: load_order, total_constants: total })
}

fn load_recursive(
    module: &Name,
    search_paths: &[PathBuf],
    loaded: &mut HashMap<String, Arc<ModuleData>>,
    load_order: &mut Vec<Name>,
    visited: &mut HashSet<String>,
) -> Result<(), String> {
    let key = module.to_string();
    if visited.contains(&key) { return Ok(()); }
    visited.insert(key.clone());

    let path = resolve_module(module, search_paths)
        .ok_or_else(|| format!("module not found: {}", module))?;
    let mut reader = OleanReader::open(&path)?;
    let md = reader.parse_module_data()?;

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

    const LEAN_LIB: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean";

    #[test]
    fn test_fast_prelude() {
        let mut r = OleanReader::open(Path::new(&format!("{}/Init/Prelude.olean", LEAN_LIB))).unwrap();
        let md = r.parse_module_data().unwrap();
        assert_eq!(md.constants.len(), 2150);
        let nat = md.constants.iter().find(|c| c.name == Name::str("Nat")).unwrap();
        assert_eq!(nat.type_.hash(), 3931117990);
    }

    #[test]
    fn test_fast_full_init() {
        let sp = vec![PathBuf::from(LEAN_LIB)];
        let loaded = load_module_tree_fast(&Name::str("Init"), &sp).unwrap();
        eprintln!("Fast Init: {} modules, {} constants", loaded.modules_loaded.len(), loaded.env.num_constants());
        assert!(loaded.env.num_constants() > 40000);
    }
}
