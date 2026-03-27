use std::fmt;
use std::sync::Arc;

use crate::hash::mix_hash;
use crate::level::Level;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Literal
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum Literal {
    Nat(u64),
    Str(String),
}

impl Literal {
    /// Lean's `Literal.hash`:
    ///   natVal v => hash v   (Nat hash = v as u64)
    ///   strVal v => hash v   (String.hash = hash_str(bytes, 11))
    pub fn hash(&self) -> u64 {
        match self {
            Literal::Nat(n) => *n,
            Literal::Str(s) => crate::hash::hash_str(s.as_bytes(), 11),
        }
    }
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Literal::Nat(a), Literal::Nat(b)) => a == b,
            (Literal::Str(a), Literal::Str(b)) => a == b,
            _ => false,
        }
    }
}
impl Eq for Literal {}

// ---------------------------------------------------------------------------
// BinderInfo
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

// ---------------------------------------------------------------------------
// ExprData — packed u64 matching Lean's Expr.Data
// ---------------------------------------------------------------------------

/// Packed metadata for an expression, matching Lean's Expr.Data layout:
///   bits  0-31: hash (u32)
///   bits 32-39: approxDepth (u8, clamped to 255)
///   bit  40:    hasFVar
///   bit  41:    hasExprMVar
///   bit  42:    hasLevelMVar
///   bit  43:    hasLevelParam
///   bits 44-63: looseBVarRange (u20, clamped to 1048575)
#[derive(Clone, Copy, PartialEq, Eq)]
struct ExprData(u64);

impl ExprData {
    /// Matches C++ `lean_expr_mk_data`.
    fn new(
        hash: u64,
        loose_bvar_range: u32,
        approx_depth: u32,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> Self {
        let depth = approx_depth.min(255);
        let range = loose_bvar_range.min(1048575);
        let h = hash as u32;
        let packed = (h as u64)
            | ((depth as u64) << 32)
            | ((has_fvar as u64) << 40)
            | ((has_expr_mvar as u64) << 41)
            | ((has_level_mvar as u64) << 42)
            | ((has_level_param as u64) << 43)
            | ((range as u64) << 44);
        ExprData(packed)
    }

    /// Matches C++ `lean_expr_mk_app_data`.
    fn new_app(f_data: ExprData, a_data: ExprData) -> Self {
        let fd = f_data.0;
        let ad = a_data.0;
        let depth = f_data.approx_depth().max(a_data.approx_depth()).saturating_add(1).min(255);
        let range = f_data.loose_bvar_range().max(a_data.loose_bvar_range());
        let h = mix_hash(fd, ad) as u32;
        let flags = (fd | ad) & (15u64 << 40); // hasFVar | hasExprMVar | hasLevelMVar | hasLevelParam
        let packed = flags | (h as u64) | ((depth as u64) << 32) | ((range as u64) << 44);
        ExprData(packed)
    }

    fn hash(self) -> u32 { self.0 as u32 }
    fn approx_depth(self) -> u32 { ((self.0 >> 32) & 255) as u32 }
    fn has_fvar(self) -> bool { (self.0 >> 40) & 1 == 1 }
    fn has_expr_mvar(self) -> bool { (self.0 >> 41) & 1 == 1 }
    fn has_level_mvar(self) -> bool { (self.0 >> 42) & 1 == 1 }
    fn has_level_param(self) -> bool { (self.0 >> 43) & 1 == 1 }
    fn loose_bvar_range(self) -> u32 { (self.0 >> 44) as u32 }
}

// ---------------------------------------------------------------------------
// Expr
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Expr(Arc<ExprInner>);

struct ExprInner {
    kind: ExprKindData,
    data: ExprData,
}

#[derive(Clone)]
enum ExprKindData {
    BVar(u64),
    FVar(Name),
    MVar(Name),
    Sort(Level),
    Const(Name, Vec<Level>),
    App(Expr, Expr),
    Lambda(Name, BinderInfo, Expr, Expr),
    Pi(Name, BinderInfo, Expr, Expr),
    Let(Name, Expr, Expr, Expr, bool),
    Lit(Literal),
    MData(Expr),  // simplified: no KVMap needed yet
    Proj(Name, u64, Expr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprKind {
    BVar, FVar, MVar, Sort, Const, App, Lambda, Pi, Let, Lit, MData, Proj,
}

/// Hash a `List Level` the Lean way: `foldl (mixHash r (hash a)) 7`
fn hash_levels(ls: &[Level]) -> u64 {
    ls.iter().fold(7u64, |r, l| mix_hash(r, l.hash()))
}

impl Expr {
    fn new(kind: ExprKindData, data: ExprData) -> Self {
        Expr(Arc::new(ExprInner { kind, data }))
    }

    // -- Constructors -------------------------------------------------------

    pub fn mk_bvar(idx: u64) -> Self {
        let data = ExprData::new(
            mix_hash(7, idx), // hash
            idx.min(1048575) as u32 + 1, // looseBVarRange = idx + 1
            0, false, false, false, false,
        );
        Expr::new(ExprKindData::BVar(idx), data)
    }

    pub fn mk_fvar(n: &Name) -> Self {
        let data = ExprData::new(
            mix_hash(13, n.hash()),
            0, 0, true, false, false, false,
        );
        Expr::new(ExprKindData::FVar(n.clone()), data)
    }

    pub fn mk_mvar(n: &Name) -> Self {
        let data = ExprData::new(
            mix_hash(17, n.hash()),
            0, 0, false, true, false, false,
        );
        Expr::new(ExprKindData::MVar(n.clone()), data)
    }

    pub fn mk_sort(l: &Level) -> Self {
        let data = ExprData::new(
            mix_hash(11, l.hash()),
            0, 0, false, false, l.has_mvar(), l.has_param(),
        );
        Expr::new(ExprKindData::Sort(l.clone()), data)
    }

    pub fn mk_const(n: &Name, ls: &[Level]) -> Self {
        let has_mvar = ls.iter().any(|l| l.has_mvar());
        let has_param = ls.iter().any(|l| l.has_param());
        let data = ExprData::new(
            mix_hash(5, mix_hash(n.hash(), hash_levels(ls))),
            0, 0, false, false, has_mvar, has_param,
        );
        Expr::new(ExprKindData::Const(n.clone(), ls.to_vec()), data)
    }

    pub fn mk_app(f: &Expr, a: &Expr) -> Self {
        let data = ExprData::new_app(f.data(), a.data());
        Expr::new(ExprKindData::App(f.clone(), a.clone()), data)
    }

    pub fn mk_lambda(n: &Name, bi: BinderInfo, domain: &Expr, body: &Expr) -> Self {
        let td = domain.data();
        let bd = body.data();
        let depth = td.approx_depth().max(bd.approx_depth()).saturating_add(1);
        let bvar_range = td.loose_bvar_range()
            .max(bd.loose_bvar_range().saturating_sub(1));
        let data = ExprData::new(
            mix_hash(depth as u64, mix_hash(td.hash() as u64, bd.hash() as u64)),
            bvar_range, depth,
            td.has_fvar() || bd.has_fvar(),
            td.has_expr_mvar() || bd.has_expr_mvar(),
            td.has_level_mvar() || bd.has_level_mvar(),
            td.has_level_param() || bd.has_level_param(),
        );
        Expr::new(ExprKindData::Lambda(n.clone(), bi, domain.clone(), body.clone()), data)
    }

    pub fn mk_pi(n: &Name, bi: BinderInfo, domain: &Expr, body: &Expr) -> Self {
        let td = domain.data();
        let bd = body.data();
        let depth = td.approx_depth().max(bd.approx_depth()).saturating_add(1);
        let bvar_range = td.loose_bvar_range()
            .max(bd.loose_bvar_range().saturating_sub(1));
        let data = ExprData::new(
            mix_hash(depth as u64, mix_hash(td.hash() as u64, bd.hash() as u64)),
            bvar_range, depth,
            td.has_fvar() || bd.has_fvar(),
            td.has_expr_mvar() || bd.has_expr_mvar(),
            td.has_level_mvar() || bd.has_level_mvar(),
            td.has_level_param() || bd.has_level_param(),
        );
        Expr::new(ExprKindData::Pi(n.clone(), bi, domain.clone(), body.clone()), data)
    }

    pub fn mk_let(n: &Name, ty: &Expr, val: &Expr, body: &Expr, nondep: bool) -> Self {
        let td = ty.data();
        let vd = val.data();
        let bd = body.data();
        let depth = td.approx_depth().max(vd.approx_depth()).max(bd.approx_depth()).saturating_add(1);
        let bvar_range = td.loose_bvar_range()
            .max(vd.loose_bvar_range())
            .max(bd.loose_bvar_range().saturating_sub(1));
        let data = ExprData::new(
            mix_hash(depth as u64, mix_hash(td.hash() as u64, mix_hash(vd.hash() as u64, bd.hash() as u64))),
            bvar_range, depth,
            td.has_fvar() || vd.has_fvar() || bd.has_fvar(),
            td.has_expr_mvar() || vd.has_expr_mvar() || bd.has_expr_mvar(),
            td.has_level_mvar() || vd.has_level_mvar() || bd.has_level_mvar(),
            td.has_level_param() || vd.has_level_param() || bd.has_level_param(),
        );
        Expr::new(ExprKindData::Let(n.clone(), ty.clone(), val.clone(), body.clone(), nondep), data)
    }

    pub fn mk_lit(lit: Literal) -> Self {
        let data = ExprData::new(
            mix_hash(3, lit.hash()),
            0, 0, false, false, false, false,
        );
        Expr::new(ExprKindData::Lit(lit), data)
    }

    pub fn mk_mdata(e: &Expr) -> Self {
        let ed = e.data();
        let depth = ed.approx_depth().saturating_add(1);
        let data = ExprData::new(
            mix_hash(depth as u64, ed.hash() as u64),
            ed.loose_bvar_range(), depth,
            ed.has_fvar(), ed.has_expr_mvar(), ed.has_level_mvar(), ed.has_level_param(),
        );
        Expr::new(ExprKindData::MData(e.clone()), data)
    }

    pub fn mk_proj(sname: &Name, idx: u64, e: &Expr) -> Self {
        let ed = e.data();
        let depth = ed.approx_depth().saturating_add(1);
        let data = ExprData::new(
            mix_hash(depth as u64, mix_hash(sname.hash(), mix_hash(idx, ed.hash() as u64))),
            ed.loose_bvar_range(), depth,
            ed.has_fvar(), ed.has_expr_mvar(), ed.has_level_mvar(), ed.has_level_param(),
        );
        Expr::new(ExprKindData::Proj(sname.clone(), idx, e.clone()), data)
    }

    pub fn mk_prop() -> Self {
        Expr::mk_sort(&Level::zero())
    }

    pub fn mk_type() -> Self {
        Expr::mk_sort(&Level::one())
    }

    // -- Accessors ----------------------------------------------------------

    fn data(&self) -> ExprData { self.0.data }

    pub fn hash(&self) -> u32 { self.data().hash() }
    pub fn approx_depth(&self) -> u32 { self.data().approx_depth() }
    pub fn has_fvar(&self) -> bool { self.data().has_fvar() }
    pub fn has_expr_mvar(&self) -> bool { self.data().has_expr_mvar() }
    pub fn has_level_mvar(&self) -> bool { self.data().has_level_mvar() }
    pub fn has_univ_param(&self) -> bool { self.data().has_level_param() }
    pub fn has_mvar(&self) -> bool { self.has_expr_mvar() || self.has_level_mvar() }
    pub fn loose_bvar_range(&self) -> u32 { self.data().loose_bvar_range() }
    pub fn has_loose_bvars(&self) -> bool { self.loose_bvar_range() > 0 }

    pub fn kind(&self) -> ExprKind {
        match &self.0.kind {
            ExprKindData::BVar(_) => ExprKind::BVar,
            ExprKindData::FVar(_) => ExprKind::FVar,
            ExprKindData::MVar(_) => ExprKind::MVar,
            ExprKindData::Sort(_) => ExprKind::Sort,
            ExprKindData::Const(_, _) => ExprKind::Const,
            ExprKindData::App(_, _) => ExprKind::App,
            ExprKindData::Lambda(_, _, _, _) => ExprKind::Lambda,
            ExprKindData::Pi(_, _, _, _) => ExprKind::Pi,
            ExprKindData::Let(_, _, _, _, _) => ExprKind::Let,
            ExprKindData::Lit(_) => ExprKind::Lit,
            ExprKindData::MData(_) => ExprKind::MData,
            ExprKindData::Proj(_, _, _) => ExprKind::Proj,
        }
    }

    pub fn is_bvar(&self) -> bool { matches!(self.kind(), ExprKind::BVar) }
    pub fn is_fvar(&self) -> bool { matches!(self.kind(), ExprKind::FVar) }
    pub fn is_mvar(&self) -> bool { matches!(self.kind(), ExprKind::MVar) }
    pub fn is_sort(&self) -> bool { matches!(self.kind(), ExprKind::Sort) }
    pub fn is_const(&self) -> bool { matches!(self.kind(), ExprKind::Const) }
    pub fn is_app(&self) -> bool { matches!(self.kind(), ExprKind::App) }
    pub fn is_lambda(&self) -> bool { matches!(self.kind(), ExprKind::Lambda) }
    pub fn is_pi(&self) -> bool { matches!(self.kind(), ExprKind::Pi) }
    pub fn is_let(&self) -> bool { matches!(self.kind(), ExprKind::Let) }
    pub fn is_lit(&self) -> bool { matches!(self.kind(), ExprKind::Lit) }
    pub fn is_mdata(&self) -> bool { matches!(self.kind(), ExprKind::MData) }
    pub fn is_proj(&self) -> bool { matches!(self.kind(), ExprKind::Proj) }
    pub fn is_binding(&self) -> bool { self.is_lambda() || self.is_pi() }
    pub fn is_atomic(&self) -> bool {
        matches!(self.kind(), ExprKind::BVar | ExprKind::FVar | ExprKind::MVar | ExprKind::Sort | ExprKind::Const | ExprKind::Lit)
    }

    pub fn bvar_idx(&self) -> u64 {
        match &self.0.kind { ExprKindData::BVar(i) => *i, _ => panic!("bvar_idx") }
    }
    pub fn fvar_name(&self) -> &Name {
        match &self.0.kind { ExprKindData::FVar(n) => n, _ => panic!("fvar_name") }
    }
    pub fn mvar_name(&self) -> &Name {
        match &self.0.kind { ExprKindData::MVar(n) => n, _ => panic!("mvar_name") }
    }
    pub fn sort_level(&self) -> &Level {
        match &self.0.kind { ExprKindData::Sort(l) => l, _ => panic!("sort_level") }
    }
    pub fn const_name(&self) -> &Name {
        match &self.0.kind { ExprKindData::Const(n, _) => n, _ => panic!("const_name") }
    }
    pub fn const_levels(&self) -> &[Level] {
        match &self.0.kind { ExprKindData::Const(_, ls) => ls, _ => panic!("const_levels") }
    }
    pub fn app_fn(&self) -> &Expr {
        match &self.0.kind { ExprKindData::App(f, _) => f, _ => panic!("app_fn") }
    }
    pub fn app_arg(&self) -> &Expr {
        match &self.0.kind { ExprKindData::App(_, a) => a, _ => panic!("app_arg") }
    }
    pub fn binding_name(&self) -> &Name {
        match &self.0.kind {
            ExprKindData::Lambda(n, _, _, _) | ExprKindData::Pi(n, _, _, _) => n,
            _ => panic!("binding_name"),
        }
    }
    pub fn binding_info(&self) -> BinderInfo {
        match &self.0.kind {
            ExprKindData::Lambda(_, bi, _, _) | ExprKindData::Pi(_, bi, _, _) => *bi,
            _ => panic!("binding_info"),
        }
    }
    pub fn binding_domain(&self) -> &Expr {
        match &self.0.kind {
            ExprKindData::Lambda(_, _, d, _) | ExprKindData::Pi(_, _, d, _) => d,
            _ => panic!("binding_domain"),
        }
    }
    pub fn binding_body(&self) -> &Expr {
        match &self.0.kind {
            ExprKindData::Lambda(_, _, _, b) | ExprKindData::Pi(_, _, _, b) => b,
            _ => panic!("binding_body"),
        }
    }
    pub fn let_name(&self) -> &Name {
        match &self.0.kind { ExprKindData::Let(n, _, _, _, _) => n, _ => panic!("let_name") }
    }
    pub fn let_type(&self) -> &Expr {
        match &self.0.kind { ExprKindData::Let(_, t, _, _, _) => t, _ => panic!("let_type") }
    }
    pub fn let_value(&self) -> &Expr {
        match &self.0.kind { ExprKindData::Let(_, _, v, _, _) => v, _ => panic!("let_value") }
    }
    pub fn let_body(&self) -> &Expr {
        match &self.0.kind { ExprKindData::Let(_, _, _, b, _) => b, _ => panic!("let_body") }
    }
    pub fn let_nondep(&self) -> bool {
        match &self.0.kind { ExprKindData::Let(_, _, _, _, nd) => *nd, _ => panic!("let_nondep") }
    }
    pub fn lit_value(&self) -> &Literal {
        match &self.0.kind { ExprKindData::Lit(l) => l, _ => panic!("lit_value") }
    }
    pub fn mdata_expr(&self) -> &Expr {
        match &self.0.kind { ExprKindData::MData(e) => e, _ => panic!("mdata_expr") }
    }
    pub fn proj_sname(&self) -> &Name {
        match &self.0.kind { ExprKindData::Proj(s, _, _) => s, _ => panic!("proj_sname") }
    }
    pub fn proj_idx(&self) -> u64 {
        match &self.0.kind { ExprKindData::Proj(_, i, _) => *i, _ => panic!("proj_idx") }
    }
    pub fn proj_expr(&self) -> &Expr {
        match &self.0.kind { ExprKindData::Proj(_, _, e) => e, _ => panic!("proj_expr") }
    }

    // -- App utilities ------------------------------------------------------

    pub fn get_app_fn(&self) -> &Expr {
        let mut e = self;
        while e.is_app() {
            e = e.app_fn();
        }
        e
    }

    pub fn get_app_args(&self) -> Vec<Expr> {
        let mut args = Vec::new();
        let mut e = self;
        while e.is_app() {
            args.push(e.app_arg().clone());
            e = e.app_fn();
        }
        args.reverse();
        args
    }

    pub fn get_app_num_args(&self) -> usize {
        let mut n = 0;
        let mut e = self;
        while e.is_app() {
            n += 1;
            e = e.app_fn();
        }
        n
    }

    /// Build `mk_app(mk_app(...mk_app(f, args[0]), args[1])..., args[n-1])`
    pub fn mk_app_n(f: &Expr, args: &[Expr]) -> Expr {
        let mut e = f.clone();
        for a in args {
            e = Expr::mk_app(&e, a);
        }
        e
    }

    // -- Update (structural sharing) ----------------------------------------

    pub fn update_app(&self, new_fn: &Expr, new_arg: &Expr) -> Expr {
        if Arc::ptr_eq(&self.app_fn().0, &new_fn.0)
            && Arc::ptr_eq(&self.app_arg().0, &new_arg.0)
        {
            self.clone()
        } else {
            Expr::mk_app(new_fn, new_arg)
        }
    }

    pub fn update_binding(&self, new_domain: &Expr, new_body: &Expr) -> Expr {
        if Arc::ptr_eq(&self.binding_domain().0, &new_domain.0)
            && Arc::ptr_eq(&self.binding_body().0, &new_body.0)
        {
            self.clone()
        } else if self.is_lambda() {
            Expr::mk_lambda(self.binding_name(), self.binding_info(), new_domain, new_body)
        } else {
            Expr::mk_pi(self.binding_name(), self.binding_info(), new_domain, new_body)
        }
    }

    pub fn update_sort(&self, new_level: &Level) -> Expr {
        if self.sort_level().ptr_eq(new_level) {
            self.clone()
        } else {
            Expr::mk_sort(new_level)
        }
    }

    pub fn update_const(&self, new_levels: &[Level]) -> Expr {
        let old = self.const_levels();
        if old.len() == new_levels.len()
            && old.iter().zip(new_levels).all(|(a, b)| a.ptr_eq(b))
        {
            self.clone()
        } else {
            Expr::mk_const(self.const_name(), new_levels)
        }
    }

    pub fn update_let(&self, new_type: &Expr, new_value: &Expr, new_body: &Expr) -> Expr {
        if Arc::ptr_eq(&self.let_type().0, &new_type.0)
            && Arc::ptr_eq(&self.let_value().0, &new_value.0)
            && Arc::ptr_eq(&self.let_body().0, &new_body.0)
        {
            self.clone()
        } else {
            Expr::mk_let(self.let_name(), new_type, new_value, new_body, self.let_nondep())
        }
    }

    pub fn update_mdata(&self, new_e: &Expr) -> Expr {
        if Arc::ptr_eq(&self.mdata_expr().0, &new_e.0) {
            self.clone()
        } else {
            Expr::mk_mdata(new_e)
        }
    }

    pub fn update_proj(&self, new_e: &Expr) -> Expr {
        if Arc::ptr_eq(&self.proj_expr().0, &new_e.0) {
            self.clone()
        } else {
            Expr::mk_proj(self.proj_sname(), self.proj_idx(), new_e)
        }
    }

    // -- Arrow detection ----------------------------------------------------

    /// True if `Pi` where body has no loose bvar 0 (non-dependent arrow).
    pub fn is_arrow(&self) -> bool {
        self.is_pi() && self.binding_body().loose_bvar_range() == 0
    }

    // -- Pointer equality ---------------------------------------------------

    pub fn ptr_eq(&self, other: &Expr) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

// -- Structural equality (matches C++ lean_expr_beq) -------------------------

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) { return true; }
        if self.hash() != other.hash() { return false; }
        if self.kind() != other.kind() { return false; }
        match (&self.0.kind, &other.0.kind) {
            (ExprKindData::BVar(a), ExprKindData::BVar(b)) => a == b,
            (ExprKindData::FVar(a), ExprKindData::FVar(b)) => a == b,
            (ExprKindData::MVar(a), ExprKindData::MVar(b)) => a == b,
            (ExprKindData::Sort(a), ExprKindData::Sort(b)) => a == b,
            (ExprKindData::Const(n1, ls1), ExprKindData::Const(n2, ls2)) => n1 == n2 && ls1 == ls2,
            (ExprKindData::App(f1, a1), ExprKindData::App(f2, a2)) => f1 == f2 && a1 == a2,
            (ExprKindData::Lambda(_, _, d1, b1), ExprKindData::Lambda(_, _, d2, b2)) => d1 == d2 && b1 == b2,
            (ExprKindData::Pi(_, _, d1, b1), ExprKindData::Pi(_, _, d2, b2)) => d1 == d2 && b1 == b2,
            (ExprKindData::Let(_, t1, v1, b1, _), ExprKindData::Let(_, t2, v2, b2, _)) => t1 == t2 && v1 == v2 && b1 == b2,
            (ExprKindData::Lit(a), ExprKindData::Lit(b)) => a == b,
            (ExprKindData::MData(a), ExprKindData::MData(b)) => a == b,
            (ExprKindData::Proj(s1, i1, e1), ExprKindData::Proj(s2, i2, e2)) => s1 == s2 && i1 == i2 && e1 == e2,
            _ => false,
        }
    }
}
impl Eq for Expr {}

impl std::hash::Hash for Expr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.hash());
    }
}

// -- Display ----------------------------------------------------------------

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0.kind {
            ExprKindData::BVar(i) => write!(f, "#{}", i),
            ExprKindData::FVar(n) => write!(f, "{}", n),
            ExprKindData::MVar(n) => write!(f, "?{}", n),
            ExprKindData::Sort(l) => {
                if l.is_zero() { write!(f, "Prop") }
                else if l.is_one() { write!(f, "Type") }
                else { write!(f, "Sort {}", l) }
            }
            ExprKindData::Const(n, ls) => {
                if ls.is_empty() { write!(f, "{}", n) }
                else {
                    let lvls: Vec<String> = ls.iter().map(|l| l.to_string()).collect();
                    write!(f, "{}.{{{}}}", n, lvls.join(", "))
                }
            }
            ExprKindData::App(func, arg) => write!(f, "({} {})", func, arg),
            ExprKindData::Lambda(n, _, dom, body) => write!(f, "(fun {} : {} => {})", n, dom, body),
            ExprKindData::Pi(n, _, dom, body) => {
                if self.is_arrow() {
                    write!(f, "({} -> {})", dom, body)
                } else {
                    write!(f, "(forall {} : {}, {})", n, dom, body)
                }
            }
            ExprKindData::Let(n, ty, val, body, _) => write!(f, "(let {} : {} := {} in {})", n, ty, val, body),
            ExprKindData::Lit(Literal::Nat(n)) => write!(f, "{}", n),
            ExprKindData::Lit(Literal::Str(s)) => write!(f, "\"{}\"", s),
            ExprKindData::MData(e) => write!(f, "{}", e),
            ExprKindData::Proj(s, i, e) => write!(f, "{}.{} {}", s, i, e),
        }
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Expr({})", self)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn nat_const() -> Expr { Expr::mk_const(&Name::str("Nat"), &[]) }
    fn nat_zero() -> Expr { Expr::mk_const(&Name::str("Nat.zero"), &[]) }
    fn nat_succ() -> Expr { Expr::mk_const(&Name::str("Nat.succ"), &[]) }

    #[test]
    fn test_bvar() {
        let b0 = Expr::mk_bvar(0);
        let b1 = Expr::mk_bvar(1);
        assert!(b0.is_bvar());
        assert_eq!(b0.bvar_idx(), 0);
        assert_eq!(b0.loose_bvar_range(), 1);
        assert_eq!(b1.loose_bvar_range(), 2);
        assert!(!b0.has_fvar());
    }

    #[test]
    fn test_fvar() {
        let x = Expr::mk_fvar(&Name::str("x"));
        assert!(x.is_fvar());
        assert!(x.has_fvar());
        assert_eq!(x.fvar_name(), &Name::str("x"));
    }

    #[test]
    fn test_sort() {
        let prop = Expr::mk_prop();
        assert!(prop.is_sort());
        assert!(prop.sort_level().is_zero());

        let ty = Expr::mk_type();
        assert!(ty.sort_level().is_one());
    }

    #[test]
    fn test_const() {
        let n = Expr::mk_const(&Name::str("Nat"), &[]);
        assert!(n.is_const());
        assert_eq!(n.const_name(), &Name::str("Nat"));
        assert!(n.const_levels().is_empty());
    }

    #[test]
    fn test_const_with_levels() {
        let u = Level::mk_param(&Name::str("u"));
        let e = Expr::mk_const(&Name::str("List"), &[u.clone()]);
        assert_eq!(e.const_levels().len(), 1);
        assert!(e.has_univ_param());
    }

    #[test]
    fn test_app() {
        let f = nat_succ();
        let z = nat_zero();
        let app = Expr::mk_app(&f, &z);
        assert!(app.is_app());
        assert_eq!(app.app_fn(), &f);
        assert_eq!(app.app_arg(), &z);
        assert_eq!(app.get_app_fn(), &f);
        assert_eq!(app.get_app_num_args(), 1);
    }

    #[test]
    fn test_nested_app() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let c = Expr::mk_const(&Name::str("c"), &[]);
        let e = Expr::mk_app_n(&f, &[a.clone(), b.clone(), c.clone()]);
        assert_eq!(e.get_app_fn(), &f);
        assert_eq!(e.get_app_num_args(), 3);
        let args = e.get_app_args();
        assert_eq!(args[0], a);
        assert_eq!(args[1], b);
        assert_eq!(args[2], c);
    }

    #[test]
    fn test_lambda() {
        let nat = nat_const();
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        assert!(lam.is_lambda());
        assert!(lam.is_binding());
        assert!(!lam.has_loose_bvars()); // bvar(0) is bound by the lambda
        assert_eq!(lam.binding_name(), &Name::str("x"));
    }

    #[test]
    fn test_pi() {
        let nat = nat_const();
        let body = nat.clone(); // Nat -> Nat (non-dependent)
        let pi = Expr::mk_pi(&Name::str("x"), BinderInfo::Default, &nat, &body);
        assert!(pi.is_pi());
        assert!(pi.is_arrow());
    }

    #[test]
    fn test_pi_dependent() {
        let nat = nat_const();
        let body = Expr::mk_bvar(0); // dependent: body uses bound var
        let pi = Expr::mk_pi(&Name::str("x"), BinderInfo::Default, &nat, &body);
        assert!(pi.is_pi());
        assert!(!pi.is_arrow()); // dependent
    }

    #[test]
    fn test_let() {
        let nat = nat_const();
        let zero = nat_zero();
        let body = Expr::mk_bvar(0);
        let e = Expr::mk_let(&Name::str("x"), &nat, &zero, &body, false);
        assert!(e.is_let());
        assert!(!e.has_loose_bvars());
    }

    #[test]
    fn test_lit() {
        let n = Expr::mk_lit(Literal::Nat(42));
        assert!(n.is_lit());
        assert_eq!(*n.lit_value(), Literal::Nat(42));

        let s = Expr::mk_lit(Literal::Str("hello".into()));
        assert_eq!(*s.lit_value(), Literal::Str("hello".into()));
    }

    #[test]
    fn test_proj() {
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let p = Expr::mk_proj(&Name::str("Prod"), 0, &a);
        assert!(p.is_proj());
        assert_eq!(p.proj_sname(), &Name::str("Prod"));
        assert_eq!(p.proj_idx(), 0);
    }

    #[test]
    fn test_equality() {
        let a = Expr::mk_const(&Name::str("Nat"), &[]);
        let b = Expr::mk_const(&Name::str("Nat"), &[]);
        let c = Expr::mk_const(&Name::str("Bool"), &[]);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn test_hash_consistency() {
        let a = Expr::mk_app(&nat_succ(), &nat_zero());
        let b = Expr::mk_app(&nat_succ(), &nat_zero());
        assert_eq!(a.hash(), b.hash());
    }

    #[test]
    fn test_loose_bvar_range_binding() {
        // lambda x. #1 — bvar 1 escapes the single binder
        let body = Expr::mk_bvar(1);
        let nat = nat_const();
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        assert_eq!(lam.loose_bvar_range(), 1);

        // lambda x. #0 — bvar 0 is captured
        let body2 = Expr::mk_bvar(0);
        let lam2 = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body2);
        assert_eq!(lam2.loose_bvar_range(), 0);
    }

    #[test]
    fn test_flags_propagation() {
        let fv = Expr::mk_fvar(&Name::str("x"));
        let mv = Expr::mk_mvar(&Name::str("m"));
        let app = Expr::mk_app(&fv, &mv);
        assert!(app.has_fvar());
        assert!(app.has_expr_mvar());

        let u = Level::mk_param(&Name::str("u"));
        let c = Expr::mk_const(&Name::str("List"), &[u]);
        assert!(c.has_univ_param());
    }

    #[test]
    fn test_update_sharing() {
        let f = nat_succ();
        let z = nat_zero();
        let app = Expr::mk_app(&f, &z);
        let same = app.update_app(&f, &z);
        // Should be pointer-equal since nothing changed
        assert!(app.ptr_eq(&same));
    }

    #[test]
    fn test_update_different() {
        let f = nat_succ();
        let z = nat_zero();
        let app = Expr::mk_app(&f, &z);
        let one = Expr::mk_app(&nat_succ(), &nat_zero());
        let new_app = app.update_app(&f, &one);
        assert!(!app.ptr_eq(&new_app));
        assert_eq!(new_app.app_arg(), &one);
    }

    #[test]
    fn test_mdata() {
        let inner = nat_zero();
        let md = Expr::mk_mdata(&inner);
        assert!(md.is_mdata());
        assert_eq!(md.mdata_expr(), &inner);
    }

    #[test]
    fn test_display() {
        assert_eq!(Expr::mk_prop().to_string(), "Prop");
        assert_eq!(Expr::mk_type().to_string(), "Type");
        assert_eq!(Expr::mk_bvar(0).to_string(), "#0");
        assert_eq!(Expr::mk_lit(Literal::Nat(42)).to_string(), "42");
    }
}
