//! Stages 05–10: Type Checker — WHNF, type inference, definitional equality,
//! inductive reduction, quotient reduction, declaration checking.

use std::collections::HashMap;

use crate::debruijn::*;
use crate::env::*;
use crate::expr::*;
use crate::level::Level;
use crate::local_ctx::LocalContext;
use crate::name::Name;

// ============================================================================
// Equiv Manager (Stage 05.4) — union-find for proven equalities
// ============================================================================

#[derive(Clone, Debug, Default)]
pub struct EquivManager {
    parent: Vec<usize>,
    rank: Vec<u8>,
    expr_to_id: HashMap<u64, usize>, // hash(ptr) → id (simplified key)
}

impl EquivManager {
    pub fn new() -> Self { Self::default() }

    fn get_or_create(&mut self, ptr: u64) -> usize {
        if let Some(&id) = self.expr_to_id.get(&ptr) {
            id
        } else {
            let id = self.parent.len();
            self.parent.push(id);
            self.rank.push(0);
            self.expr_to_id.insert(ptr, id);
            id
        }
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]]; // path compression
            x = self.parent[x];
        }
        x
    }

    pub fn add_equiv(&mut self, a: &Expr, b: &Expr) {
        let ka = a as *const Expr as u64;
        let kb = b as *const Expr as u64;
        let ia = self.get_or_create(ka);
        let ib = self.get_or_create(kb);
        let ra = self.find(ia);
        let rb = self.find(ib);
        if ra == rb { return; }
        if self.rank[ra] < self.rank[rb] {
            self.parent[ra] = rb;
        } else if self.rank[ra] > self.rank[rb] {
            self.parent[rb] = ra;
        } else {
            self.parent[rb] = ra;
            self.rank[ra] += 1;
        }
    }

    pub fn is_equiv(&mut self, a: &Expr, b: &Expr) -> bool {
        let ka = a as *const Expr as u64;
        let kb = b as *const Expr as u64;
        if ka == kb { return true; }
        let ia = match self.expr_to_id.get(&ka) { Some(&id) => id, None => return false };
        let ib = match self.expr_to_id.get(&kb) { Some(&id) => id, None => return false };
        self.find(ia) == self.find(ib)
    }
}

// ============================================================================
// TypeChecker
// ============================================================================

pub struct TypeChecker {
    env: Environment,
    lctx: LocalContext,
    infer_cache: HashMap<u64, Expr>,
    whnf_cache: HashMap<u64, Expr>,
    name_counter: u64,
}

impl TypeChecker {
    pub fn new(env: Environment, lctx: LocalContext) -> Self {
        TypeChecker {
            env,
            lctx,
            infer_cache: HashMap::new(),
            whnf_cache: HashMap::new(),
            name_counter: 0,
        }
    }

    pub fn env(&self) -> &Environment { &self.env }
    pub fn lctx(&self) -> &LocalContext { &self.lctx }
    pub fn lctx_mut(&mut self) -> &mut LocalContext { &mut self.lctx }

    fn fresh_name(&mut self) -> Name {
        let n = self.name_counter;
        self.name_counter += 1;
        Name::mk_numeral(&Name::mk_string(&Name::anonymous(), "_tc"), n)
    }

    // ========================================================================
    // Stage 05: WHNF
    // ========================================================================

    /// WHNF core: beta, zeta, iota (recursor/proj/quot), but NOT delta.
    pub fn whnf_core(&mut self, e: &Expr) -> Expr {
        match e.kind() {
            ExprKind::BVar | ExprKind::Sort | ExprKind::MVar
            | ExprKind::Pi | ExprKind::Const | ExprKind::Lambda | ExprKind::Lit => e.clone(),
            ExprKind::FVar => {
                // Zeta: if let-bound in lctx, unfold
                if let Some(decl) = self.lctx.find(e.fvar_name()) {
                    if let Some(val) = decl.get_value() {
                        let v = val.clone();
                        return self.whnf_core(&v);
                    }
                }
                e.clone()
            }
            ExprKind::MData => {
                let inner = e.mdata_expr().clone();
                self.whnf_core(&inner)
            }
            ExprKind::Let => {
                let val = e.let_value().clone();
                let body = e.let_body().clone();
                let r = instantiate1(&body, &val);
                self.whnf_core(&r)
            }
            ExprKind::Proj => {
                self.reduce_proj(e).unwrap_or_else(|| e.clone())
            }
            ExprKind::App => {
                let fn_e = e.app_fn().clone();
                let whnf_fn = self.whnf_core(&fn_e);
                if whnf_fn.is_lambda() {
                    // Beta reduction
                    let app_arg = e.app_arg().clone();
                    let r = instantiate1(whnf_fn.binding_body(), &app_arg);
                    return self.whnf_core(&r);
                }
                // Try recursor reduction
                let full = if whnf_fn.ptr_eq(&fn_e) {
                    e.clone()
                } else {
                    e.update_app(&whnf_fn, e.app_arg())
                };
                if let Some(r) = self.reduce_recursor(&full) {
                    return self.whnf_core(&r);
                }
                if let Some(r) = self.reduce_quot(&full) {
                    return self.whnf_core(&r);
                }
                full
            }
        }
    }

    /// Full WHNF with delta reduction. Cached.
    pub fn whnf(&mut self, e: &Expr) -> Expr {
        let key = e.hash() as u64 | ((e as *const Expr as u64) << 32);
        if let Some(cached) = self.whnf_cache.get(&key) {
            return cached.clone();
        }
        let e1 = self.whnf_core(e);
        let result = if let Some(unfolded) = self.unfold_definition(&e1) {
            self.whnf(&unfolded)
        } else {
            e1
        };
        self.whnf_cache.insert(key, result.clone());
        result
    }

    /// Unfold a constant or App(Const, ...) if it's a reducible definition.
    fn unfold_definition(&self, e: &Expr) -> Option<Expr> {
        let head = e.get_app_fn();
        if !head.is_const() { return None; }
        let info = self.env.find(head.const_name())?;
        match &info.kind {
            ConstantInfoKind::Definition { value, hints, .. } => {
                if matches!(hints, ReducibilityHints::Opaque) { return None; }
                let val = instantiate_lparams(value, info.get_lparams(), head.const_levels());
                let args = e.get_app_args();
                Some(Expr::mk_app_n(&val, &args))
            }
            _ => None,
        }
    }

    /// Reduce projection: Proj(S, i, ctor_app) → field[i].
    fn reduce_proj(&mut self, e: &Expr) -> Option<Expr> {
        if !e.is_proj() { return None; }
        let major = e.proj_expr().clone();
        let major_whnf = self.whnf(&major);
        let ctor = major_whnf.get_app_fn();
        if !ctor.is_const() { return None; }
        let ctor_info = self.env.find(ctor.const_name())?;
        match &ctor_info.kind {
            ConstantInfoKind::Constructor { nparams, .. } => {
                let args = major_whnf.get_app_args();
                let field_idx = *nparams as usize + e.proj_idx() as usize;
                args.get(field_idx).cloned()
            }
            _ => None,
        }
    }

    // ========================================================================
    // Stage 06: Type Inference
    // ========================================================================

    pub fn infer_type(&mut self, e: &Expr) -> Expr {
        let key = e.hash() as u64 | ((e as *const Expr as u64) << 32);
        if let Some(cached) = self.infer_cache.get(&key) {
            return cached.clone();
        }
        let result = self.infer_type_uncached(e);
        self.infer_cache.insert(key, result.clone());
        result
    }

    fn infer_type_uncached(&mut self, e: &Expr) -> Expr {
        match e.kind() {
            ExprKind::BVar => panic!("infer_type: unexpected bound variable"),
            ExprKind::Lit => match e.lit_value() {
                Literal::Nat(_) => Expr::mk_const(&Name::str("Nat"), &[]),
                Literal::Str(_) => Expr::mk_const(&Name::str("String"), &[]),
            },
            ExprKind::MData => {
                let inner = e.mdata_expr().clone();
                self.infer_type(&inner)
            }
            ExprKind::FVar => {
                if let Some(decl) = self.lctx.find(e.fvar_name()) {
                    decl.get_type().clone()
                } else {
                    panic!("unknown free variable: {}", e.fvar_name())
                }
            }
            ExprKind::MVar => panic!("infer_type: unexpected metavariable"),
            ExprKind::Sort => {
                Expr::mk_sort(&Level::mk_succ(e.sort_level()))
            }
            ExprKind::Const => {
                let info = self.env.get(e.const_name());
                instantiate_lparams(&info.type_, info.get_lparams(), e.const_levels())
            }
            ExprKind::App => {
                let fn_type = self.infer_type(e.app_fn());
                let fn_type_whnf = self.whnf(&fn_type);
                if !fn_type_whnf.is_pi() {
                    panic!("function expected, got {}", fn_type_whnf);
                }
                let arg = e.app_arg().clone();
                instantiate1(fn_type_whnf.binding_body(), &arg)
            }
            ExprKind::Lambda => {
                let name = self.fresh_name();
                let dom = e.binding_domain().clone();
                let fvar = self.lctx.mk_local_decl(
                    name, e.binding_name().clone(), dom, e.binding_info(),
                );
                let body = instantiate1(e.binding_body(), &fvar);
                let body_type = self.infer_type(&body);
                self.lctx.mk_pi(&[fvar], &body_type)
            }
            ExprKind::Pi => {
                let name = self.fresh_name();
                let dom = e.binding_domain().clone();
                let s1 = self.infer_sort(&dom);
                let fvar = self.lctx.mk_local_decl(
                    name, e.binding_name().clone(), dom, e.binding_info(),
                );
                let body = instantiate1(e.binding_body(), &fvar);
                let s2 = self.infer_sort(&body);
                Expr::mk_sort(&Level::mk_imax(&s1, &s2))
            }
            ExprKind::Let => {
                let name = self.fresh_name();
                let ty = e.let_type().clone();
                let val = e.let_value().clone();
                let fvar = self.lctx.mk_let_decl(
                    name, e.let_name().clone(), ty, val,
                );
                let body = instantiate1(e.let_body(), &fvar);
                let body_type = self.infer_type(&body);
                // Abstract fvar back out (it might not appear in body_type)
                instantiate1(&abstract1(&body_type, &fvar), &e.let_value().clone())
            }
            ExprKind::Proj => {
                let struct_type = self.infer_type(e.proj_expr());
                let struct_type_whnf = self.whnf(&struct_type);
                let type_fn = struct_type_whnf.get_app_fn();
                if !type_fn.is_const() {
                    // Can't determine projection type — return Sort as fallback
                    return Expr::mk_type();
                }
                let info = self.env.get(type_fn.const_name());
                match &info.kind {
                    ConstantInfoKind::Inductive { ctors, nparams, .. } => {
                        let ctor_name = &ctors[0];
                        let ctor_info = self.env.get(ctor_name);
                        let mut ctor_type = instantiate_lparams(&ctor_info.type_, ctor_info.get_lparams(), type_fn.const_levels());
                        let params = struct_type_whnf.get_app_args();
                        // Skip nparams pi's, substituting with actual params
                        for p in params.iter().take(*nparams as usize) {
                            ctor_type = self.whnf(&ctor_type);
                            if ctor_type.is_pi() {
                                ctor_type = instantiate1(ctor_type.binding_body(), p);
                            }
                        }
                        // Skip proj_idx fields, substituting with projections
                        for j in 0..e.proj_idx() {
                            ctor_type = self.whnf(&ctor_type);
                            if ctor_type.is_pi() {
                                let proj = Expr::mk_proj(e.proj_sname(), j, e.proj_expr());
                                ctor_type = instantiate1(ctor_type.binding_body(), &proj);
                            }
                        }
                        // The domain of the current pi is the field type
                        ctor_type = self.whnf(&ctor_type);
                        if ctor_type.is_pi() {
                            ctor_type.binding_domain().clone()
                        } else {
                            panic!("invalid projection index")
                        }
                    }
                    _ => return Expr::mk_type(), // fallback for non-inductive proj
                }
            }
        }
    }

    /// Infer type and ensure it's a Sort, return the level.
    fn infer_sort(&mut self, e: &Expr) -> Level {
        let ty = self.infer_type(e);
        let ty_whnf = self.whnf(&ty);
        if ty_whnf.is_sort() {
            ty_whnf.sort_level().clone()
        } else {
            panic!("type expected, got {}", ty_whnf)
        }
    }

    /// Ensure e has type Pi, return the Pi.
    pub fn ensure_pi(&mut self, e: &Expr) -> Expr {
        let w = self.whnf(e);
        if w.is_pi() { w } else { panic!("function expected") }
    }

    /// Ensure e has type Sort, return the Sort.
    pub fn ensure_sort(&mut self, e: &Expr) -> Expr {
        let w = self.whnf(e);
        if w.is_sort() { w } else { panic!("type expected") }
    }

    // ========================================================================
    // Stage 07: Definitional Equality
    // ========================================================================

    pub fn is_def_eq(&mut self, a: &Expr, b: &Expr) -> bool {
        // Quick structural check
        if a == b { return true; }
        if a.ptr_eq(b) { return true; }

        // WHNF both sides
        let a_whnf = self.whnf(a);
        let b_whnf = self.whnf(b);

        if a_whnf == b_whnf { return true; }
        if a_whnf.ptr_eq(&b_whnf) { return true; }

        // Sort-Sort
        if a_whnf.is_sort() && b_whnf.is_sort() {
            return a_whnf.sort_level().is_equivalent(b_whnf.sort_level());
        }

        // Same head constant → compare args
        if a_whnf.kind() == b_whnf.kind() {
            match (a_whnf.kind(), b_whnf.kind()) {
                (ExprKind::Const, _) => {
                    if a_whnf.const_name() == b_whnf.const_name() {
                        let ls1 = a_whnf.const_levels();
                        let ls2 = b_whnf.const_levels();
                        return ls1.len() == ls2.len()
                            && ls1.iter().zip(ls2).all(|(l1, l2)| l1.is_equivalent(l2));
                    }
                }
                (ExprKind::FVar, _) => {
                    return a_whnf.fvar_name() == b_whnf.fvar_name();
                }
                (ExprKind::Lambda, _) | (ExprKind::Pi, _) => {
                    return self.is_def_eq_binding(&a_whnf, &b_whnf);
                }
                (ExprKind::App, _) => {
                    // Compare as applications with same head
                    let fn_a = a_whnf.get_app_fn();
                    let fn_b = b_whnf.get_app_fn();
                    if fn_a == fn_b {
                        let args_a = a_whnf.get_app_args();
                        let args_b = b_whnf.get_app_args();
                        if args_a.len() == args_b.len() {
                            return args_a.iter().zip(args_b.iter())
                                .all(|(x, y)| self.is_def_eq(x, y));
                        }
                    }
                }
                (ExprKind::Lit, _) => {
                    return a_whnf.lit_value() == b_whnf.lit_value();
                }
                _ => {}
            }
        }

        // Lazy delta: try unfolding one or both sides
        if a_whnf.is_app() || a_whnf.is_const() || b_whnf.is_app() || b_whnf.is_const() {
            let unfold_a = self.unfold_definition(&a_whnf);
            let unfold_b = self.unfold_definition(&b_whnf);
            match (unfold_a, unfold_b) {
                (Some(ua), Some(ub)) => {
                    if self.is_def_eq(&ua, &ub) { return true; }
                }
                (Some(ua), None) => {
                    if self.is_def_eq(&ua, &b_whnf) { return true; }
                }
                (None, Some(ub)) => {
                    if self.is_def_eq(&a_whnf, &ub) { return true; }
                }
                (None, None) => {}
            }
        }

        // Eta: if one is lambda and other is not
        if a_whnf.is_lambda() && !b_whnf.is_lambda() {
            return self.is_def_eq_eta(&a_whnf, &b_whnf);
        }
        if b_whnf.is_lambda() && !a_whnf.is_lambda() {
            return self.is_def_eq_eta(&b_whnf, &a_whnf);
        }

        // Proof irrelevance
        if self.is_proof_irrelevant(&a_whnf, &b_whnf) {
            return true;
        }

        false
    }

    fn is_def_eq_binding(&mut self, a: &Expr, b: &Expr) -> bool {
        if !self.is_def_eq(a.binding_domain(), b.binding_domain()) {
            return false;
        }
        let name = self.fresh_name();
        let fvar = self.lctx.mk_local_decl(
            name, a.binding_name().clone(), a.binding_domain().clone(), a.binding_info(),
        );
        let a_body = instantiate1(a.binding_body(), &fvar);
        let b_body = instantiate1(b.binding_body(), &fvar);
        self.is_def_eq(&a_body, &b_body)
    }

    fn is_def_eq_eta(&mut self, lam: &Expr, other: &Expr) -> bool {
        // lam = λx. body, other is not lambda
        // check: λx. body =?= λx. other x (eta expand other)
        let name = self.fresh_name();
        let fvar = self.lctx.mk_local_decl(
            name, lam.binding_name().clone(), lam.binding_domain().clone(), lam.binding_info(),
        );
        let lam_body = instantiate1(lam.binding_body(), &fvar);
        let other_app = Expr::mk_app(other, &fvar);
        self.is_def_eq(&lam_body, &other_app)
    }

    fn is_proof_irrelevant(&mut self, a: &Expr, b: &Expr) -> bool {
        // If both have types that are Prop, they're equal
        let ty_a = self.infer_type(a);
        let ty_a_whnf = self.whnf(&ty_a);
        if !ty_a_whnf.is_sort() || !ty_a_whnf.sort_level().is_zero() {
            return false;
        }
        let ty_b = self.infer_type(b);
        let ty_b_whnf = self.whnf(&ty_b);
        if !ty_b_whnf.is_sort() || !ty_b_whnf.sort_level().is_zero() {
            return false;
        }
        self.is_def_eq(&ty_a, &ty_b)
    }

    // ========================================================================
    // Stage 08: Inductive (recursor reduction)
    // ========================================================================

    /// Try to reduce a recursor application.
    fn reduce_recursor(&mut self, e: &Expr) -> Option<Expr> {
        let fn_e = e.get_app_fn();
        if !fn_e.is_const() { return None; }
        let info = self.env.find(fn_e.const_name())?;
        let rec = match &info.kind {
            ConstantInfoKind::Recursor { nparams, nindices, nmotives, nminors, rules, .. } => {
                (info.clone(), *nparams, *nindices, *nmotives, *nminors, rules.clone())
            }
            _ => return None,
        };
        let (info, nparams, _nindices, nmotives, nminors, rules) = rec;
        let args = e.get_app_args();
        let major_idx = (nparams + nmotives + nminors) as usize;
        if args.len() <= major_idx { return None; }

        let major = &args[major_idx];
        let major_whnf = self.whnf(major);
        let ctor = major_whnf.get_app_fn();
        if !ctor.is_const() { return None; }

        // Find matching rule
        let rule = rules.iter().find(|r| &r.ctor_name == ctor.const_name())?;

        // Build result
        let mut rhs = instantiate_lparams(&rule.rhs, info.get_lparams(), fn_e.const_levels());
        // Apply params
        let mut result_args: Vec<Expr> = args[..nparams as usize].to_vec();
        // Apply motives
        result_args.extend_from_slice(&args[nparams as usize..(nparams + nmotives) as usize]);
        // Apply minors
        result_args.extend_from_slice(&args[(nparams + nmotives) as usize..major_idx]);
        // Apply constructor fields (skip nparams in ctor args)
        let ctor_args = major_whnf.get_app_args();
        if ctor_args.len() > nparams as usize {
            result_args.extend_from_slice(&ctor_args[nparams as usize..]);
        }
        // Apply extra args after major
        if args.len() > major_idx + 1 {
            result_args.extend_from_slice(&args[major_idx + 1..]);
        }
        rhs = Expr::mk_app_n(&rhs, &result_args);
        Some(rhs)
    }

    // ========================================================================
    // Stage 09: Quotient reduction
    // ========================================================================

    fn reduce_quot(&mut self, e: &Expr) -> Option<Expr> {
        let fn_e = e.get_app_fn();
        if !fn_e.is_const() { return None; }
        let name = fn_e.const_name();
        let info = self.env.find(name)?;
        match &info.kind {
            ConstantInfoKind::Quot { kind: QuotKind::Lift } => {
                // Quot.lift : ... (Quot.mk r a) → f a
                let args = e.get_app_args();
                if args.len() < 6 { return None; }
                let mk_arg = self.whnf(&args[5]);
                let mk_fn = mk_arg.get_app_fn();
                if !mk_fn.is_const() { return None; }
                let mk_info = self.env.find(mk_fn.const_name())?;
                if !matches!(&mk_info.kind, ConstantInfoKind::Quot { kind: QuotKind::Mk }) {
                    return None;
                }
                let mk_args = mk_arg.get_app_args();
                if mk_args.len() < 4 { return None; }
                let a = &mk_args[3]; // the element
                let f = &args[3];    // the lifted function
                let mut result = Expr::mk_app(f, a);
                // Apply remaining args
                for arg in &args[6..] {
                    result = Expr::mk_app(&result, arg);
                }
                Some(result)
            }
            ConstantInfoKind::Quot { kind: QuotKind::Ind } => {
                let args = e.get_app_args();
                if args.len() < 5 { return None; }
                let mk_arg = self.whnf(&args[4]);
                let mk_fn = mk_arg.get_app_fn();
                if !mk_fn.is_const() { return None; }
                let mk_info = self.env.find(mk_fn.const_name())?;
                if !matches!(&mk_info.kind, ConstantInfoKind::Quot { kind: QuotKind::Mk }) {
                    return None;
                }
                let mk_args = mk_arg.get_app_args();
                if mk_args.len() < 4 { return None; }
                let a = &mk_args[3];
                let h = &args[3];
                let mut result = Expr::mk_app(h, a);
                for arg in &args[5..] {
                    result = Expr::mk_app(&result, arg);
                }
                Some(result)
            }
            _ => None,
        }
    }

    // ========================================================================
    // Stage 10: Declaration checking
    // ========================================================================

    /// Check and add a declaration to the environment.
    pub fn add_decl(&mut self, decl: &Declaration) -> Result<Environment, EnvError> {
        match decl {
            Declaration::Axiom { name, lparams, type_, is_unsafe } => {
                self.env.check_name(name)?;
                Environment::check_no_dup_lparams(lparams)?;
                self.check_no_mvar_or_fvar(type_)?;
                if !self.env.is_believer() {
                    // Type-check the type
                    let _ = self.infer_type(type_);
                }
                self.env.add_constant_info(ConstantInfo {
                    name: name.clone(),
                    lparams: lparams.clone(),
                    type_: type_.clone(),
                    kind: ConstantInfoKind::Axiom { is_unsafe: *is_unsafe },
                })
            }
            Declaration::Definition { name, lparams, type_, value, hints, safety } => {
                self.env.check_name(name)?;
                Environment::check_no_dup_lparams(lparams)?;
                self.check_no_mvar_or_fvar(type_)?;
                self.check_no_mvar_or_fvar(value)?;
                if !self.env.is_believer() {
                    let _ = self.infer_type(type_);
                    let val_type = self.infer_type(value);
                    if !self.is_def_eq(&val_type, type_) {
                        return Err(EnvError(format!(
                            "type mismatch for definition '{}': value type does not match declared type", name
                        )));
                    }
                }
                self.env.add_constant_info(ConstantInfo {
                    name: name.clone(),
                    lparams: lparams.clone(),
                    type_: type_.clone(),
                    kind: ConstantInfoKind::Definition {
                        value: value.clone(),
                        hints: hints.clone(),
                        safety: *safety,
                    },
                })
            }
            Declaration::Theorem { name, lparams, type_, value } => {
                self.env.check_name(name)?;
                Environment::check_no_dup_lparams(lparams)?;
                self.check_no_mvar_or_fvar(type_)?;
                self.check_no_mvar_or_fvar(value)?;
                if !self.env.is_believer() {
                    let _ = self.infer_type(type_);
                    let val_type = self.infer_type(value);
                    if !self.is_def_eq(&val_type, type_) {
                        return Err(EnvError(format!(
                            "type mismatch for theorem '{}'", name
                        )));
                    }
                }
                self.env.add_constant_info(ConstantInfo {
                    name: name.clone(),
                    lparams: lparams.clone(),
                    type_: type_.clone(),
                    kind: ConstantInfoKind::Theorem { value: value.clone() },
                })
            }
            Declaration::Opaque { name, lparams, type_, value, is_unsafe } => {
                self.env.check_name(name)?;
                Environment::check_no_dup_lparams(lparams)?;
                self.check_no_mvar_or_fvar(type_)?;
                self.check_no_mvar_or_fvar(value)?;
                if !self.env.is_believer() {
                    let _ = self.infer_type(type_);
                    let val_type = self.infer_type(value);
                    if !self.is_def_eq(&val_type, type_) {
                        return Err(EnvError(format!(
                            "type mismatch for opaque '{}'", name
                        )));
                    }
                }
                self.env.add_constant_info(ConstantInfo {
                    name: name.clone(),
                    lparams: lparams.clone(),
                    type_: type_.clone(),
                    kind: ConstantInfoKind::Opaque { value: value.clone(), is_unsafe: *is_unsafe },
                })
            }
            Declaration::Mutual { .. } | Declaration::Inductive { .. } => {
                Err(EnvError("mutual/inductive not yet implemented in add_decl".into()))
            }
        }
    }

    fn check_no_mvar_or_fvar(&self, e: &Expr) -> Result<(), EnvError> {
        if e.has_mvar() {
            return Err(EnvError("declaration contains metavariables".into()));
        }
        if e.has_fvar() {
            return Err(EnvError("declaration contains free variables".into()));
        }
        Ok(())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_env_with_nat() -> Environment {
        let env = Environment::new(0);
        let env = env.add_constant_info(ConstantInfo {
            name: Name::str("Nat"),
            lparams: vec![],
            type_: Expr::mk_sort(&Level::one()),
            kind: ConstantInfoKind::Inductive {
                nparams: 0, nindices: 0,
                all: vec![Name::str("Nat")],
                ctors: vec![Name::str("Nat.zero"), Name::str("Nat.succ")],
                nnested: 0, is_rec: true, is_unsafe: false, is_reflexive: false,
            },
        }).unwrap();
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let env = env.add_constant_info(ConstantInfo {
            name: Name::str("Nat.zero"),
            lparams: vec![],
            type_: nat.clone(),
            kind: ConstantInfoKind::Constructor {
                induct_name: Name::str("Nat"), cidx: 0, nparams: 0, nfields: 0, is_unsafe: false,
            },
        }).unwrap();
        let env = env.add_constant_info(ConstantInfo {
            name: Name::str("Nat.succ"),
            lparams: vec![],
            type_: Expr::mk_pi(&Name::str("n"), BinderInfo::Default, &nat, &nat),
            kind: ConstantInfoKind::Constructor {
                induct_name: Name::str("Nat"), cidx: 1, nparams: 0, nfields: 1, is_unsafe: false,
            },
        }).unwrap();
        env
    }

    fn nat() -> Expr { Expr::mk_const(&Name::str("Nat"), &[]) }
    fn zero() -> Expr { Expr::mk_const(&Name::str("Nat.zero"), &[]) }
    fn succ() -> Expr { Expr::mk_const(&Name::str("Nat.succ"), &[]) }

    // -- WHNF (Stage 05) ----------------------------------------------------

    #[test]
    fn test_whnf_beta() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        // (λx:Nat. x) zero → zero
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
        let app = Expr::mk_app(&lam, &zero());
        let r = tc.whnf(&app);
        assert_eq!(r, zero());
    }

    #[test]
    fn test_whnf_let() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        // let x := zero in succ x → succ zero
        let body = Expr::mk_app(&succ(), &Expr::mk_bvar(0));
        let e = Expr::mk_let(&Name::str("x"), &nat(), &zero(), &body, false);
        let r = tc.whnf(&e);
        // After let reduction: succ zero. succ is a constructor, so it's WHNF.
        assert!(r.is_app());
        assert_eq!(r.app_fn(), &succ());
        assert_eq!(r.app_arg(), &zero());
    }

    #[test]
    fn test_whnf_nested_beta() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        // (λx. λy. x) a b → a
        let a = Expr::mk_const(&Name::str("Nat.zero"), &[]);
        let inner = Expr::mk_lambda(&Name::str("y"), BinderInfo::Default, &nat(), &Expr::mk_bvar(1));
        let outer = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &inner);
        let app = Expr::mk_app_n(&outer, &[a.clone(), nat()]);
        let r = tc.whnf(&app);
        assert_eq!(r, a);
    }

    #[test]
    fn test_whnf_delta() {
        let env = mk_env_with_nat();
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
        let env = env.add_constant_info(ConstantInfo {
            name: Name::str("id"),
            lparams: vec![],
            type_: Expr::mk_pi(&Name::str("x"), BinderInfo::Default, &nat(), &nat()),
            kind: ConstantInfoKind::Definition {
                value: lam,
                hints: ReducibilityHints::Abbreviation,
                safety: DefinitionSafety::Safe,
            },
        }).unwrap();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        // id zero → zero
        let app = Expr::mk_app(&Expr::mk_const(&Name::str("id"), &[]), &zero());
        let r = tc.whnf(&app);
        assert_eq!(r, zero());
    }

    #[test]
    fn test_whnf_opaque_not_unfolded() {
        let env = mk_env_with_nat();
        let env = env.add_constant_info(ConstantInfo {
            name: Name::str("secret"),
            lparams: vec![],
            type_: nat(),
            kind: ConstantInfoKind::Definition {
                value: zero(),
                hints: ReducibilityHints::Opaque,
                safety: DefinitionSafety::Safe,
            },
        }).unwrap();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let e = Expr::mk_const(&Name::str("secret"), &[]);
        let r = tc.whnf(&e);
        assert!(r.is_const());
        assert_eq!(r.const_name(), &Name::str("secret"));
    }

    #[test]
    fn test_whnf_fvar_let_unfold() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let fvar = tc.lctx_mut().mk_let_decl(
            Name::str("x"), Name::str("x"), nat(), zero(),
        );
        let r = tc.whnf(&fvar);
        assert_eq!(r, zero());
    }

    // -- Type Inference (Stage 06) ------------------------------------------

    #[test]
    fn test_infer_const() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let ty = tc.infer_type(&zero());
        assert_eq!(ty, nat());
    }

    #[test]
    fn test_infer_app() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let e = Expr::mk_app(&succ(), &zero());
        let ty = tc.infer_type(&e);
        assert_eq!(ty, nat());
    }

    #[test]
    fn test_infer_sort() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let ty = tc.infer_type(&Expr::mk_prop());
        assert!(ty.is_sort());
        assert_eq!(ty.sort_level(), &Level::one());
    }

    #[test]
    fn test_infer_lambda() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        // λ (x : Nat). x  has type  Nat → Nat
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
        let ty = tc.infer_type(&lam);
        assert!(ty.is_pi());
    }

    #[test]
    fn test_infer_lit() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let ty = tc.infer_type(&Expr::mk_lit(Literal::Nat(42)));
        assert_eq!(ty, nat());
    }

    // -- Definitional Equality (Stage 07) -----------------------------------

    #[test]
    fn test_def_eq_reflexive() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        assert!(tc.is_def_eq(&zero(), &zero()));
    }

    #[test]
    fn test_def_eq_beta() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        // (λx. x) zero =?= zero
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
        let app = Expr::mk_app(&lam, &zero());
        assert!(tc.is_def_eq(&app, &zero()));
    }

    #[test]
    fn test_def_eq_delta() {
        let env = mk_env_with_nat();
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
        let env = env.add_constant_info(ConstantInfo {
            name: Name::str("myId"),
            lparams: vec![],
            type_: Expr::mk_pi(&Name::str("x"), BinderInfo::Default, &nat(), &nat()),
            kind: ConstantInfoKind::Definition {
                value: lam,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
            },
        }).unwrap();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        // myId zero =?= zero
        let app = Expr::mk_app(&Expr::mk_const(&Name::str("myId"), &[]), &zero());
        assert!(tc.is_def_eq(&app, &zero()));
    }

    #[test]
    fn test_def_eq_sort() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let s1 = Expr::mk_sort(&Level::mk_max_core(&u, &v));
        let s2 = Expr::mk_sort(&Level::mk_max_core(&v, &u));
        assert!(tc.is_def_eq(&s1, &s2));
    }

    #[test]
    fn test_def_eq_negative() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        assert!(!tc.is_def_eq(&zero(), &Expr::mk_app(&succ(), &zero())));
    }

    // -- Projection reduction -----------------------------------------------

    #[test]
    fn test_proj_reduction() {
        let env = mk_env_with_nat();
        // Add a simple Prod-like structure
        let env = env.add_constant_info(ConstantInfo {
            name: Name::str("MyPair"),
            lparams: vec![],
            type_: Expr::mk_type(),
            kind: ConstantInfoKind::Inductive {
                nparams: 0, nindices: 0,
                all: vec![Name::str("MyPair")],
                ctors: vec![Name::str("MyPair.mk")],
                nnested: 0, is_rec: false, is_unsafe: false, is_reflexive: false,
            },
        }).unwrap();
        let pair_ty = Expr::mk_const(&Name::str("MyPair"), &[]);
        let mk_ty = Expr::mk_pi(&Name::str("a"), BinderInfo::Default, &nat(),
            &Expr::mk_pi(&Name::str("b"), BinderInfo::Default, &nat(), &pair_ty));
        let env = env.add_constant_info(ConstantInfo {
            name: Name::str("MyPair.mk"),
            lparams: vec![],
            type_: mk_ty,
            kind: ConstantInfoKind::Constructor {
                induct_name: Name::str("MyPair"), cidx: 0, nparams: 0, nfields: 2, is_unsafe: false,
            },
        }).unwrap();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let mk = Expr::mk_const(&Name::str("MyPair.mk"), &[]);
        let pair = Expr::mk_app_n(&mk, &[zero(), Expr::mk_app(&succ(), &zero())]);
        let proj0 = Expr::mk_proj(&Name::str("MyPair"), 0, &pair);
        let r = tc.whnf(&proj0);
        assert_eq!(r, zero());
    }

    // -- Add declaration (Stage 10) -----------------------------------------

    #[test]
    fn test_add_axiom() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let new_env = tc.add_decl(&Declaration::Axiom {
            name: Name::str("myAxiom"),
            lparams: vec![],
            type_: nat(),
            is_unsafe: false,
        }).unwrap();
        assert!(new_env.find(&Name::str("myAxiom")).is_some());
    }

    #[test]
    fn test_add_duplicate_rejected() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let result = tc.add_decl(&Declaration::Axiom {
            name: Name::str("Nat"),
            lparams: vec![],
            type_: Expr::mk_type(),
            is_unsafe: false,
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_add_definition() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let new_env = tc.add_decl(&Declaration::Definition {
            name: Name::str("myZero"),
            lparams: vec![],
            type_: nat(),
            value: zero(),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
        }).unwrap();
        let info = new_env.find(&Name::str("myZero")).unwrap();
        assert!(info.is_definition());
    }

    #[test]
    fn test_add_mvar_rejected() {
        let env = mk_env_with_nat();
        let mut tc = TypeChecker::new(env, LocalContext::new());
        let result = tc.add_decl(&Declaration::Axiom {
            name: Name::str("bad"),
            lparams: vec![],
            type_: Expr::mk_mvar(&Name::str("m")),
            is_unsafe: false,
        });
        assert!(result.is_err());
    }

    // -- Equiv Manager ------------------------------------------------------

    #[test]
    fn test_equiv_manager() {
        let mut em = EquivManager::new();
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let c = Expr::mk_const(&Name::str("c"), &[]);
        assert!(!em.is_equiv(&a, &b));
        em.add_equiv(&a, &b);
        assert!(em.is_equiv(&a, &b));
        em.add_equiv(&b, &c);
        assert!(em.is_equiv(&a, &c));
    }
}
