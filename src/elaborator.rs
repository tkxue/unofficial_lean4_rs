//! Stage 35-36: Elaboration — Syntax → Expr.

use std::collections::HashMap;

use crate::debruijn::*;
use crate::env::*;
use crate::expr::*;
use crate::level::Level;
use crate::local_ctx::LocalContext;
use crate::name::Name;
use crate::resolve::*;
use crate::syntax::Syntax;
use crate::type_checker::TypeChecker;

// ============================================================================
// Metavariable context
// ============================================================================

pub struct MetavarContext {
    decls: HashMap<Name, MetavarDecl>,
    assignments: HashMap<Name, Expr>,
    next_id: u64,
}

pub struct MetavarDecl {
    pub type_: Expr,
    pub lctx: LocalContext,
}

impl MetavarContext {
    pub fn new() -> Self {
        MetavarContext { decls: HashMap::new(), assignments: HashMap::new(), next_id: 0 }
    }

    pub fn mk_fresh_mvar(&mut self, type_: Expr, lctx: &LocalContext) -> Expr {
        let id = self.next_id;
        self.next_id += 1;
        let name = Name::mk_numeral(&Name::mk_string(&Name::anonymous(), "_mvar"), id);
        self.decls.insert(name.clone(), MetavarDecl { type_, lctx: lctx.clone() });
        Expr::mk_mvar(&name)
    }

    pub fn assign(&mut self, name: &Name, value: Expr) {
        self.assignments.insert(name.clone(), value);
    }

    pub fn is_assigned(&self, name: &Name) -> bool {
        self.assignments.contains_key(name)
    }

    pub fn get_assignment(&self, name: &Name) -> Option<&Expr> {
        self.assignments.get(name)
    }

    pub fn get_type(&self, name: &Name) -> Option<&Expr> {
        self.decls.get(name).map(|d| &d.type_)
    }

    pub fn mk_fresh_mvar_named(&mut self, name: Name, type_: Expr, lctx: &LocalContext) -> Expr {
        self.decls.insert(name.clone(), MetavarDecl { type_, lctx: lctx.clone() });
        Expr::mk_mvar(&name)
    }

    pub fn next_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Replace all assigned mvars in an expression.
    pub fn instantiate_mvars(&self, e: &Expr) -> Expr {
        if !e.has_expr_mvar() { return e.clone(); }
        replace_no_offset(e, &mut |sub| {
            if !sub.has_expr_mvar() { return Some(sub.clone()); }
            if sub.is_mvar() {
                if let Some(val) = self.assignments.get(sub.mvar_name()) {
                    return Some(self.instantiate_mvars(val));
                }
            }
            None
        })
    }

    pub fn has_unsolved(&self) -> bool {
        self.decls.keys().any(|k| !self.assignments.contains_key(k))
    }
}

// ============================================================================
// Elaborator
// ============================================================================

pub struct Elaborator {
    pub env: Environment,
    pub tc: TypeChecker,
    pub mctx: MetavarContext,
    pub lctx: LocalContext,
    pub res: ResCtx,
    name_counter: u64,
}

#[derive(Debug)]
pub struct ElabError(pub String);

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Elaborator {
    pub fn new(env: Environment) -> Self {
        let lctx = LocalContext::new();
        let tc = TypeChecker::new(env.clone(), lctx.clone());
        Elaborator {
            env,
            tc,
            mctx: MetavarContext::new(),
            lctx,
            res: ResCtx::new(),
            name_counter: 0,
        }
    }

    /// Reset for a new file, keeping the base environment and TC caches.
    pub fn reset_for_file(&mut self, base_env: &Environment) {
        self.env = base_env.clone();
        self.lctx = LocalContext::new();
        self.mctx = MetavarContext::new();
        self.res = ResCtx::new();
        // Keep tc caches — they're still valid for the same env
        self.tc = TypeChecker::new(self.env.clone(), self.lctx.clone());
    }

    /// Sync TC's local context with elaborator's before any TC call.
    pub fn sync_tc(&mut self) {
        *self.tc.lctx_mut() = self.lctx.clone();
    }

    fn fresh_name(&mut self, prefix: &str) -> Name {
        let n = self.name_counter;
        self.name_counter += 1;
        Name::mk_numeral(&Name::mk_string(&Name::anonymous(), prefix), n)
    }

    // ========================================================================
    // Term elaboration
    // ========================================================================

    pub fn elab_term(&mut self, stx: &Syntax, expected: Option<&Expr>) -> Result<Expr, ElabError> {
        self.sync_tc();
        match stx {
            Syntax::Missing => Ok(self.mctx.mk_fresh_mvar(
                expected.cloned().unwrap_or_else(Expr::mk_type), &self.lctx)),
            Syntax::Ident { val, .. } => self.elab_ident(val, expected),
            Syntax::Atom { val, .. } => self.elab_atom(val),
            Syntax::Node { kind, args, .. } => self.elab_node(kind, args, expected),
        }
    }

    fn elab_ident(&mut self, name: &Name, _expected: Option<&Expr>) -> Result<Expr, ElabError> {
        // Check local
        for local in self.lctx_locals() {
            if &local == name {
                return Ok(Expr::mk_fvar(name));
            }
        }
        // Built-in aliases
        let s = name.to_string();
        let aliased = match s.as_str() {
            "true" => Some("Bool.true"),
            "false" => Some("Bool.false"),
            "none" => Some("Option.none"),
            "some" => Some("Option.some"),
            "nil" => Some("List.nil"),
            "cons" => Some("List.cons"),
            "not" => Some("Bool.not"),
            "and" => Some("Bool.and"),
            "or" => Some("Bool.or"),
            "rfl" => Some("Eq.refl"),
            "pure" => Some("Pure.pure"),
            "bind" => Some("Bind.bind"),
            _ => None,
        };
        if let Some(alias) = aliased {
            let alias_name = Name::str(alias);
            if let Some(info) = self.env.find(&alias_name) {
                let levels: Vec<Level> = info.lparams.iter()
                    .map(|_| Level::mk_param(&self.fresh_name("_u")))
                    .collect();
                return Ok(Expr::mk_const(&alias_name, &levels));
            }
        }
        // Resolve against environment
        match resolve_name(name, &self.res, &self.env) {
            Ok(resolved) => {
                let info = self.env.get(&resolved);
                let levels: Vec<Level> = info.lparams.iter()
                    .map(|_| Level::mk_param(&self.fresh_name("_u")))
                    .collect();
                Ok(Expr::mk_const(&resolved, &levels))
            }
            Err(_) => Err(ElabError(format!("unknown identifier '{}'", name))),
        }
    }

    fn lctx_locals(&self) -> Vec<Name> {
        self.res.locals.clone()
    }

    fn elab_atom(&mut self, val: &str) -> Result<Expr, ElabError> {
        // Numeric literal
        if let Ok(n) = val.parse::<u64>() {
            return Ok(Expr::mk_lit(Literal::Nat(n)));
        }
        // String literal
        if val.starts_with('"') {
            return Ok(Expr::mk_lit(Literal::Str(val[1..val.len()-1].to_string())));
        }
        Err(ElabError(format!("unexpected atom '{}'", val)))
    }

    fn elab_node(&mut self, kind: &Name, args: &[Syntax], expected: Option<&Expr>) -> Result<Expr, ElabError> {
        let k = kind.to_string();
        match k.as_str() {
            "Term.num" => {
                let val = args[0].as_atom().unwrap_or("0");
                let n: u64 = val.parse().unwrap_or(0);
                Ok(Expr::mk_lit(Literal::Nat(n)))
            }
            "Term.str" => {
                let val = args[0].as_atom().unwrap_or("");
                Ok(Expr::mk_lit(Literal::Str(val.to_string())))
            }
            "Term.ident" => {
                let name = args[0].as_ident()
                    .ok_or_else(|| ElabError("expected ident".into()))?;
                self.elab_ident(name, expected)
            }
            "Term.app" => {
                let f = self.elab_term(&args[0], None)?;
                let f = self.insert_implicits(f)?;
                let a = self.elab_term(&args[1], None)?;
                Ok(Expr::mk_app(&f, &a))
            }
            "Term.binop" => {
                // args[0] = operator atom, args[1] = lhs, args[2] = rhs
                let op = args[0].as_atom().unwrap_or("+");
                let lhs = self.elab_term(&args[1], None)?;
                let rhs = self.elab_term(&args[2], None)?;
                self.elab_binop(op, &lhs, &rhs)
            }
            "Term.fun" => {
                let n = args.len();
                if n < 2 { return Err(ElabError("fun needs binder + body".into())); }
                let body_stx = &args[n - 1];
                let mut fvars = Vec::new();
                for binder in &args[..n-1] {
                    let (binder_name, binder_type, bi) = self.extract_binder(binder)?;
                    let fvar = self.lctx.mk_local_decl(
                        binder_name.clone(), binder_name.clone(), binder_type, bi,
                    );
                    self.res.push_local(binder_name);
                    fvars.push(fvar);
                }
                let body = self.elab_term(body_stx, None)?;
                for _ in &fvars { self.res.pop_local(); }
                Ok(self.lctx.mk_lambda(&fvars, &body))
            }
            "Term.forall" => {
                let n = args.len();
                if n < 2 { return Err(ElabError("forall needs binder + body".into())); }
                let body_stx = &args[n - 1];
                let mut fvars = Vec::new();
                for binder in &args[..n-1] {
                    for (bname, btype, bi) in self.extract_binders(binder)? {
                        let fvar = self.lctx.mk_local_decl(
                            bname.clone(), bname.clone(), btype, bi,
                        );
                        self.res.push_local(bname);
                        fvars.push(fvar);
                    }
                }
                let body = self.elab_term(body_stx, None)?;
                for _ in &fvars { self.res.pop_local(); }
                Ok(self.lctx.mk_pi(&fvars, &body))
            }
            "Term.paren" => self.elab_term(&args[0], expected),
            "Term.explicit" => {
                // @f — elaborate without implicit insertion
                self.elab_term(&args[0], expected)
            }
            "Term.not" => {
                let e = self.elab_term(&args[0], None)?;
                let not = Expr::mk_const(&Name::str("Not"), &[]);
                Ok(Expr::mk_app(&not, &e))
            }
            "Term.bnot" => {
                let e = self.elab_term(&args[0], None)?;
                let bnot = Expr::mk_const(&Name::str("not"), &[]);
                Ok(Expr::mk_app(&bnot, &e))
            }
            "Term.proj" => {
                let obj = self.elab_term(&args[0], None)?;
                let field = args[1].as_ident()
                    .ok_or_else(|| ElabError("proj field must be ident".into()))?;
                // Simplified: try TypeName.fieldName
                let obj_type = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    self.tc.infer_type(&obj)
                })) {
                    Ok(ty) => ty,
                    Err(_) => return Ok(obj),
                };
                let type_name = obj_type.get_app_fn();
                if type_name.is_const() {
                    let proj_name = type_name.const_name().append(field);
                    if self.env.find(&proj_name).is_some() {
                        let info = self.env.get(&proj_name);
                        let levels: Vec<Level> = info.lparams.iter()
                            .map(|_| Level::mk_param(&self.fresh_name("_u")))
                            .collect();
                        let proj = Expr::mk_const(&proj_name, &levels);
                        return Ok(Expr::mk_app(&proj, &obj));
                    }
                }
                Ok(obj)
            }
            "Term.anonymousCtor" => {
                // ⟨a, b⟩ — needs expected type to resolve constructor
                // Simplified: treat as Prod.mk if 2 args
                if args.len() == 2 {
                    let a = self.elab_term(&args[0], None)?;
                    let b = self.elab_term(&args[1], None)?;
                    let mk = Expr::mk_const(&Name::str("Prod.mk"), &[
                        Level::mk_param(&self.fresh_name("_u")),
                        Level::mk_param(&self.fresh_name("_v")),
                    ]);
                    let ta = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                    let tb = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                    Ok(Expr::mk_app_n(&mk, &[ta, tb, a, b]))
                } else {
                    // Generic: create mvar
                    let ty = expected.cloned().unwrap_or_else(Expr::mk_type);
                    Ok(self.mctx.mk_fresh_mvar(ty, &self.lctx))
                }
            }
            "Term.hole" => {
                let ty = expected.cloned().unwrap_or_else(Expr::mk_type);
                Ok(self.mctx.mk_fresh_mvar(ty, &self.lctx))
            }
            "Term.type" => Ok(Expr::mk_type()),
            "Term.prop" => Ok(Expr::mk_prop()),
            "Term.tuple" => {
                // (a, b) → Prod.mk a b (simplified, no nested tuples)
                let a = self.elab_term(&args[0], None)?;
                let b = self.elab_term(&args[1], None)?;
                let mk = Expr::mk_const(&Name::str("Prod.mk"), &[
                    Level::mk_param(&self.fresh_name("_u")),
                    Level::mk_param(&self.fresh_name("_v")),
                ]);
                let ta = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                let tb = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                Ok(Expr::mk_app_n(&mk, &[ta, tb, a, b]))
            }
            "Term.if" => {
                // Desugar: if c then t else f → ite c t f
                let c = self.elab_term(&args[0], None)?;
                let t = self.elab_term(&args[1], expected)?;
                let f = self.elab_term(&args[2], expected)?;
                let ite = Expr::mk_const(&Name::str("ite"), &[]);
                // ite {α} (c : Prop) [Decidable c] (t f : α) : α
                let ty_mvar = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                let dec_mvar = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                Ok(Expr::mk_app_n(&ite, &[ty_mvar, c, dec_mvar, t, f]))
            }
            "Term.let" => {
                // args: name, (type?), value, body
                let name = args[0].as_ident()
                    .cloned()
                    .unwrap_or_else(|| self.fresh_name("_let"));
                let (ty, val_idx) = if args.len() == 4 {
                    (self.elab_term(&args[1], None)?, 2)
                } else {
                    (self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx), 1)
                };
                let value = self.elab_term(&args[val_idx], Some(&ty))?;
                let fvar = self.lctx.mk_let_decl(
                    name.clone(), name.clone(), ty.clone(), value.clone(),
                );
                self.res.push_local(name);
                let body = self.elab_term(&args[val_idx + 1], expected)?;
                self.res.pop_local();
                Ok(Expr::mk_let(
                    &args[0].as_ident().cloned().unwrap_or_else(|| Name::str("_")),
                    &ty, &value,
                    &abstract1(&body, &fvar), false,
                ))
            }
            "Term.typeAscription" => {
                let ty = self.elab_term(&args[1], None)?;
                self.elab_term(&args[0], Some(&ty))
            }
            "Term.sort" => {
                if args.is_empty() {
                    // Bare `Sort` → Sort with fresh universe
                    Ok(Expr::mk_sort(&Level::mk_param(&self.fresh_name("_u"))))
                } else {
                    // Sort u
                    Ok(Expr::mk_sort(&Level::mk_param(&self.fresh_name("_u"))))
                }
            }
            "Term.do" => {
                // Simplified: desugar last statement as return value
                if args.is_empty() {
                    let ty = expected.cloned().unwrap_or_else(Expr::mk_type);
                    return Ok(self.mctx.mk_fresh_mvar(ty, &self.lctx));
                }
                // For now, just elaborate the last statement
                self.elab_term(args.last().unwrap(), expected)
            }
            "Term.return" => {
                // return e → Pure.pure e
                if args.is_empty() {
                    return Ok(Expr::mk_const(&Name::str("Pure.pure"), &[]));
                }
                let e = self.elab_term(&args[0], None)?;
                let pure = Expr::mk_const(&Name::str("Pure.pure"), &[Level::mk_param(&self.fresh_name("_u"))]);
                let ty_mvar = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                let inst_mvar = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                Ok(Expr::mk_app_n(&pure, &[ty_mvar, inst_mvar, e]))
            }
            "Term.calc" => {
                // Simplified: elaborate first step as the result
                if args.is_empty() {
                    return Err(ElabError("calc needs at least one step".into()));
                }
                self.elab_term(&args[0], expected)
            }
            "Term.by" => {
                let ty = expected.cloned().unwrap_or_else(Expr::mk_prop);
                match crate::tactic::eval_by(self, args, &ty) {
                    Ok(proof) => Ok(proof),
                    Err(_) => {
                        // Fallback: create unsolved mvar
                        Ok(self.mctx.mk_fresh_mvar(ty, &self.lctx))
                    }
                }
            }
            "Term.subtype" => {
                // { x : T // P x } → Subtype (fun x : T => P x)
                let name = args[0].as_ident().cloned().unwrap_or_else(|| self.fresh_name("_x"));
                let ty = if args.len() > 1 && !args[1].is_missing() {
                    self.elab_term(&args[1], None)?
                } else {
                    self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx)
                };
                let fvar = self.lctx.mk_local_decl(name.clone(), name.clone(), ty.clone(), BinderInfo::Default);
                self.res.push_local(name.clone());
                let pred = if args.len() > 2 {
                    self.elab_term(&args[2], None)?
                } else {
                    Expr::mk_prop()
                };
                self.res.pop_local();
                let lambda = self.lctx.mk_lambda(&[fvar], &pred);
                let subtype = Expr::mk_const(&Name::str("Subtype"), &[Level::mk_param(&self.fresh_name("_u"))]);
                Ok(Expr::mk_app(&subtype, &lambda))
            }
            "Term.set" => {
                // Simplified: just create a type mvar
                Ok(self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx))
            }
            "Term.list" => {
                let u = Level::mk_param(&self.fresh_name("_u"));
                let nil = Expr::mk_const(&Name::str("List.nil"), &[u.clone()]);
                let cons_name = Name::str("List.cons");
                let mut result = nil;
                for elem in args.iter().rev() {
                    let e = self.elab_term(elem, None)?;
                    let cons = Expr::mk_const(&cons_name, &[u.clone()]);
                    let ty_mvar = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                    result = Expr::mk_app_n(&cons, &[ty_mvar, e, result]);
                }
                Ok(result)
            }
            "Term.exists" => {
                let n = args.len();
                if n < 2 { return Err(ElabError("exists needs binder + body".into())); }
                let body_stx = &args[n - 1];
                let mut fvars = Vec::new();
                for binder in &args[..n-1] {
                    for (bname, btype, bi) in self.extract_binders(binder)? {
                        let fvar = self.lctx.mk_local_decl(bname.clone(), bname.clone(), btype, bi);
                        self.res.push_local(bname);
                        fvars.push(fvar);
                    }
                }
                let body = self.elab_term(body_stx, None)?;
                for _ in &fvars { self.res.pop_local(); }
                let pred = self.lctx.mk_lambda(&fvars, &body);
                let exists = Expr::mk_const(&Name::str("Exists"), &[Level::mk_param(&self.fresh_name("_u"))]);
                Ok(Expr::mk_app(&exists, &pred))
            }
            "Term.show" => {
                // show T from e → elaborate e with expected type T
                if args.len() >= 2 {
                    let ty = self.elab_term(&args[0], None)?;
                    self.elab_term(&args[1], Some(&ty))
                } else {
                    self.elab_term(&args[0], expected)
                }
            }
            "Term.match" => {
                // args[0] = scrutinee, args[1..] = matchArm(pattern, body)
                if args.is_empty() { return Err(ElabError("match needs scrutinee".into())); }
                let scrutinee = self.elab_term(&args[0], None)?;
                let scrut_type = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    self.tc.infer_type(&scrutinee)
                })) {
                    Ok(ty) => self.tc.whnf(&ty),
                    Err(_) => return Err(ElabError("can't infer scrutinee type".into())),
                };
                // Look up inductive type
                let head = scrut_type.get_app_fn();
                if !head.is_const() {
                    return Err(ElabError(format!("match scrutinee type not inductive: {}", scrut_type)));
                }
                let ind_info = self.env.find(head.const_name())
                    .ok_or_else(|| ElabError(format!("unknown type: {}", head.const_name())))?;
                let ctors = match &ind_info.kind {
                    ConstantInfoKind::Inductive { ctors, .. } => ctors.clone(),
                    _ => return Err(ElabError("match on non-inductive".into())),
                };
                // For each constructor, find matching arm and elaborate body
                // Build casesOn: T.casesOn (motive) scrutinee minor1 minor2 ...
                let cases_on_name = Name::mk_string(head.const_name(), "casesOn");
                let ret_type = expected.cloned().unwrap_or_else(|| {
                    self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx)
                });
                // Build motive: fun _ => ret_type
                let motive = Expr::mk_lambda(
                    &self.fresh_name("_x"), BinderInfo::Default, &scrut_type, &ret_type,
                );
                let mut result_args = vec![];
                // casesOn takes: (params), motive, scrutinee, minors...
                // For now: skip params, just pass motive + scrutinee + arm bodies
                result_args.push(motive);
                result_args.push(scrutinee);
                // Elaborate each arm body
                for arm in &args[1..] {
                    if arm.is_node("matchArm") && arm.num_args() >= 2 {
                        let body = self.elab_term(arm.arg(arm.num_args() - 1), Some(&ret_type))?;
                        result_args.push(body);
                    }
                }
                // Build casesOn application
                if let Some(cases_info) = self.env.find(&cases_on_name) {
                    let levels: Vec<Level> = cases_info.lparams.iter()
                        .map(|_| Level::mk_param(&self.fresh_name("_u")))
                        .collect();
                    let cases_on = Expr::mk_const(&cases_on_name, &levels);
                    Ok(Expr::mk_app_n(&cases_on, &result_args))
                } else {
                    // Fallback: return scrutinee (can't compile match)
                    Err(ElabError(format!("casesOn not found for {}", head.const_name())))
                }
            }
            _ => Err(ElabError(format!("unsupported syntax kind: {}", k))),
        }
    }

    fn elab_binop(&mut self, op: &str, lhs: &Expr, rhs: &Expr) -> Result<Expr, ElabError> {
        // Map operators to kernel constants
        let const_name = match op {
            "+" => "HAdd.hAdd",
            "-" => "HSub.hSub",
            "*" => "HMul.hMul",
            "/" => "HDiv.hDiv",
            "%" => "HMod.hMod",
            "^" => "HPow.hPow",
            "++" => "HAppend.hAppend",
            "=" | "==" => "BEq.beq",
            "!=" | "≠" => "bne",
            "<" => "LT.lt",
            ">" => "GT.gt",
            "≤" | "<=" => "LE.le",
            "≥" | ">=" => "GE.ge",
            "∧" | "&&" => "And",
            "∨" | "||" => "Or",
            "→" | "->" => return Ok(Expr::mk_pi(
                &self.fresh_name("_a"), BinderInfo::Default, lhs, rhs)),
            "×" => "Prod",
            "::" => "List.cons",
            _ => return Err(ElabError(format!("unknown operator '{}'", op))),
        };

        // For → we already handled it above
        // For others: build application with implicit type args
        let f = match resolve_name(&Name::str(const_name), &self.res, &self.env) {
            Ok(resolved) => {
                let info = self.env.get(&resolved);
                let levels: Vec<Level> = info.lparams.iter()
                    .map(|_| Level::mk_param(&self.fresh_name("_u")))
                    .collect();
                Expr::mk_const(&resolved, &levels)
            }
            Err(_) => {
                // Fallback: just create the const without resolution
                Expr::mk_const(&Name::str(const_name), &[])
            }
        };
        let f = self.insert_implicits(f)?;
        Ok(Expr::mk_app(&Expr::mk_app(&f, lhs), rhs))
    }

    /// Extract multiple (name, type, bi) from a binder group like (a b c : Nat).
    fn extract_binders(&mut self, binder: &Syntax) -> Result<Vec<(Name, Expr, BinderInfo)>, ElabError> {
        if let Some(name) = binder.as_ident() {
            let ty = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
            return Ok(vec![(name.clone(), ty, BinderInfo::Default)]);
        }
        if let Some(kind) = binder.kind_name() {
            let k = kind.to_string();
            let bi = match k.as_str() {
                "Binder.implicit" => BinderInfo::Implicit,
                "Binder.inst" => BinderInfo::InstImplicit,
                "Binder.strict" => BinderInfo::StrictImplicit,
                _ => BinderInfo::Default,
            };
            let binder_args = binder.args();
            if binder_args.is_empty() {
                let name = self.fresh_name("_x");
                let ty = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                return Ok(vec![(name, ty, bi)]);
            }
            let type_stx = binder_args.last().unwrap();
            let ty = if type_stx.is_missing() {
                self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx)
            } else {
                self.elab_term(type_stx, None)?
            };
            // All args except the last are names
            let mut result = Vec::new();
            for name_stx in &binder_args[..binder_args.len()-1] {
                let name = name_stx.as_ident().cloned().unwrap_or_else(|| self.fresh_name("_x"));
                result.push((name, ty.clone(), bi));
            }
            if result.is_empty() {
                result.push((self.fresh_name("_x"), ty, bi));
            }
            return Ok(result);
        }
        let (n, t, b) = self.extract_binder(binder)?;
        Ok(vec![(n, t, b)])
    }

    /// Extract name, type, and binder info from a binder syntax node.
    fn extract_binder(&mut self, binder: &Syntax) -> Result<(Name, Expr, BinderInfo), ElabError> {
        // Simple ident: fun x => ...
        if let Some(name) = binder.as_ident() {
            let ty = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
            return Ok((name.clone(), ty, BinderInfo::Default));
        }
        // Binder node: (x : T), {x : T}, [inst : C], ⦃x : T⦄
        if let Some(kind) = binder.kind_name() {
            let k = kind.to_string();
            let bi = match k.as_str() {
                "Binder.implicit" => BinderInfo::Implicit,
                "Binder.inst" => BinderInfo::InstImplicit,
                "Binder.strict" => BinderInfo::StrictImplicit,
                _ => BinderInfo::Default,
            };
            let binder_args = binder.args();
            // Last arg is the type (or Missing), earlier args are names
            if binder_args.is_empty() {
                let name = self.fresh_name("_x");
                let ty = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
                return Ok((name, ty, bi));
            }
            let type_stx = binder_args.last().unwrap();
            let ty = if type_stx.is_missing() {
                self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx)
            } else {
                self.elab_term(type_stx, None)?
            };
            // First name (simplified: only handle one name per binder group)
            let name = if binder_args.len() > 1 {
                binder_args[0].as_ident().cloned().unwrap_or_else(|| self.fresh_name("_x"))
            } else {
                self.fresh_name("_x")
            };
            return Ok((name, ty, bi));
        }
        // Fallback
        let name = self.fresh_name("_x");
        let ty = self.mctx.mk_fresh_mvar(Expr::mk_type(), &self.lctx);
        Ok((name, ty, BinderInfo::Default))
    }

    /// Insert metavariables for implicit arguments.
    pub fn insert_implicits(&mut self, e: Expr) -> Result<Expr, ElabError> {
        self.sync_tc();
        // Simplified: look at the type, insert mvars for implicit/inst-implicit args
        let ty = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.tc.infer_type(&e)
        })) {
            Ok(ty) => ty,
            Err(_) => return Ok(e), // can't infer type, return as-is
        };

        let mut result = e;
        let mut cur_ty = ty;
        loop {
            let whnf_ty = self.tc.whnf(&cur_ty);
            if !whnf_ty.is_pi() { break; }
            match whnf_ty.binding_info() {
                BinderInfo::Implicit | BinderInfo::InstImplicit | BinderInfo::StrictImplicit => {
                    let mvar = self.mctx.mk_fresh_mvar(
                        whnf_ty.binding_domain().clone(), &self.lctx);
                    result = Expr::mk_app(&result, &mvar);
                    cur_ty = instantiate1(whnf_ty.binding_body(), &mvar);
                }
                _ => break,
            }
        }
        Ok(result)
    }

    // ========================================================================
    // Command elaboration
    // ========================================================================

    pub fn elab_command(&mut self, cmd: &Syntax) -> Result<(), ElabError> {
        let kind = match cmd.kind_name() {
            Some(k) => k.to_string(),
            None => return Ok(()),
        };
        match kind.as_str() {
            "Command.def" | "Command.abbrev" => self.elab_def(cmd, &kind),
            "Command.theorem" => self.elab_theorem(cmd),
            "Command.axiom" => self.elab_axiom(cmd),
            "Command.namespace" => {
                if let Some(name) = cmd.arg(0).as_ident() {
                    self.res.push_ns(name.clone());
                }
                Ok(())
            }
            "Command.open" => {
                if let Some(name) = cmd.arg(0).as_ident() {
                    self.res.open_scope(name.clone());
                }
                Ok(())
            }
            "Command.end" => { self.res.pop_ns(); Ok(()) }
            "Command.variable" | "Command.universe" | "Command.section"
            | "Command.set_option" | "Command.attribute"
            | "Command.instance" => Ok(()), // stub
            "Command.mutual" => {
                // Elaborate each def/theorem in the mutual block
                for sub_cmd in cmd.args() {
                    let _ = self.elab_command(sub_cmd);
                }
                Ok(())
            }
            "Command.inductive" | "Command.structure" => self.elab_inductive(cmd),
            _ if kind.starts_with("#") => Ok(()), // #check, #eval, etc.
            _ => Ok(()),
        }
    }

    fn elab_def(&mut self, cmd: &Syntax, kind: &str) -> Result<(), ElabError> {
        let args = cmd.args();
        if args.is_empty() { return Err(ElabError("def needs a name".into())); }
        let name = args[0].as_ident()
            .ok_or_else(|| ElabError("def name must be identifier".into()))?;
        let full_name = if self.res.current_ns.is_anonymous() {
            name.clone()
        } else {
            self.res.current_ns.append(name)
        };

        // Separate binders from return type and value
        // Parser produces: [name, binder*, (retType?), value]
        // Binders have kind "Binder.*", value is last, retType if present is second-to-last term
        let mut binder_args = Vec::new();
        let mut value_stx = None;
        let mut ret_type_stx = None;

        for (i, arg) in args.iter().enumerate().skip(1) {
            if let Some(k) = arg.kind_name() {
                let ks = k.to_string();
                if ks.starts_with("Binder.") {
                    binder_args.push(arg);
                    continue;
                }
            }
            // Non-binder args: could be return type or value
            // The last arg is always the value
            // If there are 2+ non-binder args after binders, first is ret type
            if value_stx.is_some() {
                ret_type_stx = value_stx.take();
            }
            value_stx = Some(arg);
        }

        let value_stx = value_stx.ok_or_else(|| ElabError("def needs a value".into()))?;

        // Pre-register the def name so recursive references can resolve
        // Use a placeholder type (will be replaced)
        let placeholder_type = Expr::mk_type();
        let pre_ci = ConstantInfo {
            name: full_name.clone(),
            lparams: vec![],
            type_: placeholder_type.clone(),
            kind: ConstantInfoKind::Axiom { is_unsafe: false },
        };
        if let Ok(new_env) = self.env.add_constant_info(pre_ci) {
            self.env = new_env;
            self.tc = TypeChecker::new(self.env.clone(), self.lctx.clone());
        }

        // Create fvars for binders
        let mut fvars = Vec::new();
        for binder in &binder_args {
            for (bname, btype, bi) in self.extract_binders(binder)? {
                let fvar = self.lctx.mk_local_decl(
                    bname.clone(), bname.clone(), btype, bi,
                );
                self.res.push_local(bname);
                fvars.push(fvar);
            }
        }

        // Elaborate return type if present
        let expected = match ret_type_stx {
            Some(rt) => Some(self.elab_term(rt, None)?),
            None => None,
        };

        // Elaborate value with binders in scope
        let value_inner = self.elab_term(value_stx, expected.as_ref())?;

        // Pop locals
        for _ in &fvars { self.res.pop_local(); }

        // Abstract over binders → lambda
        let value = if fvars.is_empty() {
            self.mctx.instantiate_mvars(&value_inner)
        } else {
            let lam = self.lctx.mk_lambda(&fvars, &value_inner);
            self.mctx.instantiate_mvars(&lam)
        };

        // Compute type
        let type_ = if !fvars.is_empty() && expected.is_some() {
            // Build Pi type from binders + return type
            let ret = expected.unwrap();
            let pi = self.lctx.mk_pi(&fvars, &ret);
            self.mctx.instantiate_mvars(&pi)
        } else {
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.tc.infer_type(&value)
            })) {
                Ok(ty) => self.mctx.instantiate_mvars(&ty),
                Err(_) => Expr::mk_type(),
            }
        };

        let hints = if kind == "Command.abbrev" {
            ReducibilityHints::Abbreviation
        } else {
            ReducibilityHints::Regular(1)
        };

        let ci = ConstantInfo {
            name: full_name,
            lparams: vec![],
            type_,
            kind: ConstantInfoKind::Definition {
                value,
                hints,
                safety: DefinitionSafety::Safe,
            },
        };
        self.env = self.env.replace_constant_info(ci);
        self.tc = TypeChecker::new(self.env.clone(), self.lctx.clone());
        Ok(())
    }

    fn elab_theorem(&mut self, cmd: &Syntax) -> Result<(), ElabError> {
        let args = cmd.args();
        if args.len() < 3 { return Err(ElabError("theorem needs name, type, value".into())); }
        let name = args[0].as_ident()
            .ok_or_else(|| ElabError("theorem name must be identifier".into()))?;
        let full_name = if self.res.current_ns.is_anonymous() {
            name.clone()
        } else {
            self.res.current_ns.append(name)
        };

        // Separate binders from type and value (same logic as elab_def)
        let mut binder_args = Vec::new();
        let mut non_binder = Vec::new();
        for arg in args.iter().skip(1) {
            if let Some(k) = arg.kind_name() {
                if k.to_string().starts_with("Binder.") {
                    binder_args.push(arg);
                    continue;
                }
            }
            non_binder.push(arg);
        }
        // non_binder should have [type, value] at minimum
        let (type_stx, value_stx) = if non_binder.len() >= 2 {
            (non_binder[non_binder.len() - 2], non_binder[non_binder.len() - 1])
        } else if non_binder.len() == 1 {
            (non_binder[0], non_binder[0])
        } else {
            return Err(ElabError("theorem needs type and value".into()));
        };

        // Create fvars for binders
        let mut fvars = Vec::new();
        for binder in &binder_args {
            for (bname, btype, bi) in self.extract_binders(binder)? {
                let fvar = self.lctx.mk_local_decl(bname.clone(), bname.clone(), btype, bi);
                self.res.push_local(bname);
                fvars.push(fvar);
            }
        }

        let type_ = self.elab_term(type_stx, None)?;
        let value = self.elab_term(value_stx, Some(&type_))?;

        // Pop locals
        for _ in &fvars { self.res.pop_local(); }

        // Abstract over binders
        let (type_, value) = if fvars.is_empty() {
            (self.mctx.instantiate_mvars(&type_), self.mctx.instantiate_mvars(&value))
        } else {
            let pi = self.lctx.mk_pi(&fvars, &type_);
            let lam = self.lctx.mk_lambda(&fvars, &value);
            (self.mctx.instantiate_mvars(&pi), self.mctx.instantiate_mvars(&lam))
        };

        let ci = ConstantInfo {
            name: full_name,
            lparams: vec![],
            type_,
            kind: ConstantInfoKind::Theorem { value },
        };
        self.env = self.env.add_constant_info(ci)
            .map_err(|e| ElabError(format!("{}", e)))?;
        Ok(())
    }

    fn elab_axiom(&mut self, cmd: &Syntax) -> Result<(), ElabError> {
        let args = cmd.args();
        if args.is_empty() { return Err(ElabError("axiom needs a name".into())); }
        let name = args[0].as_ident()
            .ok_or_else(|| ElabError("axiom name must be identifier".into()))?;
        let full_name = if self.res.current_ns.is_anonymous() {
            name.clone()
        } else {
            self.res.current_ns.append(name)
        };
        let type_ = self.elab_term(args.last().unwrap(), None)?;
        let type_ = self.mctx.instantiate_mvars(&type_);

        let ci = ConstantInfo {
            name: full_name,
            lparams: vec![],
            type_,
            kind: ConstantInfoKind::Axiom { is_unsafe: false },
        };
        self.env = self.env.add_constant_info(ci)
            .map_err(|e| ElabError(format!("{}", e)))?;
        Ok(())
    }

    fn elab_inductive(&mut self, cmd: &Syntax) -> Result<(), ElabError> {
        let args = cmd.args();
        if args.is_empty() { return Err(ElabError("inductive/structure needs a name".into())); }
        let name = args[0].as_ident()
            .ok_or_else(|| ElabError("inductive name must be identifier".into()))?;
        let full_name = if self.res.current_ns.is_anonymous() {
            name.clone()
        } else {
            self.res.current_ns.append(name)
        };

        // Collect constructors (nodes with kind "ctor") and fields (kind "field")
        let mut ctor_names = Vec::new();
        let mut field_names = Vec::new();
        for arg in args.iter().skip(1) {
            if let Some(k) = arg.kind_name() {
                let ks = k.to_string();
                if ks == "ctor" {
                    if let Some(cn) = arg.args().first().and_then(|a| a.as_ident()) {
                        ctor_names.push(full_name.append(cn));
                    }
                } else if ks == "field" {
                    if let Some(fn_) = arg.args().first().and_then(|a| a.as_ident()) {
                        field_names.push(fn_.clone());
                    }
                }
            }
        }

        // For structures: create a single mk constructor from fields
        let is_structure = cmd.kind_name().map_or(false, |k| k.to_string().contains("structure"));
        if is_structure && ctor_names.is_empty() {
            let mk_name = Name::mk_string(&full_name, "mk");
            ctor_names.push(mk_name.clone());

            // Add field projections
            for (i, field) in field_names.iter().enumerate() {
                let proj_name = Name::mk_string(&full_name, &field.to_string());
                let proj_ci = ConstantInfo {
                    name: proj_name,
                    lparams: vec![],
                    type_: Expr::mk_type(), // simplified
                    kind: ConstantInfoKind::Definition {
                        value: Expr::mk_bvar(0), // placeholder
                        hints: ReducibilityHints::Abbreviation,
                        safety: DefinitionSafety::Safe,
                    },
                };
                let _ = self.env.add_constant_info(proj_ci);
            }
        }

        // Add the inductive type
        let ind_ci = ConstantInfo {
            name: full_name.clone(),
            lparams: vec![],
            type_: Expr::mk_type(), // simplified
            kind: ConstantInfoKind::Inductive {
                nparams: 0,
                nindices: 0,
                all: vec![full_name.clone()],
                ctors: ctor_names.clone(),
                nnested: 0,
                is_rec: false,
                is_unsafe: false,
                is_reflexive: false,
            },
        };
        self.env = self.env.add_constant_info(ind_ci)
            .map_err(|e| ElabError(format!("{}", e)))?;

        // Add constructors
        for (i, ctor_name) in ctor_names.iter().enumerate() {
            let ctor_ci = ConstantInfo {
                name: ctor_name.clone(),
                lparams: vec![],
                type_: Expr::mk_const(&full_name, &[]), // simplified: ctor : T
                kind: ConstantInfoKind::Constructor {
                    induct_name: full_name.clone(),
                    cidx: i as u32,
                    nparams: 0,
                    nfields: 0,
                    is_unsafe: false,
                },
            };
            self.env = self.env.add_constant_info(ctor_ci)
                .map_err(|e| ElabError(format!("{}", e)))?;
        }

        Ok(())
    }
}

// ============================================================================
// Top-level: interpret a .lean file
// ============================================================================

use crate::parser::parse_file;
use crate::olean_fast::load_module_tree_fast;
use std::path::PathBuf;

pub fn interpret_lean_file(
    src: &str,
    search_paths: &[PathBuf],
) -> Result<Environment, ElabError> {
    let (is_prelude, imports, commands) = parse_file(src);

    // Load dependencies — use the fast tree loader
    let env = if imports.is_empty() {
        Environment::new(0)
    } else {
        // Load the first import as a tree (it pulls in transitive deps)
        // For multiple imports, load each tree and the last one wins
        let mut env = Environment::new(0);
        for imp in &imports {
            match load_module_tree_fast(imp, search_paths) {
                Ok(loaded) => { env = loaded.env; }
                Err(e) => return Err(ElabError(format!("import {}: {}", imp, e))),
            }
        }
        env
    };

    let mut elab = Elaborator::new(env);

    for cmd in &commands {
        if let Err(e) = elab.elab_command(cmd) {
            eprintln!("elaboration error: {}", e);
            // Continue processing
        }
    }

    Ok(elab.env)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn elab_with_init(src: &str) -> Result<Environment, ElabError> {
        let sp = vec![PathBuf::from("/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean")];
        interpret_lean_file(src, &sp)
    }

    #[test]
    fn test_interpret_def_simple() {
        let env = elab_with_init("import Init\ndef myZero := 0").unwrap();
        assert!(env.find(&Name::str("myZero")).is_some(), "myZero not found");
    }

    #[test]
    fn test_interpret_def_nat() {
        let env = elab_with_init("import Init\ndef myOne := 1").unwrap();
        let ci = env.find(&Name::str("myOne")).unwrap();
        assert!(ci.is_definition());
    }

    #[test]
    fn test_interpret_multiple_defs() {
        let env = elab_with_init("import Init\ndef a := 0\ndef b := 1\ndef c := 2").unwrap();
        assert!(env.find(&Name::str("a")).is_some());
        assert!(env.find(&Name::str("b")).is_some());
        assert!(env.find(&Name::str("c")).is_some());
    }
}
