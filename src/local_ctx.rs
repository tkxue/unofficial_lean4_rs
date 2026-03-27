//! Stage 04: Local Context — tracks free variables during type checking.

use std::collections::HashMap;

use crate::debruijn::{abstract_expr, instantiate};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// ============================================================================
// LocalDecl
// ============================================================================

#[derive(Clone, Debug)]
pub enum LocalDecl {
    /// Context declaration (regular variable with type + binder info).
    CDecl {
        index: u64,
        name: Name,
        user_name: Name,
        type_: Expr,
        bi: BinderInfo,
    },
    /// Let declaration (variable with type + value).
    LDecl {
        index: u64,
        name: Name,
        user_name: Name,
        type_: Expr,
        value: Expr,
    },
}

impl LocalDecl {
    pub fn get_idx(&self) -> u64 {
        match self { LocalDecl::CDecl { index, .. } | LocalDecl::LDecl { index, .. } => *index }
    }
    pub fn get_name(&self) -> &Name {
        match self { LocalDecl::CDecl { name, .. } | LocalDecl::LDecl { name, .. } => name }
    }
    pub fn get_user_name(&self) -> &Name {
        match self { LocalDecl::CDecl { user_name, .. } | LocalDecl::LDecl { user_name, .. } => user_name }
    }
    pub fn get_type(&self) -> &Expr {
        match self { LocalDecl::CDecl { type_, .. } | LocalDecl::LDecl { type_, .. } => type_ }
    }
    pub fn get_value(&self) -> Option<&Expr> {
        match self { LocalDecl::LDecl { value, .. } => Some(value), _ => None }
    }
    pub fn get_info(&self) -> BinderInfo {
        match self { LocalDecl::CDecl { bi, .. } => *bi, _ => BinderInfo::Default }
    }
    pub fn is_let(&self) -> bool { matches!(self, LocalDecl::LDecl { .. }) }
    pub fn mk_ref(&self) -> Expr { Expr::mk_fvar(self.get_name()) }
}

// ============================================================================
// LocalContext
// ============================================================================

#[derive(Clone, Debug)]
pub struct LocalContext {
    decls: HashMap<Name, LocalDecl>,
    next_idx: u64,
}

impl LocalContext {
    pub fn new() -> Self {
        LocalContext { decls: HashMap::new(), next_idx: 0 }
    }

    pub fn is_empty(&self) -> bool { self.decls.is_empty() }
    pub fn len(&self) -> usize { self.decls.len() }

    /// Add a context declaration (regular variable). Returns fvar reference.
    pub fn mk_local_decl(
        &mut self, name: Name, user_name: Name, type_: Expr, bi: BinderInfo,
    ) -> Expr {
        let idx = self.next_idx;
        self.next_idx += 1;
        let decl = LocalDecl::CDecl { index: idx, name: name.clone(), user_name, type_, bi };
        self.decls.insert(name.clone(), decl);
        Expr::mk_fvar(&name)
    }

    /// Add a let declaration. Returns fvar reference.
    pub fn mk_let_decl(
        &mut self, name: Name, user_name: Name, type_: Expr, value: Expr,
    ) -> Expr {
        let idx = self.next_idx;
        self.next_idx += 1;
        let decl = LocalDecl::LDecl { index: idx, name: name.clone(), user_name, type_, value };
        self.decls.insert(name.clone(), decl);
        Expr::mk_fvar(&name)
    }

    pub fn find(&self, name: &Name) -> Option<&LocalDecl> {
        self.decls.get(name)
    }

    pub fn find_fvar(&self, fvar: &Expr) -> Option<&LocalDecl> {
        assert!(fvar.is_fvar());
        self.find(fvar.fvar_name())
    }

    pub fn get(&self, name: &Name) -> &LocalDecl {
        self.find(name).unwrap_or_else(|| panic!("unknown local decl: {}", name))
    }

    pub fn get_type(&self, fvar: &Expr) -> &Expr {
        self.find_fvar(fvar).expect("unknown fvar").get_type()
    }

    pub fn clear(&mut self, name: &Name) {
        self.decls.remove(name);
    }

    /// Build `λ (x₁:A₁) ... (xₙ:Aₙ). body` from free variables.
    /// For let-bound fvars, wraps in Let instead of Lambda.
    pub fn mk_lambda(&self, fvars: &[Expr], body: &Expr) -> Expr {
        self.mk_binding(fvars, body, true)
    }

    /// Build `∀ (x₁:A₁) ... (xₙ:Aₙ). body` from free variables.
    pub fn mk_pi(&self, fvars: &[Expr], body: &Expr) -> Expr {
        self.mk_binding(fvars, body, false)
    }

    fn mk_binding(&self, fvars: &[Expr], body: &Expr, is_lambda: bool) -> Expr {
        let n = fvars.len();
        if n == 0 { return body.clone(); }

        // Step 1: abstract body over all fvars
        let mut result = abstract_expr(body, fvars);

        // Step 2: from last fvar to first, wrap in binding
        for i in (0..n).rev() {
            let decl = self.find_fvar(&fvars[i]).expect("fvar not in local context");
            // Abstract the type over remaining fvars (fvars[0..i])
            let ty = abstract_expr(decl.get_type(), &fvars[..i]);

            if decl.is_let() {
                let val = abstract_expr(decl.get_value().unwrap(), &fvars[..i]);
                result = Expr::mk_let(decl.get_user_name(), &ty, &val, &result, false);
            } else if is_lambda {
                result = Expr::mk_lambda(decl.get_user_name(), decl.get_info(), &ty, &result);
            } else {
                result = Expr::mk_pi(decl.get_user_name(), decl.get_info(), &ty, &result);
            }
        }
        result
    }
}

impl Default for LocalContext {
    fn default() -> Self { Self::new() }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn nat() -> Expr { Expr::mk_const(&Name::str("Nat"), &[]) }
    fn bool_() -> Expr { Expr::mk_const(&Name::str("Bool"), &[]) }

    #[test]
    fn test_empty() {
        let ctx = LocalContext::new();
        assert!(ctx.is_empty());
        assert_eq!(ctx.len(), 0);
    }

    #[test]
    fn test_add_cdecl() {
        let mut ctx = LocalContext::new();
        let x = ctx.mk_local_decl(Name::str("x"), Name::str("x"), nat(), BinderInfo::Default);
        assert!(x.is_fvar());
        assert_eq!(ctx.len(), 1);
        let decl = ctx.find_fvar(&x).unwrap();
        assert_eq!(decl.get_type(), &nat());
        assert!(!decl.is_let());
    }

    #[test]
    fn test_add_ldecl() {
        let mut ctx = LocalContext::new();
        let zero = Expr::mk_const(&Name::str("Nat.zero"), &[]);
        let x = ctx.mk_let_decl(Name::str("x"), Name::str("x"), nat(), zero.clone());
        let decl = ctx.find_fvar(&x).unwrap();
        assert!(decl.is_let());
        assert_eq!(decl.get_value(), Some(&zero));
    }

    #[test]
    fn test_mk_ref() {
        let mut ctx = LocalContext::new();
        let x = ctx.mk_local_decl(Name::str("x"), Name::str("x"), nat(), BinderInfo::Default);
        let decl = ctx.find_fvar(&x).unwrap();
        assert_eq!(decl.mk_ref(), x);
    }

    #[test]
    fn test_clear() {
        let mut ctx = LocalContext::new();
        ctx.mk_local_decl(Name::str("x"), Name::str("x"), nat(), BinderInfo::Default);
        assert_eq!(ctx.len(), 1);
        ctx.clear(&Name::str("x"));
        assert_eq!(ctx.len(), 0);
        assert!(ctx.find(&Name::str("x")).is_none());
    }

    #[test]
    fn test_get_type() {
        let mut ctx = LocalContext::new();
        let x = ctx.mk_local_decl(Name::str("x"), Name::str("x"), nat(), BinderInfo::Default);
        assert_eq!(ctx.get_type(&x), &nat());
    }

    #[test]
    fn test_mk_lambda_simple() {
        // mk_lambda([x:Nat, y:Bool], App(x, y))
        // should give: λ (x:Nat) (y:Bool). App(#1, #0)
        let mut ctx = LocalContext::new();
        let x = ctx.mk_local_decl(Name::str("x"), Name::str("x"), nat(), BinderInfo::Default);
        let y = ctx.mk_local_decl(Name::str("y"), Name::str("y"), bool_(), BinderInfo::Default);
        let body = Expr::mk_app(&x, &y);
        let result = ctx.mk_lambda(&[x, y], &body);

        assert!(result.is_lambda());
        assert_eq!(result.binding_domain(), &nat());

        let inner = result.binding_body();
        assert!(inner.is_lambda());
        assert_eq!(inner.binding_domain(), &bool_());

        let inner_body = inner.binding_body();
        assert!(inner_body.is_app());
        assert_eq!(inner_body.app_fn().bvar_idx(), 1);
        assert_eq!(inner_body.app_arg().bvar_idx(), 0);
    }

    #[test]
    fn test_mk_pi_simple() {
        let mut ctx = LocalContext::new();
        let x = ctx.mk_local_decl(Name::str("x"), Name::str("x"), nat(), BinderInfo::Default);
        let body = nat(); // non-dependent: Nat → Nat
        let result = ctx.mk_pi(&[x], &body);
        assert!(result.is_pi());
        assert_eq!(result.binding_domain(), &nat());
    }

    #[test]
    fn test_mk_lambda_with_let() {
        let mut ctx = LocalContext::new();
        let zero = Expr::mk_const(&Name::str("Nat.zero"), &[]);
        let x = ctx.mk_let_decl(Name::str("x"), Name::str("x"), nat(), zero.clone());
        let body = x.clone();
        let result = ctx.mk_lambda(&[x], &body);

        // Should produce Let, not Lambda
        assert!(result.is_let());
        assert_eq!(result.let_type(), &nat());
        assert_eq!(result.let_value(), &zero);
    }

    #[test]
    fn test_mk_lambda_empty() {
        let ctx = LocalContext::new();
        let e = nat();
        let result = ctx.mk_lambda(&[], &e);
        assert_eq!(result, e);
    }

    #[test]
    fn test_mk_lambda_roundtrip() {
        // mk_lambda then instantiate should recover original body
        let mut ctx = LocalContext::new();
        let x = ctx.mk_local_decl(Name::str("x"), Name::str("x"), nat(), BinderInfo::Default);
        let body = Expr::mk_app(&Expr::mk_const(&Name::str("f"), &[]), &x);
        let lam = ctx.mk_lambda(&[x.clone()], &body);

        // Open the binder: instantiate body with x
        let opened = instantiate(lam.binding_body(), &[x.clone()]);
        assert_eq!(opened, body);
    }

    #[test]
    fn test_mk_lambda_dependent_types() {
        // λ (x : Nat) (y : x). ...
        // y's type depends on x, so after abstracting [x], y's type becomes #0
        let mut ctx = LocalContext::new();
        let x = ctx.mk_local_decl(Name::str("x"), Name::str("x"), nat(), BinderInfo::Default);
        let y = ctx.mk_local_decl(Name::str("y"), Name::str("y"), x.clone(), BinderInfo::Default);
        let body = y.clone();
        let result = ctx.mk_lambda(&[x, y], &body);

        // λ (x : Nat). λ (y : #0). #0
        assert!(result.is_lambda());
        let inner = result.binding_body();
        assert!(inner.is_lambda());
        // y's type should be #0 (referring to x)
        assert!(inner.binding_domain().is_bvar());
        assert_eq!(inner.binding_domain().bvar_idx(), 0);
    }

    #[test]
    fn test_binder_info_preserved() {
        let mut ctx = LocalContext::new();
        let x = ctx.mk_local_decl(
            Name::str("x"), Name::str("x"), nat(), BinderInfo::Implicit,
        );
        let result = ctx.mk_lambda(&[x], &nat());
        assert_eq!(result.binding_info(), BinderInfo::Implicit);
    }
}
