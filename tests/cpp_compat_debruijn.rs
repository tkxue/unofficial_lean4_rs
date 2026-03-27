//! C++ compatibility tests for Stage 02: De Bruijn operations.

use lean4_kernel::name::Name;
use lean4_kernel::level::Level;
use lean4_kernel::expr::{Expr, BinderInfo};
use lean4_kernel::debruijn::*;

fn nat() -> Expr { Expr::mk_const(&Name::str("Nat"), &[]) }
fn zero() -> Expr { Expr::mk_const(&Name::str("Nat.zero"), &[]) }
fn succ() -> Expr { Expr::mk_const(&Name::str("Nat.succ"), &[]) }
fn fvar(s: &str) -> Expr { Expr::mk_fvar(&Name::str(s)) }
fn cst(s: &str) -> Expr { Expr::mk_const(&Name::str(s), &[]) }
fn lam(n: &str, dom: &Expr, body: &Expr) -> Expr {
    Expr::mk_lambda(&Name::str(n), BinderInfo::Default, dom, body)
}
fn pi(n: &str, dom: &Expr, body: &Expr) -> Expr {
    Expr::mk_pi(&Name::str(n), BinderInfo::Default, dom, body)
}

// ============================================================================
// replace
// ============================================================================

mod replace_tests {
    use super::*;

    #[test]
    fn test_replace_no_change_preserves_identity() {
        let e = Expr::mk_app(&succ(), &zero());
        let r = replace(&e, &mut |_, _| None);
        // update_* preserves pointer identity when children unchanged
        assert!(e.ptr_eq(&r));
    }

    #[test]
    fn test_replace_leaf() {
        let e = Expr::mk_app(&succ(), &zero());
        let r = replace(&e, &mut |sub, _| {
            if sub == &zero() { Some(cst("one")) } else { None }
        });
        assert_eq!(r.app_arg(), &cst("one"));
        assert_eq!(r.app_fn(), &succ()); // unchanged
    }

    #[test]
    fn test_replace_offset_under_binder() {
        let body = Expr::mk_bvar(0);
        let e = lam("x", &nat(), &body);
        let mut offsets = Vec::new();
        replace(&e, &mut |_, off| { offsets.push(off); None });
        // lambda(off=0), domain(0), body(1)
        assert_eq!(offsets, vec![0, 0, 1]);
    }

    #[test]
    fn test_replace_offset_nested_binders() {
        let body = Expr::mk_bvar(0);
        let inner = lam("y", &nat(), &body);
        let e = lam("x", &nat(), &inner);
        let mut offsets = Vec::new();
        replace(&e, &mut |_, off| { offsets.push(off); None });
        // outer_lam(0), dom(0), inner_lam(1), dom(1), body(2)
        assert_eq!(offsets, vec![0, 0, 1, 1, 2]);
    }

    #[test]
    fn test_replace_let_offset() {
        let e = Expr::mk_let(&Name::str("x"), &nat(), &zero(), &Expr::mk_bvar(0), false);
        let mut offsets = Vec::new();
        replace(&e, &mut |_, off| { offsets.push(off); None });
        // let(0), type(0), value(0), body(1)
        assert_eq!(offsets, vec![0, 0, 0, 1]);
    }
}

// ============================================================================
// for_each
// ============================================================================

mod for_each_tests {
    use super::*;

    #[test]
    fn test_count_nodes_const() {
        let mut count = 0;
        for_each(&nat(), &mut |_, _| { count += 1; true });
        assert_eq!(count, 1);
    }

    #[test]
    fn test_count_app_tree() {
        // f a b = App(App(f, a), b) → 5 nodes
        let e = Expr::mk_app_n(&cst("f"), &[cst("a"), cst("b")]);
        let mut count = 0;
        for_each(&e, &mut |_, _| { count += 1; true });
        assert_eq!(count, 5); // outer_app, inner_app, f, a, b
    }

    #[test]
    fn test_stop_at_root() {
        let e = Expr::mk_app(&succ(), &zero());
        let mut count = 0;
        for_each(&e, &mut |_, _| { count += 1; false });
        assert_eq!(count, 1);
    }

    #[test]
    fn test_offset_tracks_binders() {
        // λx. λy. let z := #0 in #1
        let inner_body = Expr::mk_bvar(1);
        let let_expr = Expr::mk_let(&Name::str("z"), &nat(), &Expr::mk_bvar(0), &inner_body, false);
        let inner = lam("y", &nat(), &let_expr);
        let e = lam("x", &nat(), &inner);

        let mut max_offset = 0;
        for_each(&e, &mut |_, off| { max_offset = max_offset.max(off); true });
        assert_eq!(max_offset, 3); // x(0), y(1), let(2), body_of_let(3)
    }
}

// ============================================================================
// find
// ============================================================================

mod find_tests {
    use super::*;

    #[test]
    fn test_find_bvar() {
        let e = Expr::mk_app(&Expr::mk_bvar(0), &cst("a"));
        let r = find(&e, &|sub| sub.is_bvar());
        assert!(r.is_some());
        assert_eq!(r.unwrap().bvar_idx(), 0);
    }

    #[test]
    fn test_find_deep() {
        let inner = Expr::mk_app(&cst("target"), &cst("a"));
        let e = Expr::mk_app(&cst("f"), &inner);
        let r = find(&e, &|sub| sub.is_const() && sub.const_name() == &Name::str("target"));
        assert!(r.is_some());
    }

    #[test]
    fn test_find_none() {
        let e = Expr::mk_app(&cst("f"), &cst("a"));
        let r = find(&e, &|sub| sub.is_bvar());
        assert!(r.is_none());
    }
}

// ============================================================================
// lift_loose_bvars
// ============================================================================

mod lift_tests {
    use super::*;

    #[test]
    fn test_lift_bvar_from_zero() {
        // #0 lifted by 5 from threshold 0 → #5
        let r = lift_loose_bvars(&Expr::mk_bvar(0), 0, 5);
        assert_eq!(r.bvar_idx(), 5);
    }

    #[test]
    fn test_lift_bvar_above_threshold() {
        // #3, threshold 2, lift 10 → #13
        let r = lift_loose_bvars(&Expr::mk_bvar(3), 2, 10);
        assert_eq!(r.bvar_idx(), 13);
    }

    #[test]
    fn test_lift_bvar_below_threshold() {
        // #1, threshold 5, lift 10 → #1 (unchanged)
        let b = Expr::mk_bvar(1);
        let r = lift_loose_bvars(&b, 5, 10);
        assert!(b.ptr_eq(&r));
    }

    #[test]
    fn test_lift_zero_is_identity() {
        let e = Expr::mk_app(&Expr::mk_bvar(0), &Expr::mk_bvar(1));
        let r = lift_loose_bvars(&e, 0, 0);
        assert!(e.ptr_eq(&r));
    }

    #[test]
    fn test_lift_no_bvars_is_identity() {
        let e = nat();
        let r = lift_loose_bvars_simple(&e, 100);
        assert!(e.ptr_eq(&r));
    }

    #[test]
    fn test_lift_in_app() {
        // App(#0, #2) lifted by 1 from 0 → App(#1, #3)
        let e = Expr::mk_app(&Expr::mk_bvar(0), &Expr::mk_bvar(2));
        let r = lift_loose_bvars_simple(&e, 1);
        assert_eq!(r.app_fn().bvar_idx(), 1);
        assert_eq!(r.app_arg().bvar_idx(), 3);
    }

    #[test]
    fn test_lift_under_binder() {
        // λx. #1 lifted by 1 from 0 → λx. #2
        // Under the binder, threshold becomes 0+1=1, so #1 >= 1, lifted to #2
        let body = Expr::mk_bvar(1);
        let e = lam("x", &nat(), &body);
        let r = lift_loose_bvars_simple(&e, 1);
        assert!(r.is_lambda());
        assert_eq!(r.binding_body().bvar_idx(), 2);
    }
}

// ============================================================================
// lower_loose_bvars
// ============================================================================

mod lower_tests {
    use super::*;

    #[test]
    fn test_lower_basic() {
        // #5, lower bvars >= 3 by 3 → #2
        let r = lower_loose_bvars(&Expr::mk_bvar(5), 3, 3);
        assert_eq!(r.bvar_idx(), 2);
    }

    #[test]
    fn test_lower_no_effect() {
        let b = Expr::mk_bvar(1);
        let r = lower_loose_bvars(&b, 5, 3); // #1 < 5, unchanged
        assert!(b.ptr_eq(&r));
    }

    #[test]
    fn test_lower_zero_is_identity() {
        let e = Expr::mk_bvar(3);
        let r = lower_loose_bvars(&e, 0, 0);
        assert!(e.ptr_eq(&r));
    }
}

// ============================================================================
// has_loose_bvar
// ============================================================================

mod has_loose_bvar_tests {
    use super::*;

    #[test]
    fn test_bvar_present() {
        assert!(has_loose_bvar(&Expr::mk_bvar(3), 3));
    }

    #[test]
    fn test_bvar_absent() {
        assert!(!has_loose_bvar(&Expr::mk_bvar(3), 2));
    }

    #[test]
    fn test_in_app() {
        let e = Expr::mk_app(&Expr::mk_bvar(1), &cst("a"));
        assert!(has_loose_bvar(&e, 1));
        assert!(!has_loose_bvar(&e, 0));
    }

    #[test]
    fn test_under_binder() {
        // λx. #1 — bvar 1 under 1 binder means loose bvar 0 at top level
        let body = Expr::mk_bvar(1);
        let e = lam("x", &nat(), &body);
        assert!(has_loose_bvar(&e, 0));
        assert!(!has_loose_bvar(&e, 1));
    }

    #[test]
    fn test_no_bvars() {
        assert!(!has_loose_bvar(&nat(), 0));
    }
}

// ============================================================================
// instantiate
// ============================================================================

mod instantiate_tests {
    use super::*;

    #[test]
    fn test_single_subst() {
        let r = instantiate1(&Expr::mk_bvar(0), &cst("a"));
        assert_eq!(r, cst("a"));
    }

    #[test]
    fn test_no_bvars_unchanged() {
        let e = nat();
        let r = instantiate1(&e, &cst("a"));
        assert!(e.ptr_eq(&r));
    }

    #[test]
    fn test_multi_subst() {
        // App(#0, #1) [0:=a, 1:=b] → App(a, b)
        let e = Expr::mk_app(&Expr::mk_bvar(0), &Expr::mk_bvar(1));
        let r = instantiate(&e, &[cst("a"), cst("b")]);
        assert_eq!(r.app_fn(), &cst("a"));
        assert_eq!(r.app_arg(), &cst("b"));
    }

    #[test]
    fn test_shift_down() {
        // #5 [0:=a, 1:=b] → #3 (shifted down by 2)
        let r = instantiate(&Expr::mk_bvar(5), &[cst("a"), cst("b")]);
        assert!(r.is_bvar());
        assert_eq!(r.bvar_idx(), 3);
    }

    #[test]
    fn test_under_one_binder() {
        // λx. #1 [0:=a] → λx. a
        let e = lam("x", &nat(), &Expr::mk_bvar(1));
        let r = instantiate(&e, &[cst("a")]);
        assert!(r.is_lambda());
        assert_eq!(r.binding_body(), &cst("a"));
    }

    #[test]
    fn test_bound_var_untouched() {
        // λx. #0 [0:=a] → λx. #0  (bvar 0 is bound)
        let e = lam("x", &nat(), &Expr::mk_bvar(0));
        let r = instantiate(&e, &[cst("a")]);
        assert!(r.binding_body().is_bvar());
        assert_eq!(r.binding_body().bvar_idx(), 0);
    }

    #[test]
    fn test_lift_during_subst() {
        // λx. #1 [0:=λy. #0]
        // Under the binder, offset=1, so #1-0 is in range, subst[0] = λy.#0
        // Must lift λy.#0 by offset=1 → λy.#0 (the inner #0 is bound, no loose bvars to lift)
        let subst_val = lam("y", &nat(), &Expr::mk_bvar(0));
        let e = lam("x", &nat(), &Expr::mk_bvar(1));
        let r = instantiate(&e, &[subst_val.clone()]);
        assert!(r.is_lambda());
        assert_eq!(r.binding_body(), &subst_val);
    }

    #[test]
    fn test_lift_free_bvar_in_subst() {
        // #0 inside body of λ, substituted with #0 (free bvar)
        // λx. #1 [0 := #0]
        // Under binder (offset=1): #1 >= 1, idx_in_subst = 1-1 = 0
        // subst[0] = #0 must be lifted by 1 → #1
        let e = lam("x", &nat(), &Expr::mk_bvar(1));
        let r = instantiate(&e, &[Expr::mk_bvar(0)]);
        assert!(r.is_lambda());
        assert_eq!(r.binding_body().bvar_idx(), 1);
    }

    #[test]
    fn test_instantiate_at_offset() {
        // #2 with s=1, subst=[a] → should replace bvar 1 only
        // bvar 2 >= s=1, 2-1=1 < n=1? No, 1 is not < 1. So shift: bvar(2-1)=bvar(1)
        let r = instantiate_at(&Expr::mk_bvar(2), 1, &[cst("a")]);
        assert!(r.is_bvar());
        assert_eq!(r.bvar_idx(), 1);

        // #1 with s=1, subst=[a] → bvar 1 >= 1, 1-1=0 < 1, replace with a
        let r2 = instantiate_at(&Expr::mk_bvar(1), 1, &[cst("a")]);
        assert_eq!(r2, cst("a"));
    }
}

// ============================================================================
// instantiate_rev
// ============================================================================

mod instantiate_rev_tests {
    use super::*;

    #[test]
    fn test_rev_single() {
        // #0 rev_subst=[a] → a (same as forward for n=1)
        let r = instantiate_rev(&Expr::mk_bvar(0), &[cst("a")]);
        assert_eq!(r, cst("a"));
    }

    #[test]
    fn test_rev_multi() {
        // #0 rev_subst=[b, a] → subst[2-0-1]=subst[1]=a
        // #1 rev_subst=[b, a] → subst[2-1-1]=subst[0]=b
        let e = Expr::mk_app(&Expr::mk_bvar(0), &Expr::mk_bvar(1));
        let r = instantiate_rev(&e, &[cst("b"), cst("a")]);
        assert_eq!(r.app_fn(), &cst("a"));
        assert_eq!(r.app_arg(), &cst("b"));
    }

    #[test]
    fn test_rev_shift() {
        // #3 rev_subst=[a, b] → 3 >= 0 and 3 < 2? No. Shift: #(3-2) = #1
        let r = instantiate_rev(&Expr::mk_bvar(3), &[cst("a"), cst("b")]);
        assert!(r.is_bvar());
        assert_eq!(r.bvar_idx(), 1);
    }
}

// ============================================================================
// abstract
// ============================================================================

mod abstract_tests {
    use super::*;

    #[test]
    fn test_abstract_single_fvar() {
        let x = fvar("x");
        let e = Expr::mk_app(&cst("f"), &x);
        let r = abstract1(&e, &x);
        assert_eq!(r.app_fn(), &cst("f"));
        assert!(r.app_arg().is_bvar());
        assert_eq!(r.app_arg().bvar_idx(), 0);
    }

    #[test]
    fn test_abstract_no_match() {
        let x = fvar("x");
        let y = fvar("y");
        let e = Expr::mk_app(&cst("f"), &x);
        let r = abstract1(&e, &y);
        // y not in e, unchanged
        assert_eq!(r.app_arg(), &x);
    }

    #[test]
    fn test_abstract_no_fvars_unchanged() {
        let e = Expr::mk_app(&cst("f"), &cst("a"));
        let r = abstract1(&e, &fvar("x"));
        assert!(e.ptr_eq(&r));
    }

    #[test]
    fn test_abstract_multiple_ordering() {
        // abstract [x, y] over App(x, y):
        // x → #(n-0-1) = #(2-0-1) = #1
        // y → #(n-1-1) = #(2-1-1) = #0
        let x = fvar("x");
        let y = fvar("y");
        let e = Expr::mk_app(&x, &y);
        let r = abstract_expr(&e, &[x, y]);
        assert_eq!(r.app_fn().bvar_idx(), 1);
        assert_eq!(r.app_arg().bvar_idx(), 0);
    }

    #[test]
    fn test_abstract_under_binder() {
        // λ_. x with abstract [x]:
        // Under binder (offset=1): x → #(1 + 1 - 0 - 1) = #1
        let x = fvar("x");
        let e = lam("a", &nat(), &x);
        let r = abstract1(&e, &x);
        assert!(r.is_lambda());
        assert!(r.binding_body().is_bvar());
        assert_eq!(r.binding_body().bvar_idx(), 1);
    }

    #[test]
    fn test_abstract_roundtrip_single() {
        let x = fvar("x");
        let e = Expr::mk_app(&cst("f"), &x);
        let abst = abstract1(&e, &x);
        let back = instantiate1(&abst, &x);
        assert_eq!(back, e);
    }

    #[test]
    fn test_abstract_roundtrip_multiple() {
        let x = fvar("x");
        let y = fvar("y");
        let z = fvar("z");
        let e = Expr::mk_app_n(&cst("f"), &[x.clone(), y.clone(), z.clone()]);
        let abst = abstract_expr(&e, &[x.clone(), y.clone(), z.clone()]);
        // x→#2, y→#1, z→#0, so instantiate with [z, y, x]
        let back = instantiate(&abst, &[z, y, x]);
        assert_eq!(back, e);
    }

    #[test]
    fn test_abstract_by_name() {
        let e = Expr::mk_app(&cst("f"), &fvar("x"));
        let r = abstract_name(&e, &Name::str("x"));
        assert!(r.app_arg().is_bvar());
    }
}

// ============================================================================
// beta reduction
// ============================================================================

mod beta_tests {
    use super::*;

    #[test]
    fn test_is_head_beta_true() {
        let lam_e = lam("x", &nat(), &Expr::mk_bvar(0));
        let app = Expr::mk_app(&lam_e, &zero());
        assert!(is_head_beta(&app));
    }

    #[test]
    fn test_is_head_beta_false() {
        assert!(!is_head_beta(&cst("f")));
        assert!(!is_head_beta(&Expr::mk_app(&cst("f"), &cst("a"))));
    }

    #[test]
    fn test_beta_identity() {
        // (λx. x) a → a
        let app = Expr::mk_app(&lam("x", &nat(), &Expr::mk_bvar(0)), &cst("a"));
        assert_eq!(head_beta_reduce(&app), cst("a"));
    }

    #[test]
    fn test_beta_constant_body() {
        // (λx. Nat) a → Nat
        let app = Expr::mk_app(&lam("x", &nat(), &nat()), &cst("a"));
        assert_eq!(head_beta_reduce(&app), nat());
    }

    #[test]
    fn test_beta_two_args() {
        // (λx. λy. x) a b → a
        let inner = lam("y", &nat(), &Expr::mk_bvar(1)); // #1 = x
        let outer = lam("x", &nat(), &inner);
        let app = Expr::mk_app_n(&outer, &[cst("a"), cst("b")]);
        assert_eq!(head_beta_reduce(&app), cst("a"));
    }

    #[test]
    fn test_beta_three_args() {
        // (λx. λy. λz. y) a b c → b
        let body = Expr::mk_bvar(1); // #1 = y (under z)
        let lam_z = lam("z", &nat(), &body);
        let lam_y = lam("y", &nat(), &lam_z);
        let lam_x = lam("x", &nat(), &lam_y);
        let app = Expr::mk_app_n(&lam_x, &[cst("a"), cst("b"), cst("c")]);
        assert_eq!(head_beta_reduce(&app), cst("b"));
    }

    #[test]
    fn test_beta_partial_application() {
        // (λx. λy. App(x, y)) a → λy. App(a, y)
        let body = Expr::mk_app(&Expr::mk_bvar(1), &Expr::mk_bvar(0));
        let inner = lam("y", &nat(), &body);
        let outer = lam("x", &nat(), &inner);
        let app = Expr::mk_app(&outer, &cst("a"));
        let r = head_beta_reduce(&app);
        // Should be λy. App(a, #0)
        assert!(r.is_lambda());
        assert!(r.binding_body().is_app());
        assert_eq!(r.binding_body().app_fn(), &cst("a"));
        assert_eq!(r.binding_body().app_arg().bvar_idx(), 0);
    }

    #[test]
    fn test_beta_no_reduction() {
        let e = Expr::mk_app(&cst("f"), &cst("a"));
        let r = head_beta_reduce(&e);
        assert_eq!(r, e);
    }

    #[test]
    fn test_cheap_beta_const_body() {
        let app = Expr::mk_app(&lam("x", &nat(), &nat()), &cst("a"));
        assert_eq!(cheap_beta_reduce(&app), nat());
    }

    #[test]
    fn test_cheap_beta_bvar() {
        // (λx. x) a → a
        let app = Expr::mk_app(&lam("x", &nat(), &Expr::mk_bvar(0)), &cst("a"));
        assert_eq!(cheap_beta_reduce(&app), cst("a"));
    }

    #[test]
    fn test_cheap_beta_not_app() {
        assert_eq!(cheap_beta_reduce(&cst("a")), cst("a"));
    }

    #[test]
    fn test_cheap_beta_not_lambda_head() {
        let e = Expr::mk_app(&cst("f"), &cst("a"));
        assert_eq!(cheap_beta_reduce(&e), e);
    }

    #[test]
    fn test_cheap_beta_complex_body_unchanged() {
        // (λx. App(#0, #0)) a — body has loose bvars and is not a single bvar
        let body = Expr::mk_app(&Expr::mk_bvar(0), &Expr::mk_bvar(0));
        let app = Expr::mk_app(&lam("x", &nat(), &body), &cst("a"));
        let r = cheap_beta_reduce(&app);
        assert_eq!(r, app); // cannot cheap-reduce
    }
}

// ============================================================================
// instantiate_lparams
// ============================================================================

mod lparams_tests {
    use super::*;

    #[test]
    fn test_sort_subst() {
        let u = Level::mk_param(&Name::str("u"));
        let e = Expr::mk_sort(&u);
        let r = instantiate_lparams(&e, &[Name::str("u")], &[Level::one()]);
        assert_eq!(r.sort_level(), &Level::one());
    }

    #[test]
    fn test_const_subst() {
        let u = Level::mk_param(&Name::str("u"));
        let e = Expr::mk_const(&Name::str("List"), &[u]);
        let r = instantiate_lparams(&e, &[Name::str("u")], &[Level::zero()]);
        assert_eq!(r.const_levels()[0], Level::zero());
    }

    #[test]
    fn test_no_params_unchanged() {
        let e = Expr::mk_const(&Name::str("Nat"), &[]);
        let r = instantiate_lparams(&e, &[Name::str("u")], &[Level::one()]);
        assert!(e.ptr_eq(&r));
    }

    #[test]
    fn test_multi_params() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let e = Expr::mk_const(&Name::str("Prod"), &[u, v]);
        let r = instantiate_lparams(&e,
            &[Name::str("u"), Name::str("v")],
            &[Level::zero(), Level::one()]);
        assert_eq!(r.const_levels()[0], Level::zero());
        assert_eq!(r.const_levels()[1], Level::one());
    }

    #[test]
    fn test_nested_in_app() {
        let u = Level::mk_param(&Name::str("u"));
        let f = Expr::mk_const(&Name::str("f"), &[u.clone()]);
        let s = Expr::mk_sort(&u);
        let e = Expr::mk_app(&f, &s);
        let r = instantiate_lparams(&e, &[Name::str("u")], &[Level::one()]);
        assert_eq!(r.app_fn().const_levels()[0], Level::one());
        assert_eq!(r.app_arg().sort_level(), &Level::one());
    }

    #[test]
    fn test_partial_subst() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let e = Expr::mk_const(&Name::str("Prod"), &[u, v]);
        let r = instantiate_lparams(&e, &[Name::str("u")], &[Level::zero()]);
        assert_eq!(r.const_levels()[0], Level::zero());
        assert!(r.const_levels()[1].is_param()); // v unchanged
    }

    #[test]
    fn test_in_lambda_body() {
        let u = Level::mk_param(&Name::str("u"));
        let body = Expr::mk_sort(&u);
        let e = lam("x", &nat(), &body);
        let r = instantiate_lparams(&e, &[Name::str("u")], &[Level::one()]);
        assert!(r.is_lambda());
        assert_eq!(r.binding_body().sort_level(), &Level::one());
    }
}
