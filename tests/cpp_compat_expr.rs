//! C++ compatibility tests for Stage 01: Expressions.
//!
//! Verifies that our Expr.Data packing and hash computation matches
//! the exact C++ `lean_expr_mk_data` and `lean_expr_mk_app_data`.

use lean4_kernel::hash::mix_hash;
use lean4_kernel::name::Name;
use lean4_kernel::level::Level;
use lean4_kernel::expr::{Expr, BinderInfo, Literal};

// ============================================================================
// ExprData packing — replicate C++ lean_expr_mk_data exactly
// ============================================================================

/// Reference C++ lean_expr_mk_data
fn cpp_mk_data(
    hash: u64, bvar_range: u32, approx_depth: u32,
    has_fvar: bool, has_expr_mvar: bool, has_level_mvar: bool, has_level_param: bool,
) -> u64 {
    let depth = approx_depth.min(255);
    let range = bvar_range.min(1048575);
    let h = hash as u32;
    (h as u64)
        + ((depth as u64) << 32)
        + ((has_fvar as u64) << 40)
        + ((has_expr_mvar as u64) << 41)
        + ((has_level_mvar as u64) << 42)
        + ((has_level_param as u64) << 43)
        + ((range as u64) << 44)
}

/// Reference C++ lean_expr_mk_app_data
fn cpp_mk_app_data(f_data: u64, a_data: u64) -> u64 {
    let get_depth = |d: u64| -> u32 { ((d >> 32) & 255) as u32 };
    let get_range = |d: u64| -> u32 { (d >> 44) as u32 };
    let depth = get_depth(f_data).max(get_depth(a_data)).saturating_add(1).min(255);
    let range = get_range(f_data).max(get_range(a_data));
    let h = mix_hash(f_data, a_data) as u32;
    let flags = (f_data | a_data) & (15u64 << 40);
    flags | (h as u64) | ((depth as u64) << 32) | ((range as u64) << 44)
}

fn hash_levels(ls: &[Level]) -> u64 {
    ls.iter().fold(7u64, |r, l| mix_hash(r, l.hash()))
}

// ============================================================================
// Hash verification — compute expected hash using C++ algorithm, compare
// ============================================================================

mod data_packing {
    use super::*;

    fn get_data(e: &Expr) -> u64 {
        cpp_mk_data(
            e.hash() as u64,
            e.loose_bvar_range(),
            e.approx_depth(),
            e.has_fvar(),
            e.has_expr_mvar(),
            e.has_level_mvar(),
            e.has_univ_param(),
        )
    }

    #[test]
    fn test_bvar_data() {
        for idx in [0, 1, 5, 100] {
            let e = Expr::mk_bvar(idx);
            let expected_hash = mix_hash(7, idx) as u32;
            assert_eq!(e.hash(), expected_hash, "bvar({}) hash mismatch", idx);
            assert_eq!(e.loose_bvar_range(), (idx as u32).min(1048575) + 1, "bvar({}) range", idx);
            assert_eq!(e.approx_depth(), 0);
            assert!(!e.has_fvar());
            assert!(!e.has_expr_mvar());
        }
    }

    #[test]
    fn test_fvar_data() {
        let e = Expr::mk_fvar(&Name::str("x"));
        let expected_hash = mix_hash(13, Name::str("x").hash()) as u32;
        assert_eq!(e.hash(), expected_hash);
        assert_eq!(e.loose_bvar_range(), 0);
        assert!(e.has_fvar());
        assert!(!e.has_expr_mvar());
    }

    #[test]
    fn test_mvar_data() {
        let e = Expr::mk_mvar(&Name::str("m"));
        let expected_hash = mix_hash(17, Name::str("m").hash()) as u32;
        assert_eq!(e.hash(), expected_hash);
        assert!(e.has_expr_mvar());
        assert!(!e.has_fvar());
    }

    #[test]
    fn test_sort_data() {
        let l = Level::mk_param(&Name::str("u"));
        let e = Expr::mk_sort(&l);
        let expected_hash = mix_hash(11, l.hash()) as u32;
        assert_eq!(e.hash(), expected_hash);
        assert!(e.has_univ_param());
        assert!(!e.has_level_mvar());
    }

    #[test]
    fn test_sort_with_mvar() {
        let l = Level::mk_mvar(&Name::str("m"));
        let e = Expr::mk_sort(&l);
        assert!(e.has_level_mvar());
        assert!(!e.has_univ_param());
    }

    #[test]
    fn test_const_data() {
        let e = Expr::mk_const(&Name::str("Nat"), &[]);
        let expected_hash = mix_hash(5, mix_hash(Name::str("Nat").hash(), hash_levels(&[]))) as u32;
        assert_eq!(e.hash(), expected_hash);
        assert!(!e.has_univ_param());
    }

    #[test]
    fn test_const_with_levels_data() {
        let u = Level::mk_param(&Name::str("u"));
        let e = Expr::mk_const(&Name::str("List"), &[u.clone()]);
        let expected_hash = mix_hash(5, mix_hash(
            Name::str("List").hash(),
            hash_levels(&[u]),
        )) as u32;
        assert_eq!(e.hash(), expected_hash);
        assert!(e.has_univ_param());
    }

    #[test]
    fn test_app_data_matches_cpp() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let app = Expr::mk_app(&f, &a);

        let f_packed = get_data(&f);
        let a_packed = get_data(&a);
        let expected_packed = cpp_mk_app_data(f_packed, a_packed);

        let actual_packed = get_data(&app);
        assert_eq!(actual_packed, expected_packed,
            "App data mismatch: actual={:#x} expected={:#x}", actual_packed, expected_packed);
    }

    #[test]
    fn test_app_nested_data() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let app1 = Expr::mk_app(&f, &a);
        let app2 = Expr::mk_app(&app1, &b);

        let app1_packed = get_data(&app1);
        let b_packed = get_data(&b);
        let expected = cpp_mk_app_data(app1_packed, b_packed);
        let actual = get_data(&app2);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_lambda_data() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);

        let td = nat.approx_depth();
        let bd = body.approx_depth();
        let depth = td.max(bd) + 1;
        let range = nat.loose_bvar_range().max(body.loose_bvar_range().saturating_sub(1));
        let expected_hash = mix_hash(depth as u64, mix_hash(nat.hash() as u64, body.hash() as u64)) as u32;

        assert_eq!(lam.hash(), expected_hash);
        assert_eq!(lam.loose_bvar_range(), range);
        assert_eq!(lam.approx_depth(), depth);
    }

    #[test]
    fn test_pi_data() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_const(&Name::str("Bool"), &[]);
        let pi = Expr::mk_pi(&Name::str("x"), BinderInfo::Default, &nat, &body);

        let depth = nat.approx_depth().max(body.approx_depth()) + 1;
        let expected_hash = mix_hash(depth as u64, mix_hash(nat.hash() as u64, body.hash() as u64)) as u32;
        assert_eq!(pi.hash(), expected_hash);
        assert_eq!(pi.loose_bvar_range(), 0);
    }

    #[test]
    fn test_let_data() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let zero = Expr::mk_const(&Name::str("Nat.zero"), &[]);
        let body = Expr::mk_bvar(0);
        let e = Expr::mk_let(&Name::str("x"), &nat, &zero, &body, false);

        let depth = nat.approx_depth().max(zero.approx_depth()).max(body.approx_depth()) + 1;
        let range = nat.loose_bvar_range().max(zero.loose_bvar_range()).max(body.loose_bvar_range().saturating_sub(1));
        let expected_hash = mix_hash(depth as u64,
            mix_hash(nat.hash() as u64,
                mix_hash(zero.hash() as u64, body.hash() as u64))) as u32;

        assert_eq!(e.hash(), expected_hash);
        assert_eq!(e.loose_bvar_range(), range);
    }

    #[test]
    fn test_lit_data() {
        let e = Expr::mk_lit(Literal::Nat(42));
        let expected_hash = mix_hash(3, 42u64) as u32;
        assert_eq!(e.hash(), expected_hash);
    }

    #[test]
    fn test_lit_string_data() {
        let e = Expr::mk_lit(Literal::Str("hello".into()));
        let str_hash = lean4_kernel::hash::hash_str(b"hello", 11);
        let expected_hash = mix_hash(3, str_hash) as u32;
        assert_eq!(e.hash(), expected_hash);
    }

    #[test]
    fn test_mdata_data() {
        let inner = Expr::mk_const(&Name::str("Nat"), &[]);
        let md = Expr::mk_mdata(&inner);
        let depth = inner.approx_depth() + 1;
        let expected_hash = mix_hash(depth as u64, inner.hash() as u64) as u32;
        assert_eq!(md.hash(), expected_hash);
        assert_eq!(md.loose_bvar_range(), inner.loose_bvar_range());
    }

    #[test]
    fn test_proj_data() {
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let p = Expr::mk_proj(&Name::str("Prod"), 0, &a);
        let depth = a.approx_depth() + 1;
        let expected_hash = mix_hash(depth as u64,
            mix_hash(Name::str("Prod").hash(),
                mix_hash(0u64, a.hash() as u64))) as u32;
        assert_eq!(p.hash(), expected_hash);
    }
}

// ============================================================================
// Flag propagation tests
// ============================================================================

mod flag_propagation {
    use super::*;

    #[test]
    fn test_fvar_propagates_through_app() {
        let fv = Expr::mk_fvar(&Name::str("x"));
        let c = Expr::mk_const(&Name::str("f"), &[]);
        let app = Expr::mk_app(&c, &fv);
        assert!(app.has_fvar());
        assert!(!app.has_expr_mvar());
    }

    #[test]
    fn test_mvar_propagates_through_app() {
        let mv = Expr::mk_mvar(&Name::str("m"));
        let c = Expr::mk_const(&Name::str("f"), &[]);
        let app = Expr::mk_app(&c, &mv);
        assert!(app.has_expr_mvar());
        assert!(!app.has_fvar());
    }

    #[test]
    fn test_both_flags_propagate() {
        let fv = Expr::mk_fvar(&Name::str("x"));
        let mv = Expr::mk_mvar(&Name::str("m"));
        let app = Expr::mk_app(&fv, &mv);
        assert!(app.has_fvar());
        assert!(app.has_expr_mvar());
    }

    #[test]
    fn test_level_mvar_propagates() {
        let lm = Level::mk_mvar(&Name::str("u"));
        let s = Expr::mk_sort(&lm);
        let c = Expr::mk_const(&Name::str("f"), &[]);
        let app = Expr::mk_app(&c, &s);
        assert!(app.has_level_mvar());
    }

    #[test]
    fn test_level_param_propagates() {
        let u = Level::mk_param(&Name::str("u"));
        let c = Expr::mk_const(&Name::str("List"), &[u]);
        let app = Expr::mk_app(&c, &Expr::mk_const(&Name::str("Nat"), &[]));
        assert!(app.has_univ_param());
    }

    #[test]
    fn test_flags_through_lambda() {
        let fv = Expr::mk_fvar(&Name::str("x"));
        let mv = Expr::mk_mvar(&Name::str("m"));
        let lam = Expr::mk_lambda(&Name::str("a"), BinderInfo::Default, &fv, &mv);
        assert!(lam.has_fvar());
        assert!(lam.has_expr_mvar());
    }

    #[test]
    fn test_flags_through_let() {
        let u = Level::mk_param(&Name::str("u"));
        let ty = Expr::mk_sort(&u);
        let val = Expr::mk_fvar(&Name::str("x"));
        let body = Expr::mk_mvar(&Name::str("m"));
        let e = Expr::mk_let(&Name::str("a"), &ty, &val, &body, false);
        assert!(e.has_fvar());
        assert!(e.has_expr_mvar());
        assert!(e.has_univ_param());
    }
}

// ============================================================================
// Loose bvar range tests
// ============================================================================

mod loose_bvar {
    use super::*;

    #[test]
    fn test_bvar_range() {
        assert_eq!(Expr::mk_bvar(0).loose_bvar_range(), 1);
        assert_eq!(Expr::mk_bvar(1).loose_bvar_range(), 2);
        assert_eq!(Expr::mk_bvar(5).loose_bvar_range(), 6);
    }

    #[test]
    fn test_no_bvars() {
        assert_eq!(Expr::mk_const(&Name::str("Nat"), &[]).loose_bvar_range(), 0);
        assert_eq!(Expr::mk_fvar(&Name::str("x")).loose_bvar_range(), 0);
        assert_eq!(Expr::mk_lit(Literal::Nat(42)).loose_bvar_range(), 0);
    }

    #[test]
    fn test_app_range_max() {
        let b0 = Expr::mk_bvar(0);
        let b5 = Expr::mk_bvar(5);
        let app = Expr::mk_app(&b0, &b5);
        assert_eq!(app.loose_bvar_range(), 6);
    }

    #[test]
    fn test_lambda_decrements_body() {
        // lambda x. #2 — body has range 3, decremented by 1 = 2
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_bvar(2);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        assert_eq!(lam.loose_bvar_range(), 2);
    }

    #[test]
    fn test_lambda_captures_bvar0() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        assert_eq!(lam.loose_bvar_range(), 0);
        assert!(!lam.has_loose_bvars());
    }

    #[test]
    fn test_let_decrements_body() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let zero = Expr::mk_const(&Name::str("Nat.zero"), &[]);
        let body = Expr::mk_bvar(3);
        let e = Expr::mk_let(&Name::str("x"), &nat, &zero, &body, false);
        assert_eq!(e.loose_bvar_range(), 3);
    }

    #[test]
    fn test_domain_bvars_not_decremented() {
        // lambda (x : #5). #0 — domain has bvar 5, not decremented
        let domain = Expr::mk_bvar(5);
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &domain, &body);
        assert_eq!(lam.loose_bvar_range(), 6); // max(6, 1-1) = 6
    }
}

// ============================================================================
// Equality tests
// ============================================================================

mod equality {
    use super::*;

    #[test]
    fn test_structural_eq_ignores_binder_name() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_bvar(0);
        let lam1 = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        let lam2 = Expr::mk_lambda(&Name::str("y"), BinderInfo::Default, &nat, &body);
        // Lean structural equality ignores binder names
        assert_eq!(lam1, lam2);
    }

    #[test]
    fn test_structural_eq_ignores_binder_info() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_bvar(0);
        let lam1 = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        let lam2 = Expr::mk_lambda(&Name::str("x"), BinderInfo::Implicit, &nat, &body);
        // Lean structural equality (is_equal) ignores binder info
        assert_eq!(lam1, lam2);
    }

    #[test]
    fn test_let_eq_ignores_nondep() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let zero = Expr::mk_const(&Name::str("Nat.zero"), &[]);
        let body = Expr::mk_bvar(0);
        let e1 = Expr::mk_let(&Name::str("x"), &nat, &zero, &body, false);
        let e2 = Expr::mk_let(&Name::str("x"), &nat, &zero, &body, true);
        assert_eq!(e1, e2);
    }

    #[test]
    fn test_different_kinds_not_equal() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let bv = Expr::mk_bvar(0);
        assert_ne!(nat, bv);
    }

    #[test]
    fn test_const_different_levels() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let c1 = Expr::mk_const(&Name::str("List"), &[u]);
        let c2 = Expr::mk_const(&Name::str("List"), &[v]);
        assert_ne!(c1, c2);
    }

    #[test]
    fn test_deep_equality() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let e1 = Expr::mk_app(&Expr::mk_app(&f, &a), &b);
        let e2 = Expr::mk_app(&Expr::mk_app(&f, &a), &b);
        assert_eq!(e1, e2);
    }
}

// ============================================================================
// App utility tests
// ============================================================================

mod app_utils {
    use super::*;

    #[test]
    fn test_get_app_fn_non_app() {
        let c = Expr::mk_const(&Name::str("Nat"), &[]);
        assert_eq!(c.get_app_fn(), &c);
    }

    #[test]
    fn test_get_app_fn_nested() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let c = Expr::mk_const(&Name::str("c"), &[]);
        let e = Expr::mk_app_n(&f, &[a, b, c]);
        assert_eq!(e.get_app_fn(), &f);
        assert_eq!(e.get_app_num_args(), 3);
    }

    #[test]
    fn test_get_app_args_order() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let e = Expr::mk_app_n(&f, &[a.clone(), b.clone()]);
        let args = e.get_app_args();
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], a);
        assert_eq!(args[1], b);
    }

    #[test]
    fn test_mk_app_n_empty() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let e = Expr::mk_app_n(&f, &[]);
        assert_eq!(e, f);
    }
}

// ============================================================================
// Update structural sharing tests
// ============================================================================

mod update_sharing {
    use super::*;

    #[test]
    fn test_update_app_same() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let app = Expr::mk_app(&f, &a);
        let same = app.update_app(app.app_fn(), app.app_arg());
        assert!(app.ptr_eq(&same));
    }

    #[test]
    fn test_update_binding_same() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        let same = lam.update_binding(lam.binding_domain(), lam.binding_body());
        assert!(lam.ptr_eq(&same));
    }

    #[test]
    fn test_update_sort_same() {
        let u = Level::mk_param(&Name::str("u"));
        let s = Expr::mk_sort(&u);
        let same = s.update_sort(s.sort_level());
        assert!(s.ptr_eq(&same));
    }

    #[test]
    fn test_update_const_same() {
        let u = Level::mk_param(&Name::str("u"));
        let c = Expr::mk_const(&Name::str("List"), &[u]);
        let same = c.update_const(c.const_levels());
        assert!(c.ptr_eq(&same));
    }

    #[test]
    fn test_update_let_same() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let zero = Expr::mk_const(&Name::str("Nat.zero"), &[]);
        let body = Expr::mk_bvar(0);
        let e = Expr::mk_let(&Name::str("x"), &nat, &zero, &body, false);
        let same = e.update_let(e.let_type(), e.let_value(), e.let_body());
        assert!(e.ptr_eq(&same));
    }

    #[test]
    fn test_update_mdata_same() {
        let inner = Expr::mk_const(&Name::str("Nat"), &[]);
        let md = Expr::mk_mdata(&inner);
        let same = md.update_mdata(md.mdata_expr());
        assert!(md.ptr_eq(&same));
    }

    #[test]
    fn test_update_proj_same() {
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let p = Expr::mk_proj(&Name::str("Prod"), 0, &a);
        let same = p.update_proj(p.proj_expr());
        assert!(p.ptr_eq(&same));
    }
}

// ============================================================================
// Depth tests
// ============================================================================

mod depth {
    use super::*;

    #[test]
    fn test_atomic_depth_zero() {
        assert_eq!(Expr::mk_const(&Name::str("Nat"), &[]).approx_depth(), 0);
        assert_eq!(Expr::mk_bvar(0).approx_depth(), 0);
        assert_eq!(Expr::mk_fvar(&Name::str("x")).approx_depth(), 0);
        assert_eq!(Expr::mk_lit(Literal::Nat(42)).approx_depth(), 0);
    }

    #[test]
    fn test_app_depth() {
        let f = Expr::mk_const(&Name::str("f"), &[]);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let app = Expr::mk_app(&f, &a);
        assert_eq!(app.approx_depth(), 1);
        let app2 = Expr::mk_app(&app, &a);
        assert_eq!(app2.approx_depth(), 2);
    }

    #[test]
    fn test_lambda_depth() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        assert_eq!(lam.approx_depth(), 1);
    }

    #[test]
    fn test_nested_depth() {
        let nat = Expr::mk_const(&Name::str("Nat"), &[]);
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat, &body);
        let app = Expr::mk_app(&lam, &nat);
        assert_eq!(app.approx_depth(), 2);
    }

    #[test]
    fn test_depth_clamped_at_255() {
        // Build deeply nested expression
        let mut e = Expr::mk_const(&Name::str("x"), &[]);
        for _ in 0..300 {
            e = Expr::mk_mdata(&e);
        }
        assert_eq!(e.approx_depth(), 255);
    }
}
