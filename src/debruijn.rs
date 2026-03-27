//! Stage 02: De Bruijn operations — replace, for_each, instantiate, abstract,
//! lift/lower loose bvars, beta reduction, universe parameter instantiation.

use crate::expr::{Expr, ExprKind, BinderInfo, Literal};
use crate::level::Level;
use crate::name::Name;

// ============================================================================
// replace — generic expression traversal with replacement
// ============================================================================

/// Generic `replace(e, f)` matching C++ `replace_rec_fn`.
///
/// `f(e, offset)` is called for each subexpression. If it returns `Some(r)`,
/// `r` is used in place of `e`. If `None`, children are recursed into.
/// `offset` counts the number of binders traversed (Lambda/Pi/Let bodies).
pub fn replace(e: &Expr, f: &mut impl FnMut(&Expr, u32) -> Option<Expr>) -> Expr {
    fn go(e: &Expr, offset: u32, f: &mut impl FnMut(&Expr, u32) -> Option<Expr>) -> Expr {
        if let Some(r) = f(e, offset) {
            return r;
        }
        match e.kind() {
            ExprKind::Const | ExprKind::Sort | ExprKind::BVar
            | ExprKind::Lit | ExprKind::MVar | ExprKind::FVar => e.clone(),
            ExprKind::MData => {
                let ne = go(e.mdata_expr(), offset, f);
                e.update_mdata(&ne)
            }
            ExprKind::Proj => {
                let ne = go(e.proj_expr(), offset, f);
                e.update_proj(&ne)
            }
            ExprKind::App => {
                let nf = go(e.app_fn(), offset, f);
                let na = go(e.app_arg(), offset, f);
                e.update_app(&nf, &na)
            }
            ExprKind::Lambda | ExprKind::Pi => {
                let nd = go(e.binding_domain(), offset, f);
                let nb = go(e.binding_body(), offset + 1, f);
                e.update_binding(&nd, &nb)
            }
            ExprKind::Let => {
                let nt = go(e.let_type(), offset, f);
                let nv = go(e.let_value(), offset, f);
                let nb = go(e.let_body(), offset + 1, f);
                e.update_let(&nt, &nv, &nb)
            }
        }
    }
    go(e, 0, f)
}

/// Simpler `replace` without offset (used by `instantiate_lparams`).
pub fn replace_no_offset(e: &Expr, f: &mut impl FnMut(&Expr) -> Option<Expr>) -> Expr {
    fn go(e: &Expr, f: &mut impl FnMut(&Expr) -> Option<Expr>) -> Expr {
        if let Some(r) = f(e) {
            return r;
        }
        match e.kind() {
            ExprKind::Const | ExprKind::Sort | ExprKind::BVar
            | ExprKind::Lit | ExprKind::MVar | ExprKind::FVar => e.clone(),
            ExprKind::MData => {
                let ne = go(e.mdata_expr(), f);
                e.update_mdata(&ne)
            }
            ExprKind::Proj => {
                let ne = go(e.proj_expr(), f);
                e.update_proj(&ne)
            }
            ExprKind::App => {
                let nf = go(e.app_fn(), f);
                let na = go(e.app_arg(), f);
                e.update_app(&nf, &na)
            }
            ExprKind::Lambda | ExprKind::Pi => {
                let nd = go(e.binding_domain(), f);
                let nb = go(e.binding_body(), f);
                e.update_binding(&nd, &nb)
            }
            ExprKind::Let => {
                let nt = go(e.let_type(), f);
                let nv = go(e.let_value(), f);
                let nb = go(e.let_body(), f);
                e.update_let(&nt, &nv, &nb)
            }
        }
    }
    go(e, f)
}

// ============================================================================
// for_each — generic expression traversal
// ============================================================================

/// Visit every subexpression. `f(e, offset)` returns true to recurse into children.
pub fn for_each(e: &Expr, f: &mut impl FnMut(&Expr, u32) -> bool) {
    fn go(e: &Expr, offset: u32, f: &mut impl FnMut(&Expr, u32) -> bool) {
        if !f(e, offset) {
            return;
        }
        match e.kind() {
            ExprKind::Const | ExprKind::Sort | ExprKind::BVar
            | ExprKind::Lit | ExprKind::MVar | ExprKind::FVar => {}
            ExprKind::MData => go(e.mdata_expr(), offset, f),
            ExprKind::Proj => go(e.proj_expr(), offset, f),
            ExprKind::App => {
                go(e.app_fn(), offset, f);
                go(e.app_arg(), offset, f);
            }
            ExprKind::Lambda | ExprKind::Pi => {
                go(e.binding_domain(), offset, f);
                go(e.binding_body(), offset + 1, f);
            }
            ExprKind::Let => {
                go(e.let_type(), offset, f);
                go(e.let_value(), offset, f);
                go(e.let_body(), offset + 1, f);
            }
        }
    }
    go(e, 0, f)
}

/// Find first subexpression satisfying `pred`.
pub fn find(e: &Expr, pred: &impl Fn(&Expr) -> bool) -> Option<Expr> {
    let mut result = None;
    for_each(e, &mut |sub, _| {
        if result.is_some() { return false; }
        if pred(sub) {
            result = Some(sub.clone());
            return false;
        }
        true
    });
    result
}

// ============================================================================
// lift_loose_bvars / lower_loose_bvars
// ============================================================================

/// Lift loose bound variables >= s by d. Matches C++ `lift_loose_bvars(e, s, d)`.
pub fn lift_loose_bvars(e: &Expr, s: u32, d: u32) -> Expr {
    if d == 0 || s >= e.loose_bvar_range() {
        return e.clone();
    }
    replace(e, &mut |m, offset| {
        let s1 = s.checked_add(offset)?; // overflow => skip
        if s1 >= m.loose_bvar_range() {
            return Some(m.clone());
        }
        if m.is_bvar() && m.bvar_idx() >= (s + offset) as u64 {
            return Some(Expr::mk_bvar(m.bvar_idx() + d as u64));
        }
        None
    })
}

/// `lift_loose_bvars(e, d)` = `lift_loose_bvars(e, 0, d)`
pub fn lift_loose_bvars_simple(e: &Expr, d: u32) -> Expr {
    lift_loose_bvars(e, 0, d)
}

/// Lower loose bound variables >= s by d. Matches C++ `lower_loose_bvars(e, s, d)`.
pub fn lower_loose_bvars(e: &Expr, s: u32, d: u32) -> Expr {
    if d == 0 || s >= e.loose_bvar_range() {
        return e.clone();
    }
    replace(e, &mut |m, offset| {
        let s1 = s.checked_add(offset)?;
        if s1 >= m.loose_bvar_range() {
            return Some(m.clone());
        }
        if m.is_bvar() && m.bvar_idx() >= s1 as u64 {
            return Some(Expr::mk_bvar(m.bvar_idx() - d as u64));
        }
        None
    })
}

/// `lower_loose_bvars(e, d)` = `lower_loose_bvars(e, d, d)`
pub fn lower_loose_bvars_simple(e: &Expr, d: u32) -> Expr {
    lower_loose_bvars(e, d, d)
}

/// `has_loose_bvar(e, i)` — checks if bvar `i` occurs in `e`.
pub fn has_loose_bvar(e: &Expr, i: u32) -> bool {
    let mut found = false;
    for_each(e, &mut |sub, offset| {
        if found { return false; }
        let n_i = match i.checked_add(offset) {
            Some(v) => v,
            None => return false, // overflow
        };
        if n_i >= sub.loose_bvar_range() { return false; }
        if sub.is_bvar() && sub.bvar_idx() == n_i as u64 {
            found = true;
        }
        true
    });
    found
}

// ============================================================================
// instantiate — bound variable substitution
// ============================================================================

/// `instantiate(e, s, n, subst)` — replace bvars s..s+n-1 with subst[0..n-1].
/// Bvars >= s+n are shifted down by n. Matches C++ `instantiate(a, s, n, subst)`.
pub fn instantiate_at(e: &Expr, s: u32, subst: &[Expr]) -> Expr {
    let n = subst.len() as u32;
    if s >= e.loose_bvar_range() || n == 0 {
        return e.clone();
    }
    replace(e, &mut |m, offset| {
        let s1 = match s.checked_add(offset) {
            Some(v) => v,
            None => return Some(m.clone()), // overflow
        };
        if s1 >= m.loose_bvar_range() {
            return Some(m.clone());
        }
        if m.is_bvar() {
            let vidx = m.bvar_idx();
            if vidx >= s1 as u64 {
                let h = s1 as u64 + n as u64;
                if vidx < h {
                    let sub = &subst[(vidx - s1 as u64) as usize];
                    return Some(lift_loose_bvars_simple(sub, offset));
                } else {
                    return Some(Expr::mk_bvar(vidx - n as u64));
                }
            }
        }
        None
    })
}

/// `instantiate(e, subst)` — replace bvars 0..n-1.
pub fn instantiate(e: &Expr, subst: &[Expr]) -> Expr {
    instantiate_at(e, 0, subst)
}

/// `instantiate1(e, v)` — replace bvar 0 with v.
pub fn instantiate1(e: &Expr, v: &Expr) -> Expr {
    instantiate(e, &[v.clone()])
}

/// `instantiate_rev(e, subst)` — like instantiate but array is reversed.
/// bvar i maps to subst[n - i - 1] (for i in 0..n-1).
pub fn instantiate_rev(e: &Expr, subst: &[Expr]) -> Expr {
    let n = subst.len();
    if !e.has_loose_bvars() || n == 0 {
        return e.clone();
    }
    replace(e, &mut |m, offset| {
        if offset >= m.loose_bvar_range() {
            return Some(m.clone());
        }
        if m.is_bvar() {
            let vidx = m.bvar_idx();
            if vidx >= offset as u64 {
                let h = offset as u64 + n as u64;
                if vidx < h {
                    let idx = n - (vidx as usize - offset as usize) - 1;
                    return Some(lift_loose_bvars_simple(&subst[idx], offset));
                } else {
                    return Some(Expr::mk_bvar(vidx - n as u64));
                }
            }
        }
        None
    })
}

// ============================================================================
// abstract — free variable to bound variable
// ============================================================================

/// `abstract_expr(e, fvars)` — replace fvars[i] with bvar(n-i-1 + offset).
/// Matches C++ `abstract(e, n, subst)`.
pub fn abstract_expr(e: &Expr, fvars: &[Expr]) -> Expr {
    let n = fvars.len();
    if !e.has_fvar() || n == 0 {
        return e.clone();
    }
    replace(e, &mut |m, offset| {
        if !m.has_fvar() {
            return Some(m.clone());
        }
        if m.is_fvar() {
            let name = m.fvar_name();
            for i in (0..n).rev() {
                debug_assert!(fvars[i].is_fvar());
                if fvars[i].fvar_name() == name {
                    return Some(Expr::mk_bvar((offset as u64) + (n - i - 1) as u64));
                }
            }
            return None;
        }
        None
    })
}

/// Abstract a single free variable.
pub fn abstract1(e: &Expr, fvar: &Expr) -> Expr {
    abstract_expr(e, &[fvar.clone()])
}

/// Abstract by name.
pub fn abstract_name(e: &Expr, n: &Name) -> Expr {
    let fvar = Expr::mk_fvar(n);
    abstract_expr(e, &[fvar])
}

// ============================================================================
// Beta reduction
// ============================================================================

/// True if `e` is `App(Lambda(...), _)` at the head.
pub fn is_head_beta(e: &Expr) -> bool {
    e.is_app() && e.get_app_fn().is_lambda()
}

/// Head beta reduce: `(λx. body) arg` → `body[0 := arg]`, iteratively.
pub fn head_beta_reduce(e: &Expr) -> Expr {
    if !is_head_beta(e) {
        return e.clone();
    }
    let mut rev_args = Vec::new();
    let mut cur = e;
    while cur.is_app() {
        rev_args.push(cur.app_arg().clone());
        cur = cur.app_fn();
    }
    // cur is the head lambda
    let result = apply_beta(cur, &rev_args);
    head_beta_reduce(&result)
}

/// `apply_beta(f, rev_args)` — apply function f to reversed args with beta reduction.
/// Simplified version without preserve_data/zeta.
pub fn apply_beta(f: &Expr, rev_args: &[Expr]) -> Expr {
    if rev_args.is_empty() {
        return f.clone();
    }
    apply_beta_rec(f, 0, rev_args)
}

fn apply_beta_rec(e: &Expr, i: usize, rev_args: &[Expr]) -> Expr {
    if e.is_lambda() {
        if i + 1 < rev_args.len() {
            apply_beta_rec(e.binding_body(), i + 1, rev_args)
        } else {
            // All lambdas consumed: instantiate body with all rev_args (forward order).
            // C++: instantiate(binding_body(e), num_rev_args, rev_args)
            instantiate(e.binding_body(), rev_args)
        }
    } else {
        // Not enough lambdas. Remaining unapplied args are rev_args[0..n].
        let num_rev_args = rev_args.len();
        let n = num_rev_args - i;
        // C++: instantiate(e, i, rev_args + n) — substitutes bvars 0..i-1
        let body = instantiate(e, &rev_args[n..]);
        mk_rev_app(&body, &rev_args[..n])
    }
}

/// Build `App(App(...App(f, args[n-1])..., args[1]), args[0])` (args in reverse order).
fn mk_rev_app(f: &Expr, rev_args: &[Expr]) -> Expr {
    let mut e = f.clone();
    for a in rev_args.iter().rev() {
        e = Expr::mk_app(&e, a);
    }
    e
}

/// Cheap beta reduce: only reduce if the body after consuming all lambdas has
/// no loose bvars or is a single bvar.
pub fn cheap_beta_reduce(e: &Expr) -> Expr {
    if !e.is_app() { return e.clone(); }
    let head = e.get_app_fn();
    if !head.is_lambda() { return e.clone(); }

    let args = e.get_app_args();
    let mut fn_body = head.clone();
    let mut i = 0usize;
    while fn_body.is_lambda() && i < args.len() {
        fn_body = fn_body.binding_body().clone();
        i += 1;
    }
    if !fn_body.has_loose_bvars() {
        return Expr::mk_app_n(&fn_body, &args[i..]);
    } else if fn_body.is_bvar() {
        let idx = fn_body.bvar_idx() as usize;
        debug_assert!(idx < i);
        let replacement = &args[i - idx - 1];
        return Expr::mk_app_n(replacement, &args[i..]);
    }
    e.clone()
}

// ============================================================================
// Universe parameter instantiation
// ============================================================================

/// `instantiate_lparams(e, params, levels)` — substitute universe params in
/// Sort and Const nodes. Matches C++ `instantiate_lparams`.
pub fn instantiate_lparams(e: &Expr, params: &[Name], levels: &[Level]) -> Expr {
    if !e.has_univ_param() {
        return e.clone();
    }
    replace_no_offset(e, &mut |sub| {
        if !sub.has_univ_param() {
            return Some(sub.clone());
        }
        if sub.is_const() {
            let new_levels: Vec<Level> = sub.const_levels().iter()
                .map(|l| l.instantiate(params, levels))
                .collect();
            return Some(sub.update_const(&new_levels));
        }
        if sub.is_sort() {
            let new_level = sub.sort_level().instantiate(params, levels);
            return Some(sub.update_sort(&new_level));
        }
        None
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn nat() -> Expr { Expr::mk_const(&Name::str("Nat"), &[]) }
    fn zero() -> Expr { Expr::mk_const(&Name::str("Nat.zero"), &[]) }
    fn succ() -> Expr { Expr::mk_const(&Name::str("Nat.succ"), &[]) }
    fn fvar(s: &str) -> Expr { Expr::mk_fvar(&Name::str(s)) }

    // -- for_each -----------------------------------------------------------

    #[test]
    fn test_for_each_count() {
        let e = Expr::mk_app(&succ(), &zero());
        let mut count = 0;
        for_each(&e, &mut |_, _| { count += 1; true });
        // App(succ, zero) → 3 nodes
        assert_eq!(count, 3);
    }

    #[test]
    fn test_for_each_offset() {
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &body);
        let mut offsets = Vec::new();
        for_each(&lam, &mut |_, off| { offsets.push(off); true });
        // lam(offset=0), domain(0), body(1)
        assert_eq!(offsets, vec![0, 0, 1]);
    }

    #[test]
    fn test_for_each_early_stop() {
        let e = Expr::mk_app(&Expr::mk_app(&succ(), &zero()), &nat());
        let mut count = 0;
        for_each(&e, &mut |_, _| { count += 1; false }); // stop immediately
        assert_eq!(count, 1);
    }

    // -- find ---------------------------------------------------------------

    #[test]
    fn test_find() {
        let e = Expr::mk_app(&succ(), &zero());
        let found = find(&e, &|sub| sub.is_const() && sub.const_name() == &Name::str("Nat.zero"));
        assert!(found.is_some());
        assert_eq!(found.unwrap(), zero());
    }

    #[test]
    fn test_find_not_found() {
        let e = Expr::mk_app(&succ(), &zero());
        let found = find(&e, &|sub| sub.is_bvar());
        assert!(found.is_none());
    }

    // -- replace ------------------------------------------------------------

    #[test]
    fn test_replace_identity() {
        let e = Expr::mk_app(&succ(), &zero());
        let r = replace(&e, &mut |_, _| None);
        assert_eq!(r, e);
    }

    #[test]
    fn test_replace_swap() {
        // Replace Nat.zero with Nat.succ everywhere
        let e = Expr::mk_app(&succ(), &zero());
        let r = replace(&e, &mut |sub, _| {
            if sub.is_const() && sub.const_name() == &Name::str("Nat.zero") {
                Some(succ())
            } else {
                None
            }
        });
        assert_eq!(r.app_arg(), &succ());
    }

    // -- lift/lower ---------------------------------------------------------

    #[test]
    fn test_lift_bvar() {
        let b0 = Expr::mk_bvar(0);
        let lifted = lift_loose_bvars_simple(&b0, 3);
        assert_eq!(lifted.bvar_idx(), 3);
    }

    #[test]
    fn test_lift_no_bvars() {
        let c = nat();
        let lifted = lift_loose_bvars_simple(&c, 5);
        assert!(c.ptr_eq(&lifted)); // unchanged
    }

    #[test]
    fn test_lift_threshold() {
        let b3 = Expr::mk_bvar(3);
        // lift bvars >= 2 by 10
        let lifted = lift_loose_bvars(&b3, 2, 10);
        assert_eq!(lifted.bvar_idx(), 13);
        // lift bvars >= 5 by 10 — bvar 3 is below threshold
        let not_lifted = lift_loose_bvars(&b3, 5, 10);
        assert!(b3.ptr_eq(&not_lifted));
    }

    #[test]
    fn test_lower_bvar() {
        let b5 = Expr::mk_bvar(5);
        let lowered = lower_loose_bvars(&b5, 3, 3);
        assert_eq!(lowered.bvar_idx(), 2);
    }

    #[test]
    fn test_has_loose_bvar() {
        let e = Expr::mk_app(&Expr::mk_bvar(0), &Expr::mk_bvar(2));
        assert!(has_loose_bvar(&e, 0));
        assert!(!has_loose_bvar(&e, 1));
        assert!(has_loose_bvar(&e, 2));
    }

    // -- instantiate --------------------------------------------------------

    #[test]
    fn test_instantiate1_simple() {
        // #0 [0 := zero] → zero
        let b0 = Expr::mk_bvar(0);
        let r = instantiate1(&b0, &zero());
        assert_eq!(r, zero());
    }

    #[test]
    fn test_instantiate_no_bvars() {
        let c = nat();
        let r = instantiate1(&c, &zero());
        assert!(c.ptr_eq(&r)); // unchanged
    }

    #[test]
    fn test_instantiate_shifts_down() {
        // #3 with subst=[a] → #2 (shifted down by 1)
        let b3 = Expr::mk_bvar(3);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let r = instantiate(&b3, &[a]);
        assert!(r.is_bvar());
        assert_eq!(r.bvar_idx(), 2);
    }

    #[test]
    fn test_instantiate_in_app() {
        // App(#0, #1) with subst=[a, b] → App(a, b)
        let e = Expr::mk_app(&Expr::mk_bvar(0), &Expr::mk_bvar(1));
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let r = instantiate(&e, &[a.clone(), b.clone()]);
        assert_eq!(r.app_fn(), &a);
        assert_eq!(r.app_arg(), &b);
    }

    #[test]
    fn test_instantiate_under_binder() {
        // λx. #1 with subst=[a] → λx. a
        let body = Expr::mk_bvar(1);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &body);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let r = instantiate(&lam, &[a.clone()]);
        assert!(r.is_lambda());
        assert_eq!(r.binding_body(), &a); // #1 under one binder → subst[0] = a
    }

    #[test]
    fn test_instantiate_bvar0_in_binder_stays() {
        // λx. #0 with subst=[a] → λx. #0 (bvar 0 is bound by the lambda)
        let body = Expr::mk_bvar(0);
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &body);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let r = instantiate(&lam, &[a]);
        assert!(r.is_lambda());
        assert!(r.binding_body().is_bvar());
        assert_eq!(r.binding_body().bvar_idx(), 0);
    }

    // -- instantiate_rev ----------------------------------------------------

    #[test]
    fn test_instantiate_rev() {
        // #0 with rev_subst=[b, a] → a (index 0 maps to subst[n-0-1] = subst[1] = a)
        let b0 = Expr::mk_bvar(0);
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let r = instantiate_rev(&b0, &[b, a.clone()]);
        assert_eq!(r, a);
    }

    #[test]
    fn test_instantiate_rev_multi() {
        // App(#0, #1) with rev_subst=[b, a]:
        //   #0 → subst[2-0-1] = subst[1] = a
        //   #1 → subst[2-1-1] = subst[0] = b
        let e = Expr::mk_app(&Expr::mk_bvar(0), &Expr::mk_bvar(1));
        let a = Expr::mk_const(&Name::str("a"), &[]);
        let b = Expr::mk_const(&Name::str("b"), &[]);
        let r = instantiate_rev(&e, &[b.clone(), a.clone()]);
        assert_eq!(r.app_fn(), &a);
        assert_eq!(r.app_arg(), &b);
    }

    // -- abstract -----------------------------------------------------------

    #[test]
    fn test_abstract_single() {
        let x = fvar("x");
        let e = Expr::mk_app(&succ(), &x);
        let r = abstract1(&e, &x);
        // succ(x) → succ(#0)
        assert!(r.app_arg().is_bvar());
        assert_eq!(r.app_arg().bvar_idx(), 0);
    }

    #[test]
    fn test_abstract_no_fvars() {
        let e = Expr::mk_app(&succ(), &zero());
        let x = fvar("x");
        let r = abstract1(&e, &x);
        assert!(e.ptr_eq(&r)); // unchanged
    }

    #[test]
    fn test_abstract_multiple() {
        // abstract [x, y] over App(x, y)
        let x = fvar("x");
        let y = fvar("y");
        let e = Expr::mk_app(&x, &y);
        let r = abstract_expr(&e, &[x.clone(), y.clone()]);
        // x → bvar(offset + n - 0 - 1) = bvar(0 + 2 - 0 - 1) = bvar(1)
        // y → bvar(offset + n - 1 - 1) = bvar(0 + 2 - 1 - 1) = bvar(0)
        assert!(r.app_fn().is_bvar());
        assert_eq!(r.app_fn().bvar_idx(), 1);
        assert!(r.app_arg().is_bvar());
        assert_eq!(r.app_arg().bvar_idx(), 0);
    }

    #[test]
    fn test_abstract_instantiate_roundtrip() {
        let x = fvar("x");
        let y = fvar("y");
        let e = Expr::mk_app(&Expr::mk_app(&succ(), &x), &y);
        let abst = abstract_expr(&e, &[x.clone(), y.clone()]);
        // abstract [x,y] assigns x→#1, y→#0
        // so instantiate with [y, x] (bvar0→y, bvar1→x) recovers original
        let back = instantiate(&abst, &[y.clone(), x.clone()]);
        assert_eq!(back, e);
    }

    // -- beta reduction -----------------------------------------------------

    #[test]
    fn test_is_head_beta() {
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
        let app = Expr::mk_app(&lam, &zero());
        assert!(is_head_beta(&app));
        assert!(!is_head_beta(&zero()));
    }

    #[test]
    fn test_head_beta_reduce_identity() {
        // (λx. x) a → a
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
        let app = Expr::mk_app(&lam, &zero());
        let r = head_beta_reduce(&app);
        assert_eq!(r, zero());
    }

    #[test]
    fn test_head_beta_reduce_const() {
        // (λx. Nat) a → Nat
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &nat());
        let app = Expr::mk_app(&lam, &zero());
        let r = head_beta_reduce(&app);
        assert_eq!(r, nat());
    }

    #[test]
    fn test_head_beta_nested() {
        // (λx. λy. x) a b → a
        let inner = Expr::mk_lambda(&Name::str("y"), BinderInfo::Default, &nat(), &Expr::mk_bvar(1));
        let outer = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &inner);
        let app1 = Expr::mk_app(&outer, &zero());
        let app2 = Expr::mk_app(&app1, &nat());
        let r = head_beta_reduce(&app2);
        assert_eq!(r, zero());
    }

    #[test]
    fn test_head_beta_no_reduction() {
        let e = Expr::mk_app(&succ(), &zero());
        let r = head_beta_reduce(&e);
        assert_eq!(r, e);
    }

    #[test]
    fn test_cheap_beta_reduce_simple() {
        // (λx. Nat) a → Nat (body has no loose bvars)
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &nat());
        let app = Expr::mk_app(&lam, &zero());
        let r = cheap_beta_reduce(&app);
        assert_eq!(r, nat());
    }

    #[test]
    fn test_cheap_beta_bvar_body() {
        // (λx. x) a → a (body is single bvar)
        let lam = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
        let app = Expr::mk_app(&lam, &zero());
        let r = cheap_beta_reduce(&app);
        assert_eq!(r, zero());
    }

    // -- instantiate_lparams ------------------------------------------------

    #[test]
    fn test_instantiate_lparams_sort() {
        let u = Level::mk_param(&Name::str("u"));
        let e = Expr::mk_sort(&u);
        let one = Level::one();
        let r = instantiate_lparams(&e, &[Name::str("u")], &[one.clone()]);
        assert_eq!(r.sort_level(), &one);
    }

    #[test]
    fn test_instantiate_lparams_const() {
        let u = Level::mk_param(&Name::str("u"));
        let e = Expr::mk_const(&Name::str("List"), &[u]);
        let two = Level::mk_succ_n(&Level::zero(), 2);
        let r = instantiate_lparams(&e, &[Name::str("u")], &[two.clone()]);
        assert_eq!(r.const_levels()[0], two);
    }

    #[test]
    fn test_instantiate_lparams_no_params() {
        let e = Expr::mk_const(&Name::str("Nat"), &[]);
        let r = instantiate_lparams(&e, &[Name::str("u")], &[Level::one()]);
        assert!(e.ptr_eq(&r)); // unchanged
    }

    #[test]
    fn test_instantiate_lparams_nested() {
        // App(Const("f", [u]), Sort(u)) with u := 1
        let u = Level::mk_param(&Name::str("u"));
        let f = Expr::mk_const(&Name::str("f"), &[u.clone()]);
        let s = Expr::mk_sort(&u);
        let e = Expr::mk_app(&f, &s);
        let one = Level::one();
        let r = instantiate_lparams(&e, &[Name::str("u")], &[one.clone()]);
        assert_eq!(r.app_fn().const_levels()[0], one);
        assert_eq!(r.app_arg().sort_level(), &one);
    }
}
