//! Simp tactic — bottom-up rewriting with lemma database.

use std::collections::HashMap;

use crate::debruijn::*;
use crate::env::*;
use crate::expr::*;
use crate::level::Level;
use crate::name::Name;
use crate::type_checker::TypeChecker;
use crate::local_ctx::LocalContext;

// ============================================================================
// Simp Lemma DB
// ============================================================================

#[derive(Clone, Debug)]
pub struct SimpLemma {
    pub name: Name,
    pub lhs: Expr,  // left-hand side of the equality
    pub rhs: Expr,  // right-hand side
}

#[derive(Clone, Debug, Default)]
pub struct SimpDb {
    /// Head constant → list of simp lemmas
    lemmas: HashMap<String, Vec<SimpLemma>>,
}

impl SimpDb {
    pub fn new() -> Self { Self::default() }

    pub fn add(&mut self, name: Name, lhs: Expr, rhs: Expr) {
        let head = lhs.get_app_fn().to_string();
        self.lemmas.entry(head).or_default().push(SimpLemma { name, lhs, rhs });
    }

    pub fn lookup(&self, head: &str) -> &[SimpLemma] {
        self.lemmas.get(head).map_or(&[], |v| v.as_slice())
    }

    pub fn len(&self) -> usize {
        self.lemmas.values().map(|v| v.len()).sum()
    }

    /// Build simp DB from environment by scanning for known simp lemmas.
    /// This is a heuristic — we look for equalities that are likely @[simp].
    pub fn from_env(env: &Environment) -> Self {
        let mut db = SimpDb::new();
        // Hardcode the most common simp lemmas from Init
        let known_simp: &[&str] = &[
            "Nat.zero_add", "Nat.add_zero", "Nat.succ_add", "Nat.add_succ",
            "Nat.zero_mul", "Nat.mul_zero", "Nat.one_mul", "Nat.mul_one",
            "Nat.add_comm", "Nat.add_assoc", "Nat.mul_comm", "Nat.mul_assoc",
            "Bool.true_and", "Bool.and_true", "Bool.false_and", "Bool.and_false",
            "Bool.true_or", "Bool.or_true", "Bool.false_or", "Bool.or_false",
            "Bool.not_not", "Bool.not_true", "Bool.not_false",
            "List.nil_append", "List.append_nil",
            "List.length_nil", "List.length_cons",
            "Eq.mpr_refl", "if_true", "if_false",
            "and_true", "true_and", "and_false", "false_and",
            "or_true", "true_or", "or_false", "false_or",
            "not_true", "not_false", "not_not",
            "ite_true", "ite_false",
        ];
        for &lemma_name in known_simp {
            if let Some(info) = env.find(&Name::str(lemma_name)) {
                // Try to extract LHS and RHS from the type
                // Type should be: ∀ ..., LHS = RHS  or  ∀ ..., LHS ↔ RHS
                if let Some((lhs, rhs)) = extract_eq_sides(&info.type_) {
                    db.add(Name::str(lemma_name), lhs, rhs);
                }
            }
        }
        db
    }
}

/// Extract LHS and RHS from an equality type: `∀ ..., LHS = RHS`
pub fn extract_eq_sides(ty: &Expr) -> Option<(Expr, Expr)> {
    let mut e = ty.clone();
    // Skip foralls
    while e.is_pi() {
        e = e.binding_body().clone();
    }
    // Check for Eq application: App(App(App(Eq, _type), lhs), rhs)
    let fn_ = e.get_app_fn();
    if fn_.is_const() {
        let name = fn_.const_name().to_string();
        if name == "Eq" {
            let args = e.get_app_args();
            if args.len() == 3 {
                return Some((args[1].clone(), args[2].clone()));
            }
        }
        if name == "Iff" {
            let args = e.get_app_args();
            if args.len() == 2 {
                return Some((args[0].clone(), args[1].clone()));
            }
        }
    }
    None
}

// ============================================================================
// Simp algorithm
// ============================================================================

/// Try to simplify an expression using the simp DB.
/// Returns Some((simplified, proof)) if simplification happened.
pub fn simp_expr(
    e: &Expr,
    db: &SimpDb,
    tc: &mut TypeChecker,
) -> Option<Expr> {
    // Bottom-up: first simplify children
    let simplified = simp_children(e, db, tc);
    let e = simplified.as_ref().unwrap_or(e);

    // Try matching simp lemmas against the current expression
    let head = e.get_app_fn().to_string();
    for lemma in db.lookup(&head) {
        // Simple syntactic match: if e == lemma.lhs, return lemma.rhs
        // TODO: proper unification-based matching
        if exprs_match(e, &lemma.lhs) {
            return Some(lemma.rhs.clone());
        }
    }

    simplified
}

fn simp_children(e: &Expr, db: &SimpDb, tc: &mut TypeChecker) -> Option<Expr> {
    match e.kind() {
        ExprKind::App => {
            let new_fn = simp_expr(e.app_fn(), db, tc);
            let new_arg = simp_expr(e.app_arg(), db, tc);
            if new_fn.is_some() || new_arg.is_some() {
                let f = new_fn.as_ref().unwrap_or(e.app_fn());
                let a = new_arg.as_ref().unwrap_or(e.app_arg());
                Some(Expr::mk_app(f, a))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Simple syntactic expression matching (no unification).
fn exprs_match(e: &Expr, pattern: &Expr) -> bool {
    // BVars in pattern act as wildcards (they were universally quantified)
    if pattern.is_bvar() { return true; }
    if e.kind() != pattern.kind() { return false; }
    if e == pattern { return true; }
    match (e.kind(), pattern.kind()) {
        (ExprKind::Const, ExprKind::Const) => e.const_name() == pattern.const_name(),
        (ExprKind::App, ExprKind::App) => {
            exprs_match(e.app_fn(), pattern.app_fn()) &&
            exprs_match(e.app_arg(), pattern.app_arg())
        }
        (ExprKind::Lit, ExprKind::Lit) => e.lit_value() == pattern.lit_value(),
        _ => false,
    }
}

// ============================================================================
// Rewrite tactic
// ============================================================================

/// Rewrite: find `lhs` in `goal` and replace with `rhs`.
pub fn rewrite_expr(goal: &Expr, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    if exprs_match(goal, lhs) {
        return Some(rhs.clone());
    }
    match goal.kind() {
        ExprKind::App => {
            let new_fn = rewrite_expr(goal.app_fn(), lhs, rhs);
            let new_arg = rewrite_expr(goal.app_arg(), lhs, rhs);
            if new_fn.is_some() || new_arg.is_some() {
                let f = new_fn.as_ref().unwrap_or(goal.app_fn());
                let a = new_arg.as_ref().unwrap_or(goal.app_arg());
                Some(Expr::mk_app(f, a))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simp_db_add() {
        let mut db = SimpDb::new();
        let lhs = Expr::mk_app(
            &Expr::mk_app(
                &Expr::mk_const(&Name::str("HAdd.hAdd"), &[]),
                &Expr::mk_lit(Literal::Nat(0)),
            ),
            &Expr::mk_bvar(0),
        );
        let rhs = Expr::mk_bvar(0);
        db.add(Name::str("zero_add"), lhs, rhs);
        assert_eq!(db.len(), 1);
    }

    #[test]
    fn test_exprs_match() {
        let a = Expr::mk_const(&Name::str("Nat"), &[]);
        let b = Expr::mk_const(&Name::str("Nat"), &[]);
        assert!(exprs_match(&a, &b));

        // BVar in pattern = wildcard
        let pat = Expr::mk_bvar(0);
        assert!(exprs_match(&a, &pat));
    }
}
