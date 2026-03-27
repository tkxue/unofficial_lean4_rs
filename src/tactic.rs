//! Stage 51: Tactic evaluation — turns `by` blocks into proof terms.

use crate::debruijn::*;
use crate::elaborator::{ElabError, Elaborator, MetavarContext};
use crate::env::{Environment, ConstantInfoKind};
use crate::expr::*;
use crate::level::Level;
use crate::local_ctx::LocalContext;
use crate::name::Name;
use crate::syntax::Syntax;
use crate::type_checker::TypeChecker;

/// Evaluate a `by` tactic block and produce a proof term.
pub fn eval_by(
    elab: &mut Elaborator,
    tactic_tokens: &[Syntax],
    goal_type: &Expr,
) -> Result<Expr, ElabError> {
    let goal_name = Name::mk_numeral(&Name::mk_string(&Name::anonymous(), "_goal"), 0);
    elab.mctx.mk_fresh_mvar_named(goal_name.clone(), goal_type.clone(), &elab.lctx);

    let mut goals = vec![goal_name.clone()];

    // Parse and evaluate tactics
    let tactics = parse_tactic_seq(tactic_tokens);
    for tac in &tactics {
        if goals.is_empty() { break; }
        eval_tactic(elab, tac, &mut goals)?;
    }

    // Extract proof from mvar assignments
    let proof = elab.mctx.instantiate_mvars(&Expr::mk_mvar(&goal_name));
    if proof.has_expr_mvar() {
        // Try trivial closing on remaining goals
        for g in &goals {
            try_trivial_close(elab, g);
        }
        let proof = elab.mctx.instantiate_mvars(&Expr::mk_mvar(&goal_name));
        if proof.has_expr_mvar() {
            return Err(ElabError(format!("unsolved goals: {}", goals.len())));
        }
        return Ok(proof);
    }
    Ok(proof)
}

// ============================================================================
// Tactic parsing — extract tactic names + args from raw token list
// ============================================================================

#[derive(Debug)]
enum Tactic {
    Exact(Vec<Syntax>),        // exact <term>
    Apply(Vec<Syntax>),        // apply <term>
    Intro(Vec<Name>),          // intro x y z
    Intros,                    // intros
    Rfl,                       // rfl
    Trivial,                   // trivial
    Assumption,                // assumption
    Constructor,               // constructor
    Contradiction,             // contradiction
    Simp(Vec<Syntax>),         // simp [lemmas]
    Rw(Vec<Syntax>),           // rw [lemmas]
    Have(Name, Vec<Syntax>, Vec<Syntax>), // have h : T := e
    Show(Vec<Syntax>),         // show T
    AllGoals(Box<Tactic>),     // <;> tactic
    Focus(Vec<Tactic>),        // · tactic seq
    Cases(Vec<Syntax>),          // cases h
    Induction(Vec<Syntax>),      // induction n
    Unknown(String),
}

fn parse_tactic_seq(tokens: &[Syntax]) -> Vec<Tactic> {
    let mut tactics = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        let tok_str = match &tokens[i] {
            Syntax::Atom { val, .. } => val.clone(),
            Syntax::Ident { val, .. } => val.to_string(),
            _ => { i += 1; continue; }
        };
        // Strip debug formatting if present
        let word = tok_str.trim_start_matches("Ident(Name(").trim_end_matches("))");
        let word = word.trim_start_matches("Keyword(\"").trim_end_matches("\")");
        let word = word.trim_start_matches("Symbol(\"").trim_end_matches("\")");

        match word {
            "exact" => {
                i += 1;
                let args = collect_until_tactic(&tokens[i..]);
                let n = args.len();
                tactics.push(Tactic::Exact(args));
                i += n;
            }
            "apply" => {
                i += 1;
                let args = collect_until_tactic(&tokens[i..]);
                let n = args.len();
                tactics.push(Tactic::Apply(args));
                i += n;
            }
            "intro" => {
                i += 1;
                let mut names = Vec::new();
                while i < tokens.len() {
                    if let Some(n) = extract_ident_name(&tokens[i]) {
                        if is_tactic_keyword(&n) { break; }
                        names.push(Name::str(&n));
                        i += 1;
                    } else { break; }
                }
                if names.is_empty() { names.push(Name::str("_h")); }
                tactics.push(Tactic::Intro(names));
            }
            "intros" => { i += 1; tactics.push(Tactic::Intros); }
            "rfl" => { i += 1; tactics.push(Tactic::Rfl); }
            "trivial" => { i += 1; tactics.push(Tactic::Trivial); }
            "assumption" => { i += 1; tactics.push(Tactic::Assumption); }
            "constructor" => { i += 1; tactics.push(Tactic::Constructor); }
            "contradiction" => { i += 1; tactics.push(Tactic::Contradiction); }
            "simp" => {
                i += 1;
                let args = collect_until_tactic(&tokens[i..]);
                let n = args.len();
                tactics.push(Tactic::Simp(args));
                i += n;
            }
            "rw" => {
                i += 1;
                let args = collect_until_tactic(&tokens[i..]);
                let n = args.len();
                tactics.push(Tactic::Rw(args));
                i += n;
            }
            "have" => {
                i += 1;
                let args = collect_until_tactic(&tokens[i..]);
                let n = args.len();
                // Parse: have h : T := proof ; body
                // Simplified: treat entire rest as exact
                tactics.push(Tactic::Exact(args));
                i += n;
            }
            "cases" => {
                i += 1;
                let args = collect_until_tactic(&tokens[i..]);
                let n = args.len();
                tactics.push(Tactic::Cases(args));
                i += n;
            }
            "induction" => {
                i += 1;
                let args = collect_until_tactic(&tokens[i..]);
                let n = args.len();
                tactics.push(Tactic::Induction(args));
                i += n;
            }
            ";" | "<;>" => { i += 1; } // sequence separator, skip
            _ => { i += 1; } // unknown, skip
        }
    }
    tactics
}

fn collect_until_tactic(tokens: &[Syntax]) -> Vec<Syntax> {
    let mut args = Vec::new();
    for t in tokens {
        if let Some(name) = extract_ident_name(t) {
            if is_tactic_keyword(&name) { break; }
        }
        // Check for ; separator
        if let Syntax::Atom { val, .. } = t {
            if val.contains("Symbol(\";\"") || val.contains("Symbol(\"<;>\"") { break; }
        }
        args.push(t.clone());
    }
    args
}

fn extract_ident_name(stx: &Syntax) -> Option<String> {
    match stx {
        Syntax::Ident { val, .. } => Some(val.to_string()),
        Syntax::Atom { val, .. } => {
            // Handle debug-formatted tokens from the `by` parser
            if val.starts_with("Ident(Name(") {
                Some(val.trim_start_matches("Ident(Name(").trim_end_matches("))").to_string())
            } else if val.starts_with("Keyword(\"") {
                Some(val.trim_start_matches("Keyword(\"").trim_end_matches("\")").to_string())
            } else {
                Some(val.clone())
            }
        }
        _ => None,
    }
}

fn is_tactic_keyword(s: &str) -> bool {
    matches!(s, "exact" | "apply" | "intro" | "intros" | "rfl" | "trivial"
        | "assumption" | "constructor" | "contradiction" | "simp" | "rw"
        | "have" | "let" | "show" | "cases" | "induction" | "calc")
}

// ============================================================================
// Tactic evaluation
// ============================================================================

fn eval_tactic(
    elab: &mut Elaborator,
    tac: &Tactic,
    goals: &mut Vec<Name>,
) -> Result<(), ElabError> {
    if goals.is_empty() { return Ok(()); }
    elab.sync_tc();
    let goal = goals[0].clone();
    let goal_type = elab.mctx.get_type(&goal)
        .ok_or_else(|| ElabError("goal not found".into()))?.clone();

    match tac {
        Tactic::Exact(args) => {
            // Elaborate the argument as a term with goal_type as expected
            if let Some(first) = args.first() {
                let term_name = extract_ident_name(first).unwrap_or_default();
                let proof = elab_tactic_term(elab, &term_name, &goal_type)?;
                elab.mctx.assign(&goal, proof);
                goals.remove(0);
            }
            Ok(())
        }
        Tactic::Apply(args) => {
            if let Some(first) = args.first() {
                let term_name = extract_ident_name(first).unwrap_or_default();
                let f = elab_tactic_term(elab, &term_name, &Expr::mk_type())?;
                // Try to apply f to the goal
                let f_applied = elab.insert_implicits(f.clone()).unwrap_or(f);
                elab.mctx.assign(&goal, f_applied);
                goals.remove(0);
            }
            Ok(())
        }
        Tactic::Intro(names) => {
            let mut cur_goal = goal;
            let mut cur_type = goal_type;
            for name in names {
                let whnf_type = elab.tc.whnf(&cur_type);
                if !whnf_type.is_pi() { break; }
                let domain = whnf_type.binding_domain().clone();
                let fvar = elab.lctx.mk_local_decl(
                    name.clone(), name.clone(), domain.clone(), whnf_type.binding_info(),
                );
                elab.res.push_local(name.clone());
                let new_goal_type = instantiate1(whnf_type.binding_body(), &fvar);
                let new_goal_name = Name::mk_numeral(
                    &Name::mk_string(&Name::anonymous(), "_goal"),
                    elab.mctx.next_id(),
                );
                elab.mctx.mk_fresh_mvar_named(new_goal_name.clone(), new_goal_type.clone(), &elab.lctx);
                // Assign current goal to lambda
                let lam = Expr::mk_lambda(name, whnf_type.binding_info(), &domain, &Expr::mk_mvar(&new_goal_name));
                elab.mctx.assign(&cur_goal, lam);
                cur_goal = new_goal_name;
                cur_type = new_goal_type;
            }
            goals[0] = cur_goal;
            Ok(())
        }
        Tactic::Intros => {
            let mut cur_goal = goal;
            let mut cur_type = goal_type;
            let mut count = 0;
            loop {
                let whnf_type = elab.tc.whnf(&cur_type);
                if !whnf_type.is_pi() || count > 100 { break; }
                let name = Name::mk_numeral(&Name::mk_string(&Name::anonymous(), "_a"), count);
                let domain = whnf_type.binding_domain().clone();
                let fvar = elab.lctx.mk_local_decl(
                    name.clone(), name.clone(), domain.clone(), whnf_type.binding_info(),
                );
                elab.res.push_local(name.clone());
                let new_goal_type = instantiate1(whnf_type.binding_body(), &fvar);
                let new_goal_name = Name::mk_numeral(
                    &Name::mk_string(&Name::anonymous(), "_goal"),
                    elab.mctx.next_id(),
                );
                elab.mctx.mk_fresh_mvar_named(new_goal_name.clone(), new_goal_type.clone(), &elab.lctx);
                let lam = Expr::mk_lambda(&name, whnf_type.binding_info(), &domain, &Expr::mk_mvar(&new_goal_name));
                elab.mctx.assign(&cur_goal, lam);
                cur_goal = new_goal_name;
                cur_type = new_goal_type;
                count += 1;
            }
            goals[0] = cur_goal;
            Ok(())
        }
        Tactic::Rfl => {
            // Goal should be `Eq a a` → proof is `Eq.refl a`
            let refl = Expr::mk_const(&Name::str("Eq.refl"), &[Level::mk_param(&Name::str("_u"))]);
            let refl_applied = elab.insert_implicits(refl.clone()).unwrap_or(refl);
            elab.mctx.assign(&goal, refl_applied);
            goals.remove(0);
            Ok(())
        }
        Tactic::Trivial => {
            try_trivial_close(elab, &goal);
            if elab.mctx.is_assigned(&goal) {
                goals.remove(0);
            }
            Ok(())
        }
        Tactic::Assumption => {
            // Search local context for term matching goal type
            let mut found = false;
            for local_name in &elab.res.locals {
                if let Some(decl) = elab.lctx.find(local_name) {
                    let local_type = decl.get_type();
                    if elab.tc.is_def_eq(local_type, &goal_type) {
                        elab.mctx.assign(&goal, Expr::mk_fvar(local_name));
                        goals.remove(0);
                        found = true;
                        break;
                    }
                }
            }
            if !found {
                return Err(ElabError("assumption failed: no matching hypothesis".into()));
            }
            Ok(())
        }
        Tactic::Constructor => {
            // Get goal type's head constant, find its first constructor
            let whnf_goal = elab.tc.whnf(&goal_type);
            let head = whnf_goal.get_app_fn();
            if head.is_const() {
                if let Some(info) = elab.env.find(head.const_name()) {
                    if let ConstantInfoKind::Inductive { ctors, .. } = &info.kind {
                        if let Some(ctor_name) = ctors.first() {
                            let ctor = Expr::mk_const(ctor_name, head.const_levels());
                            let applied = elab.insert_implicits(ctor.clone()).unwrap_or(ctor);
                            elab.mctx.assign(&goal, applied);
                            goals.remove(0);
                        }
                    }
                }
            }
            Ok(())
        }
        Tactic::Simp(_) => {
            // Build simp DB and try to simplify the goal
            let db = crate::simp::SimpDb::from_env(&elab.env);
            elab.sync_tc();
            if let Some(simplified) = crate::simp::simp_expr(&goal_type, &db, &mut elab.tc) {
                // If simplified to True, close with True.intro
                let whnf_simplified = elab.tc.whnf(&simplified);
                if whnf_simplified.is_const() && whnf_simplified.const_name() == &Name::str("True") {
                    elab.mctx.assign(&goal, Expr::mk_const(&Name::str("True.intro"), &[]));
                    goals.remove(0);
                } else {
                    // Replace goal type with simplified version
                    // For now: just try trivial close
                    try_trivial_close(elab, &goal);
                    if elab.mctx.is_assigned(&goal) { goals.remove(0); }
                }
            } else {
                try_trivial_close(elab, &goal);
                if elab.mctx.is_assigned(&goal) { goals.remove(0); }
            }
            Ok(())
        }
        Tactic::Rw(args) => {
            // rw [h] — find h's equality, rewrite goal
            if let Some(first) = args.first() {
                let term_name = extract_ident_name(first).unwrap_or_default();
                if let Ok(h_expr) = elab_tactic_term(elab, &term_name, &Expr::mk_type()) {
                    elab.sync_tc();
                    let h_type = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        elab.tc.infer_type(&h_expr)
                    })) {
                        Ok(ty) => ty,
                        Err(_) => return Ok(()),
                    };
                    // Extract LHS/RHS from h_type (should be Eq _ lhs rhs)
                    if let Some((lhs, rhs)) = crate::simp::extract_eq_sides(&h_type) {
                        if let Some(new_goal) = crate::simp::rewrite_expr(&goal_type, &lhs, &rhs) {
                            // Create new goal for the rewritten type
                            let new_goal_name = Name::mk_numeral(
                                &Name::mk_string(&Name::anonymous(), "_goal"),
                                elab.mctx.next_id(),
                            );
                            elab.mctx.mk_fresh_mvar_named(new_goal_name.clone(), new_goal, &elab.lctx);
                            // Close current goal with Eq.mpr proof (simplified: just assign)
                            elab.mctx.assign(&goal, Expr::mk_mvar(&new_goal_name));
                            goals[0] = new_goal_name;
                        }
                    }
                }
            }
            Ok(())
        }
        Tactic::Cases(_) | Tactic::Induction(_) => {
            // Simplified: try trivial close or constructor
            try_trivial_close(elab, &goal);
            if elab.mctx.is_assigned(&goal) { goals.remove(0); }
            Ok(())
        }
        _ => Ok(()), // skip unknown tactics
    }
}

fn try_trivial_close(elab: &mut Elaborator, goal: &Name) {
    if elab.mctx.is_assigned(goal) { return; }
    let goal_type = match elab.mctx.get_type(goal) {
        Some(t) => t.clone(),
        None => return,
    };
    // Try True.intro
    let true_const = Name::str("True");
    let whnf = elab.tc.whnf(&goal_type);
    if whnf.is_const() && whnf.const_name() == &true_const {
        elab.mctx.assign(goal, Expr::mk_const(&Name::str("True.intro"), &[]));
        return;
    }
    // Try rfl (Eq.refl)
    if whnf.get_app_fn().is_const() && whnf.get_app_fn().const_name() == &Name::str("Eq") {
        let refl = Expr::mk_const(&Name::str("Eq.refl"), &[Level::mk_param(&Name::str("_u"))]);
        let applied = elab.insert_implicits(refl.clone()).unwrap_or(refl);
        elab.mctx.assign(goal, applied);
        return;
    }
}

fn elab_tactic_term(elab: &mut Elaborator, name: &str, expected: &Expr) -> Result<Expr, ElabError> {
    // Try local first
    for local in &elab.res.locals {
        if local.to_string() == name {
            return Ok(Expr::mk_fvar(local));
        }
    }
    // Try constant
    let resolved = crate::resolve::resolve_name(&Name::str(name), &elab.res, &elab.env)
        .map_err(|e| ElabError(format!("{}", e)))?;
    let info = elab.env.get(&resolved);
    let levels: Vec<Level> = info.lparams.iter()
        .map(|_| Level::mk_param(&Name::mk_numeral(&Name::mk_string(&Name::anonymous(), "_u"), 0)))
        .collect();
    Ok(Expr::mk_const(&resolved, &levels))
}
