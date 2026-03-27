//! End-to-end .lean interpretation tests.
//! Loads Init once, then tests many snippets.

use std::path::PathBuf;
use std::sync::OnceLock;
use lean4_kernel::env::Environment;
use lean4_kernel::name::Name;
use lean4_kernel::elaborator::Elaborator;
use lean4_kernel::parser::parse_file;

const LEAN_LIB: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean";

static INIT_ENV: OnceLock<Environment> = OnceLock::new();

fn get_init_env() -> &'static Environment {
    INIT_ENV.get_or_init(|| {
        let sp = vec![PathBuf::from(LEAN_LIB)];
        lean4_kernel::olean_fast::load_module_tree_fast(&Name::str("Init"), &sp)
            .unwrap().env
    })
}

fn interpret(src: &str) -> Environment {
    let env = get_init_env().clone();
    let (_, _, commands) = parse_file(src);
    let mut elab = Elaborator::new(env);
    for cmd in &commands {
        if let Err(e) = elab.elab_command(cmd) {
            eprintln!("  elab error: {}", e);
        }
    }
    elab.env
}

fn has_const(env: &Environment, name: &str) -> bool {
    env.find(&Name::str(name)).is_some()
}

// ============================================================================
// Basic definitions
// ============================================================================

#[test]
fn test_def_literal() {
    let env = interpret("def myZero := 0");
    assert!(has_const(&env, "myZero"), "myZero not found");
}

#[test]
fn test_def_multiple() {
    let env = interpret("def a := 0\ndef b := 1\ndef c := 2");
    assert!(has_const(&env, "a"));
    assert!(has_const(&env, "b"));
    assert!(has_const(&env, "c"));
}

#[test]
fn test_def_string_lit() {
    let env = interpret("def greeting := \"hello\"");
    assert!(has_const(&env, "greeting"));
}

#[test]
fn test_def_app() {
    let env = interpret("def one := Nat.succ 0");
    assert!(has_const(&env, "one"));
}

#[test]
fn test_def_lambda() {
    let env = interpret("def myId := fun x => x");
    assert!(has_const(&env, "myId"));
}

#[test]
fn test_def_lambda_typed() {
    let env = interpret("def myId := fun (x : Nat) => x");
    assert!(has_const(&env, "myId"));
}

// ============================================================================
// Axioms
// ============================================================================

#[test]
fn test_axiom() {
    let env = interpret("axiom myAxiom : Nat");
    assert!(has_const(&env, "myAxiom"));
    let ci = env.find(&Name::str("myAxiom")).unwrap();
    assert!(ci.is_axiom());
}

// ============================================================================
// Namespaces
// ============================================================================

#[test]
fn test_namespace() {
    let env = interpret("namespace Foo\ndef bar := 0\nend");
    assert!(has_const(&env, "Foo.bar"), "Foo.bar not found");
}

// ============================================================================
// Type expressions
// ============================================================================

#[test]
fn test_def_type() {
    let env = interpret("def MyType := Nat");
    assert!(has_const(&env, "MyType"));
}

#[test]
fn test_def_prop() {
    let env = interpret("def MyProp := True");
    assert!(has_const(&env, "MyProp"));
}

// ============================================================================
// Count: how many of these work?
// ============================================================================

#[test]
fn test_interpret_summary() {
    let snippets: &[(&str, &str)] = &[
        ("def a := 0", "a"),
        ("def b := 1", "b"),
        ("def c := \"hello\"", "c"),
        ("def d := Nat.succ 0", "d"),
        ("def e := fun x => x", "e"),
        ("def f := fun (x : Nat) => x", "f"),
        ("def g := True", "g"),
        ("def h := Prop", "h"),
        ("def i := Type", "i"),
        ("axiom j : Nat", "j"),
        ("namespace NS\ndef k := 0\nend", "NS.k"),
        ("def l := Nat.zero", "l"),
        ("def m := Bool.true", "m"),
        ("def n := Nat.succ (Nat.succ Nat.zero)", "n"),
        ("def p := (1, 2)", "p"),
        ("axiom q : Bool", "q"),
        ("def r := fun (x : Nat) (y : Nat) => x", "r"),
        ("namespace A\ndef s := 0\nend", "A.s"),
        ("def t := if True then 0 else 1", "t"),
        // Harder: typed definitions
        ("def u : Nat := 42", "u"),
        ("def v : Bool := Bool.true", "v"),
        // Let expressions
        ("def w := let x := 0; Nat.succ x", "w"),
        // Theorem (term-mode)
        ("theorem trivial_true : True := True.intro", "trivial_true"),
        // Multiple binders
        ("def pair := fun (a : Nat) (b : Bool) => a", "pair"),
        // Dot notation / projections
        ("def fst := Prod.fst", "fst"),
        // Application chains
        ("def two := Nat.succ (Nat.succ Nat.zero)", "two"),
        ("def three := Nat.succ (Nat.succ (Nat.succ Nat.zero))", "three"),
        // Higher-order
        ("def apply := fun (f : Nat → Nat) (x : Nat) => f x", "apply"),
        // Implicit binder
        ("def myId := fun {α : Type} (x : α) => x", "myId"),
        // Const with universe
        ("def myList := List", "myList"),
        // Nested let
        ("def nested := let a := 1; let b := 2; a", "nested"),
        // Prop/Type
        ("def mySort := Sort", "mySort"),
        ("axiom myPropAxiom : Prop", "myPropAxiom"),
        // Wildcard / hole
        ("def withHole := @id Nat 0", "withHole"),
        // Bool operations
        ("def myTrue := Bool.true", "myTrue"),
        ("def myFalse := Bool.false", "myFalse"),
        // Nat operations via succ
        ("def five := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))", "five"),
        // Empty namespace
        ("namespace Empty\nend", ""),
        // Open scope
        ("open Nat\ndef mySucc := succ", "mySucc"),
        // Arrow type
        ("def NatToNat : Type := Nat → Nat", "NatToNat"),
        // Nested namespace
        ("namespace A\nnamespace B\ndef x := 0\nend\nend", "A.B.x"),
        // Multiple axioms
        ("axiom ax1 : Nat\naxiom ax2 : Bool\naxiom ax3 : Nat → Nat", "ax3"),
        // Not
        ("def notTrue := ¬ True", "notTrue"),
        // Anonymous constructor
        ("def myPair := ⟨1, 2⟩", "myPair"),
        // Large literal
        ("def big := 999999", "big"),
        // String operations
        ("def emptyStr := \"\"", "emptyStr"),
        // Arithmetic via operator
        ("def inc (n : Nat) : Nat := Nat.succ n", "inc"),
        // Let binding in term
        ("def withLet := let x := 42; x", "withLet"),
        // Theorem term-mode
        ("theorem myTrivial : True := True.intro", "myTrivial"),
        // Forall type
        ("def NatEndomorphism := Nat → Nat", "NatEndomorphism"),
        // Nested fun with multiple typed binders
        ("def swap := fun (a : Nat) (b : Nat) => (b, a)", "swap"),
        // Application of named constant
        ("def applySucc := Nat.succ 42", "applySucc"),
        // Def with binder and body referencing binder
        ("def double (n : Nat) : Nat := Nat.add n n", "double"),
        // Multiple binders
        ("def add3 (a : Nat) (b : Nat) (c : Nat) : Nat := Nat.add (Nat.add a b) c", "add3"),
        // Implicit binder in def
        ("def myId2 {α : Type} (x : α) : α := x", "myId2"),
        // Theorem with binders
        ("theorem myRefl (a : Nat) : Eq a a := Eq.refl a", "myRefl"),
        // Axiom with arrow type
        ("axiom myFun : Nat → Nat → Bool", "myFun"),
        // Def returning a function
        ("def constZero : Nat → Nat := fun _ => 0", "constZero"),
        // Nested application
        ("def succSucc (n : Nat) : Nat := Nat.succ (Nat.succ n)", "succSucc"),
    ];

    let mut ok = 0;
    let mut fail = 0;
    for (src, expected_name) in snippets {
        if expected_name.is_empty() {
            // No constant to check — just verify no panic
            let _ = interpret(src);
            ok += 1;
            continue;
        }
        let env = interpret(src);
        if has_const(&env, expected_name) {
            ok += 1;
        } else {
            fail += 1;
            eprintln!("FAIL: '{}' → {} not found", src, expected_name);
        }
    }
    eprintln!("=== Interpret Summary: {}/{} OK ===", ok, ok + fail);
    assert_eq!(fail, 0, "{} snippets failed", fail);
}

#[test]
fn test_what_fails_next() {
    // Try increasingly hard things, report what works
    let hard: &[(&str, &str)] = &[
        ("def plus1 (n : Nat) : Nat := n + 1", "plus1"),
        ("def addTwo (a b : Nat) : Nat := a + b", "addTwo"),
        ("def listLen := List.length [1, 2, 3]", "listLen"),
        ("def myNot (b : Bool) : Bool := !b", "myNot"),
        ("def strLen := String.length \"hello\"", "strLen"),
    ];
    let env = get_init_env().clone();
    let mut ok = 0;
    let mut fail = 0;
    for (src, name) in hard {
        let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
        let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds { let _ = elab.elab_command(cmd); }
        if elab.env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
            eprintln!("  OK: {}", src);
        } else {
            fail += 1;
            eprintln!("  FAIL: {}", src);
        }
    }
    eprintln!("=== Hard tests: {}/{} ===", ok, ok + fail);
}

#[test]
fn test_tactics() {
    let tac_tests: &[(&str, &str)] = &[
        // by exact
        ("theorem t1 : True := by exact True.intro", "t1"),
        // by trivial (should try exact True.intro)
        ("theorem t2 : True := by trivial", "t2"),
        // by intro + exact
        ("theorem t3 : Nat → Nat := by intro n; exact n", "t3"),
        // by rfl
        ("theorem t4 : 0 = 0 := by rfl", "t4"),
        // by assumption
        ("theorem t5 (h : True) : True := by assumption", "t5"),
        // by constructor on And
        ("theorem t6 : True ∧ True := by constructor <;> exact True.intro", "t6"),
        // by apply
        ("theorem t7 : True := by apply True.intro", "t7"),
        // term-mode still works
        ("theorem t8 (a : Nat) : Eq a a := Eq.refl a", "t8"),
    ];
    let env = get_init_env().clone();
    let mut ok = 0;
    let mut fail = 0;
    for (src, name) in tac_tests {
        let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
        let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds { let _ = elab.elab_command(cmd); }
        if elab.env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
            eprintln!("  TAC OK: {}", name);
        } else {
            fail += 1;
            eprintln!("  TAC FAIL: {}", name);
        }
    }
    eprintln!("=== Tactic tests: {}/{} ===", ok, ok + fail);
}

#[test]
fn test_tactic_proof_terms() {
    let env = get_init_env().clone();
    // Check that by-proofs produce real proof terms (not mvars)
    let src = "theorem byExact : True := by exact True.intro";
    let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
    let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
    for cmd in &cmds { let _ = elab.elab_command(cmd); }
    let ci = elab.env.find(&lean4_kernel::name::Name::str("byExact")).unwrap();
    let val = ci.get_value().expect("theorem should have value");
    // The value should NOT be a metavariable
    let is_mvar = val.is_mvar();
    eprintln!("byExact value is_mvar: {} kind: {:?}", is_mvar, val.kind());
    // Currently this will be a mvar since we don't really evaluate tactics
    // This test documents the current state
    if is_mvar {
        eprintln!("  KNOWN ISSUE: by blocks produce unsolved mvars, not real proofs");
    } else {
        eprintln!("  GOOD: by block produced a real proof term");
    }
}

#[test]
fn test_pattern_match_and_more() {
    let tests: &[(&str, &str)] = &[
        // Match expression
        ("def isZero (n : Nat) : Bool := match n with | 0 => true | _ => false", "isZero"),
        // Cases tactic
        ("theorem t_cases (b : Bool) : b = true ∨ b = false := by cases b <;> constructor <;> rfl", "t_cases"),
        // Have tactic
        ("theorem t_have : True := by have h : True := True.intro; exact h", "t_have"),
        // Multiple intros
        ("theorem t_intros : Nat → Nat → Nat := by intros; assumption", "t_intros"),
        // Nested apply
        ("theorem t_and : True ∧ True := by exact And.intro True.intro True.intro", "t_and"),
        // Let in tactic
        ("theorem t_let : Nat := by exact (let x := 0; x)", "t_let"),
        // Structure def
        ("structure MyPoint where x : Nat; y : Nat", "MyPoint"),
        // Abbrev
        ("abbrev MyNat := Nat", "MyNat"),
    ];
    let env = get_init_env().clone();
    let mut ok = 0;
    let mut fail = 0;
    for (src, name) in tests {
        let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
        let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds {
            if let Err(e) = elab.elab_command(cmd) {
                eprintln!("  ERR {}: {}", name, e);
            }
        }
        if name.is_empty() || elab.env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
            eprintln!("  OK: {}", name);
        } else {
            fail += 1;
            eprintln!("  FAIL: {}", name);
        }
    }
    eprintln!("=== Pattern/Advanced: {}/{} ===", ok, ok + fail);
}

#[test]
fn test_debug_match_parse() {
    let src = "def isZero (n : Nat) : Bool := match n with | 0 => true | _ => false";
    let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
    eprintln!("Commands: {}", cmds.len());
    for (i, cmd) in cmds.iter().enumerate() {
        eprintln!("  cmd[{}] kind: {:?} nargs: {}", i,
            cmd.kind_name().map(|n| n.to_string()),
            cmd.num_args());
        for (j, arg) in cmd.args().iter().enumerate() {
            eprintln!("    arg[{}] kind: {:?} nargs: {}", j,
                arg.kind_name().map(|n| n.to_string()),
                arg.num_args());
        }
    }
}

#[test]
fn test_check_caseson() {
    let env = get_init_env();
    let names = ["Nat.casesOn", "Nat.rec", "Bool.casesOn", "Bool.rec"];
    for n in &names {
        let found = env.find(&lean4_kernel::name::Name::str(n)).is_some();
        eprintln!("  {} : {}", n, if found { "FOUND" } else { "MISSING" });
    }
}

#[test]
fn test_even_harder() {
    let tests: &[(&str, &str)] = &[
        // Equation-style def (match sugar)
        ("def isEven : Nat → Bool | 0 => true | Nat.succ n => !isEven n", "isEven"),
        // Where clause
        ("def f := let helper := 42; helper", "f"),
        // List literal
        ("def myList := [1, 2, 3]", "myList"),
        // Sigma type
        ("def myExists := ∃ n : Nat, n = 0", "myExists"),
        // If-then-else with Bool
        ("def max (a b : Nat) : Nat := if Nat.ble a b then b else a", "max"),
        // Nested match
        ("def add (a b : Nat) : Nat := match b with | 0 => a | Nat.succ n => Nat.succ (add a n)", "add"),
        // Prod.fst projection
        ("def fst3 := Prod.fst (1, 2)", "fst3"),
        // Show
        ("theorem show_ex : True := show True from True.intro", "show_ex"),
        // Calc (basic)
        ("theorem calc_ex : 0 = 0 := by rfl", "calc_ex"),
        // Complex lambda
        ("def compose (f g : Nat → Nat) (x : Nat) : Nat := f (g x)", "compose"),
        // Def with return function type
        ("def adder (n : Nat) : Nat → Nat := fun m => Nat.add n m", "adder"),
    ];
    let env = get_init_env().clone();
    let mut ok = 0;
    let mut fail = 0;
    for (src, name) in tests {
        let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
        let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds {
            if let Err(e) = elab.elab_command(cmd) {
                if fail < 10 { eprintln!("  ERR {}: {}", name, e); }
            }
        }
        if elab.env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
        } else {
            fail += 1;
            if fail <= 10 { eprintln!("  FAIL: {}", name); }
        }
    }
    eprintln!("=== Even Harder: {}/{} ===", ok, ok + fail);
}

#[test]
fn test_simp_rw_and_more() {
    let tests: &[(&str, &str)] = &[
        // Do notation (basic)
        ("def pureVal : Option Nat := pure 0", "pureVal"),
        // Where clause (simulated as let)
        ("def withHelper := let helper := 42; Nat.succ helper", "withHelper"),
        // Complex theorem
        ("theorem and_intro (a b : Prop) (ha : a) (hb : b) : a ∧ b := And.intro ha hb", "and_intro"),
        // Prod projection
        ("def myFst (p : Nat × Nat) : Nat := Prod.fst p", "myFst"),
        // Higher-order function
        ("def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)", "twice"),
        // Type alias
        ("def Predicate := Nat → Prop", "Predicate"),
        // Dependent type
        ("def Vec (α : Type) (n : Nat) := { l : List α // List.length l = n }", "Vec"),
        // Abbrev
        ("abbrev N := Nat", "N"),
        // Open + qualified
        ("open Bool\ndef myAnd := and true false", "myAnd"),
        // Nested if
        ("def clamp (lo hi x : Nat) : Nat := if Nat.ble x lo then lo else if Nat.ble hi x then hi else x", "clamp"),
        // Wildcard lambda
        ("def ignore := fun (_ : Nat) => 0", "ignore"),
        // Multiple let
        ("def chain := let a := 1; let b := Nat.succ a; let c := Nat.succ b; c", "chain"),
    ];
    let env = get_init_env().clone();
    let mut ok = 0;
    let mut fail = 0;
    for (src, name) in tests {
        let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
        let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds {
            if let Err(e) = elab.elab_command(cmd) {
                if fail < 5 { eprintln!("  ERR {}: {}", name, e); }
            }
        }
        if elab.env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
        } else {
            fail += 1;
            if fail <= 5 { eprintln!("  FAIL: {}", name); }
        }
    }
    eprintln!("=== Simp/Rw/More: {}/{} ===", ok, ok + fail);
}

#[test]
fn test_mathlib_style_file() {
    let src = std::fs::read_to_string("/r/tmp/lean4/test_mathlib_style.lean").unwrap();
    let sp = vec![std::path::PathBuf::from("/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean")];
    let env = lean4_kernel::elaborator::interpret_lean_file(&src, &sp).unwrap();

    let expected = vec![
        "double", "triple", "apply", "compose",
        "id'", "const'",
        "eq_self", "true_and_true",
        "true_trivial", "nat_eq_self", "and_trivial",
        "isZero",
        "Point", "Point.mk",
        "MyNat.succ", "MyNat.zero",
        "myList", "emptyList",
        "origin",
        "choice",
    ];
    let mut ok = 0;
    let mut fail = 0;
    for name in &expected {
        if env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
        } else {
            fail += 1;
            eprintln!("MISSING: {}", name);
        }
    }
    eprintln!("=== Mathlib-style file: {}/{} constants ===", ok, ok + fail);
}

#[test]
fn test_interpret_init_bindernamehint() {
    // Try to interpret a real tiny Init file
    let path = "/r/study/lean4/src/Init/BinderNameHint.lean";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(_) => { eprintln!("SKIP: {} not found", path); return; }
    };
    eprintln!("Source ({} bytes):\n{}", src.len(), &src[..src.len().min(500)]);
    let sp = vec![std::path::PathBuf::from("/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean")];
    let env = lean4_kernel::elaborator::interpret_lean_file(&src, &sp).unwrap();

    // Count new constants (beyond Init)
    let init_count = 43504; // from our earlier tests
    let total = env.num_constants();
    let new = if total > init_count { total - init_count } else { 0 };
    eprintln!("=== Init/BinderNameHint: {} total constants, {} new ===", total, new);
}

#[test]
fn test_interpret_many_init_files() {
    let lean_src = "/r/study/lean4/src";
    let sp = vec![std::path::PathBuf::from("/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean")];

    let mut files = Vec::new();
    collect_init_files2(&format!("{}/Init", lean_src), &mut files);
    files.sort();

    let mut ok = 0;
    let mut fail = 0;
    let mut total_new = 0;
    for path in &files {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let result = std::panic::catch_unwind(|| {
            lean4_kernel::elaborator::interpret_lean_file(&src, &sp)
        });
        match result {
            Ok(Ok(env)) => {
                let new = env.num_constants().saturating_sub(43504);
                total_new += new;
                ok += 1;
            }
            Ok(Err(_)) | Err(_) => {
                fail += 1;
                if fail <= 10 {
                    let short = path.rsplit('/').next().unwrap_or(path);
                    eprintln!("  FAIL: {}", short);
                }
            }
        }
    }
    eprintln!("=== Init files: {}/{} succeeded, {} new constants ===", ok, ok + fail, total_new);
}

fn collect_init_files2(dir: &str, out: &mut Vec<String>) {
    let entries = match std::fs::read_dir(dir) { Ok(e) => e, Err(_) => return };
    for entry in entries {
        let entry = match entry { Ok(e) => e, Err(_) => continue };
        let path = entry.path();
        if path.is_dir() {
            collect_init_files2(path.to_str().unwrap_or(""), out);
        } else if path.extension().map_or(false, |e| e == "lean") {
            out.push(path.to_string_lossy().to_string());
        }
    }
}

#[test]
fn test_do_calc_where() {
    let tests: &[(&str, &str)] = &[
        // Do notation basic
        ("def doEx := do return 42", "doEx"),
        // Where clause
        ("def withWhere := helper 10 where helper (n : Nat) := Nat.succ n", "withWhere"),
        // Anonymous wildcard
        ("def dropFirst := fun (_ : Nat) (y : Nat) => y", "dropFirst"),
        // Multiple open
        ("open Nat\nopen Bool\ndef myBoolAnd := and true false", "myBoolAnd"),
        // Nested namespace with defs
        ("namespace A\nnamespace B\ndef c := 0\ndef d := 1\nend B\ndef e := 2\nend A", "A.e"),
        // Deeply nested app
        ("def deep := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))))", "deep"),
    ];
    let env = get_init_env().clone();
    let mut ok = 0;
    let mut fail = 0;
    for (src, name) in tests {
        let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
        let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds { let _ = elab.elab_command(cmd); }
        if elab.env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
        } else {
            fail += 1;
            if fail <= 5 { eprintln!("  FAIL: {} from '{}'", name, src); }
        }
    }
    eprintln!("=== Do/Calc/Where: {}/{} ===", ok, ok + fail);
}

#[test]
fn test_remaining_features() {
    let tests: &[(&str, &str)] = &[
        ("axiom myChoice : ∀ {α : Type}, α → α", "myChoice"),
        ("def anon := fun _ => 0", "anon"),
        ("def ForallType := ∀ (n : Nat), n = n", "ForallType"),
        ("def myNone : Option Nat := none", "myNone"),
        ("def mySome : Option Nat := some 42", "mySome"),
        ("def app3 := @Nat.add 1 2", "app3"),
        ("structure Pair (α β : Type) where fst : α; snd : β", "Pair"),
        ("def addNats (a b : Nat) : Nat := a + b", "addNats"),
        ("theorem propId (P : Prop) (h : P) : P := h", "propId"),
        ("def firstOrZero : List Nat → Nat | [] => 0 | x :: _ => x", "firstOrZero"),
    ];
    let env = get_init_env().clone();
    let mut ok = 0;
    let mut fail = 0;
    for (src, name) in tests {
        let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
        let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds { let _ = elab.elab_command(cmd); }
        if elab.env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
        } else {
            fail += 1;
            if fail <= 5 { eprintln!("  FAIL: {} from '{}'", name, &src[..src.len().min(60)]); }
        }
    }
    eprintln!("=== Remaining: {}/{} ===", ok, ok + fail);
}

#[test]
fn test_stress() {
    let tests: &[(&str, &str)] = &[
        ("mutual\ndef even2 : Nat → Bool | 0 => true | Nat.succ n => odd2 n\ndef odd2 : Nat → Bool | 0 => false | Nat.succ n => even2 n\nend", "even2"),
        ("class MyClass (α : Type) where val : α", "MyClass"),
        ("inductive Color | red | green | blue", "Color"),
        ("def bigNum := 1000000", "bigNum"),
        ("def strEx := String.length \"hello world\"", "strEx"),
        ("def headOr (l : List Nat) (d : Nat) : Nat := match l with | [] => d | x :: _ => x", "headOr"),
        ("theorem eq_comm (a b : Nat) : a = b → b = a := fun h => Eq.symm h", "eq_comm"),
        ("open List\ndef myLen := length [1, 2, 3]", "myLen"),
        ("def bothZero (a b : Nat) : Bool := match a with | 0 => match b with | 0 => true | _ => false | _ => false", "bothZero"),
        ("def countDown (n : Nat) : Nat := match n with | 0 => 0 | Nat.succ k => countDown k", "countDown"),
        ("def mapOpt {α β : Type} (f : α → β) : Option α → Option β | none => none | some a => some (f a)", "mapOpt"),
        ("def myUnit : Type := Unit", "myUnit"),
    ];
    let env = get_init_env().clone();
    let mut ok = 0;
    let mut fail = 0;
    for (src, name) in tests {
        let (_, _, cmds) = lean4_kernel::parser::parse_file(src);
        let mut elab = lean4_kernel::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds { let _ = elab.elab_command(cmd); }
        if elab.env.find(&lean4_kernel::name::Name::str(name)).is_some() {
            ok += 1;
        } else {
            fail += 1;
            if fail <= 10 { eprintln!("  STRESS FAIL: {}", name); }
        }
    }
    eprintln!("=== Stress: {}/{} ===", ok, ok + fail);
}

#[test]
fn test_interpret_mathlib_files() {
    let sp = vec![
        std::path::PathBuf::from("/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/batteries/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/Qq/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/aesop/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/proofwidgets/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/importGraph/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/LeanSearchClient/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/plausible/.lake/build/lib/lean"),
    ];
    let mut files: Vec<String> = Vec::new();
    for subdir in &["Logic", "Data", "Init"] {
        let dir = format!("/r/study/mathlib-v4.25.2/Mathlib/{}", subdir);
        if let Ok(entries) = std::fs::read_dir(&dir) {
            for entry in entries.flatten() {
                let p = entry.path();
                if p.is_file() && p.extension().map_or(false, |e| e == "lean") && p.metadata().unwrap().len() < 5000 {
                    files.push(p.to_string_lossy().to_string());
                }
            }
        }
    }
    files.sort();
    files.truncate(20);
    let mut loaded = 0;
    let mut failed = 0;
    for path in &files {
        let src = match std::fs::read_to_string(path) { Ok(s) => s, Err(_) => continue };
        match std::panic::catch_unwind(|| lean4_kernel::elaborator::interpret_lean_file(&src, &sp)) {
            Ok(Ok(env)) => { loaded += 1; }
            _ => { failed += 1; let s = path.rsplit('/').next().unwrap_or(path); if failed <= 10 { eprintln!("  MATHLIB FAIL: {}", s); } }
        }
    }
    eprintln!("=== Mathlib .lean files: {}/{} loaded ===", loaded, loaded + failed);
}

#[test]
fn test_interpret_100_mathlib_files() {
    let sp = vec![
        std::path::PathBuf::from("/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/batteries/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/Qq/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/aesop/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/proofwidgets/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/importGraph/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/LeanSearchClient/.lake/build/lib/lean"),
        std::path::PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/plausible/.lake/build/lib/lean"),
    ];
    let mut all_files: Vec<String> = Vec::new();
    fn collect_ml(dir: &str, out: &mut Vec<String>) {
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                let p = entry.path();
                if p.is_dir() { collect_ml(p.to_str().unwrap_or(""), out); }
                else if p.extension().map_or(false, |e| e == "lean") {
                    out.push(p.to_string_lossy().to_string());
                }
            }
        }
    }
    collect_ml("/r/study/mathlib-v4.25.2/Mathlib", &mut all_files);
    all_files.sort();
    let files: Vec<&str> = all_files.iter().map(|s| s.as_str()).take(100).collect();
    let mut loaded = 0;
    let mut failed = 0;
    for path in &files {
        let src = match std::fs::read_to_string(path) { Ok(s) => s, Err(_) => continue };
        match std::panic::catch_unwind(|| lean4_kernel::elaborator::interpret_lean_file(&src, &sp)) {
            Ok(Ok(_)) => { loaded += 1; }
            _ => { failed += 1; }
        }
    }
    eprintln!("=== 100 Mathlib files: {}/{} loaded ===", loaded, loaded + failed);
}
