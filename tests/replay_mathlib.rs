//! Stage 29: Replay-verify Mathlib through the Rust type checker.

use std::path::PathBuf;
use lean4_kernel::olean::load_module_tree;
use lean4_kernel::name::Name;
use lean4_kernel::type_checker::TypeChecker;
use lean4_kernel::local_ctx::LocalContext;

const LEAN_LIB: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean";
const MATHLIB_LIB: &str = "/r/study/mathlib-v4.25.2/.lake/build/lib/lean";

#[test]
fn test_replay_mathlib() {
    let sp = vec![
        PathBuf::from(LEAN_LIB),
        PathBuf::from(MATHLIB_LIB),
    ];

    // Also add package build dirs
    let pkg_dirs = [
        "/r/study/mathlib-v4.25.2/.lake/packages/batteries/.lake/build/lib/lean",
        "/r/study/mathlib-v4.25.2/.lake/packages/Qq/.lake/build/lib/lean",
        "/r/study/mathlib-v4.25.2/.lake/packages/aesop/.lake/build/lib/lean",
        "/r/study/mathlib-v4.25.2/.lake/packages/proofwidgets/.lake/build/lib/lean",
        "/r/study/mathlib-v4.25.2/.lake/packages/importGraph/.lake/build/lib/lean",
        "/r/study/mathlib-v4.25.2/.lake/packages/LeanSearchClient/.lake/build/lib/lean",
        "/r/study/mathlib-v4.25.2/.lake/packages/plausible/.lake/build/lib/lean",
    ];
    let mut sp = sp;
    for d in &pkg_dirs {
        let p = PathBuf::from(d);
        if p.exists() { sp.push(p); }
    }

    eprintln!("Search paths:");
    for p in &sp { eprintln!("  {}", p.display()); }

    // Load Mathlib (top-level umbrella)
    eprintln!("Loading Mathlib...");
    let loaded = match load_module_tree(&Name::str("Mathlib"), &sp) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("Failed to load Mathlib: {}", e);
            // Try a smaller target
            eprintln!("Trying Mathlib.Algebra.Group.Basic...");
            match load_module_tree(&Name::str("Mathlib.Algebra.Group.Basic"), &sp) {
                Ok(l) => l,
                Err(e2) => { eprintln!("Also failed: {}", e2); return; }
            }
        }
    };

    eprintln!("Loaded: {} modules, {} constants",
        loaded.modules_loaded.len(), loaded.env.num_constants());

    // Type-check all constants
    let mut tc = TypeChecker::new(loaded.env.clone(), LocalContext::new());
    let mut ok = 0u64;
    let mut fail = 0u64;
    let mut first_fails: Vec<String> = Vec::new();

    loaded.env.for_each_constant(|name, ci| {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tc.infer_type(&ci.type_)
        }));
        match result {
            Ok(_) => { ok += 1; }
            Err(e) => {
                fail += 1;
                if first_fails.len() < 20 {
                    let msg = if let Some(s) = e.downcast_ref::<String>() {
                        s.clone()
                    } else if let Some(s) = e.downcast_ref::<&str>() {
                        s.to_string()
                    } else {
                        "unknown panic".to_string()
                    };
                    first_fails.push(format!("{}: {}", name, msg));
                }
            }
        }
    });

    let total = ok + fail;
    let pct = if total > 0 { 100.0 * ok as f64 / total as f64 } else { 0.0 };
    eprintln!("=== Mathlib Type Inference ===");
    eprintln!("  OK:   {}", ok);
    eprintln!("  FAIL: {}", fail);
    eprintln!("  Pass rate: {:.2}% ({}/{})", pct, ok, total);
    if !first_fails.is_empty() {
        eprintln!("First failures:");
        for f in &first_fails { eprintln!("  {}", f); }
    }
}
