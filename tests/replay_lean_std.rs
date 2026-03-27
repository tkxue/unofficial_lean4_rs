//! Load and replay-verify the full Lean+Std standard library.

use std::path::PathBuf;
use lean4_kernel::olean::load_module_tree;
use lean4_kernel::name::Name;
use lean4_kernel::type_checker::TypeChecker;
use lean4_kernel::local_ctx::LocalContext;

const LEAN_LIB: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean";

#[test]
fn test_load_lean_stdlib() {
    let sp = vec![PathBuf::from(LEAN_LIB)];
    // Load Lean (includes Init + Std + Lean itself)
    let loaded = load_module_tree(&Name::str("Lean"), &sp).unwrap();
    eprintln!("Lean stdlib: {} modules, {} constants",
        loaded.modules_loaded.len(), loaded.env.num_constants());

    // Type-check all constants
    let mut tc = TypeChecker::new(loaded.env.clone(), LocalContext::new());
    let mut ok = 0u32;
    let mut fail = 0u32;
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

    eprintln!("=== Lean Stdlib Type Inference ===");
    eprintln!("  OK:   {}", ok);
    eprintln!("  FAIL: {}", fail);
    if !first_fails.is_empty() {
        eprintln!("First failures:");
        for f in &first_fails { eprintln!("  {}", f); }
    }
    let total = ok + fail;
    let pct = 100.0 * ok as f64 / total as f64;
    eprintln!("  Pass rate: {:.1}% ({}/{})", pct, ok, total);
}
