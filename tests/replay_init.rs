//! Stage 27: Replay-verify Init constants through the Rust type checker.

use std::path::PathBuf;
use lean4_kernel::olean::load_module_tree;
use lean4_kernel::name::Name;
use lean4_kernel::env::*;
use lean4_kernel::type_checker::TypeChecker;
use lean4_kernel::local_ctx::LocalContext;

const LEAN_LIB: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean";

#[test]
fn test_replay_prelude_types() {
    let sp = vec![PathBuf::from(LEAN_LIB)];
    let loaded = load_module_tree(&Name::str("Init"), &sp).unwrap();
    eprintln!("Loaded {} constants", loaded.env.num_constants());

    let mut tc = TypeChecker::new(loaded.env.clone(), LocalContext::new());
    let mut ok = 0u32;
    let mut fail = 0u32;
    let mut skip = 0u32;
    let mut first_fails: Vec<String> = Vec::new();

    loaded.env.for_each_constant(|name, ci| {
        // For each constant, try to infer the type of its type
        // (the type of a type should be a Sort)
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tc.infer_type(&ci.type_)
        }));
        match result {
            Ok(_ty) => { ok += 1; }
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

    eprintln!("=== Prelude Type Inference ===");
    eprintln!("  OK:   {}", ok);
    eprintln!("  FAIL: {}", fail);
    eprintln!("  SKIP: {}", skip);
    if !first_fails.is_empty() {
        eprintln!("First failures:");
        for f in &first_fails {
            eprintln!("  {}", f);
        }
    }
    let total = ok + fail + skip;
    eprintln!("  Pass rate: {:.1}%", 100.0 * ok as f64 / total as f64);
}
