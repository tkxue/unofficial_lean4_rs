//! Benchmark: fast olean reader + Mathlib replay

use std::path::PathBuf;
use std::time::Instant;
use lean4_kernel::name::Name;
use lean4_kernel::type_checker::TypeChecker;
use lean4_kernel::local_ctx::LocalContext;

const LEAN_LIB: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean";
const MATHLIB_LIB: &str = "/r/study/mathlib-v4.25.2/.lake/build/lib/lean";

fn mathlib_search_paths() -> Vec<PathBuf> {
    let mut sp = vec![PathBuf::from(LEAN_LIB), PathBuf::from(MATHLIB_LIB)];
    for pkg in &["batteries", "Qq", "aesop", "proofwidgets", "importGraph", "LeanSearchClient", "plausible"] {
        let p = PathBuf::from(format!("/r/study/mathlib-v4.25.2/.lake/packages/{}/.lake/build/lib/lean", pkg));
        if p.exists() { sp.push(p); }
    }
    sp
}

#[test]
fn bench_mathlib_fast() {
    let sp = mathlib_search_paths();

    let t0 = Instant::now();
    let loaded = lean4_kernel::olean_fast::load_module_tree_fast(&Name::str("Mathlib"), &sp).unwrap();
    let load_time = t0.elapsed();

    eprintln!("=== Load ===");
    eprintln!("  {} modules, {} constants in {:.2}s",
        loaded.modules_loaded.len(), loaded.env.num_constants(), load_time.as_secs_f64());

    let t1 = Instant::now();
    let mut tc = TypeChecker::new(loaded.env.clone(), LocalContext::new());
    let mut ok = 0u64;
    let mut fail = 0u64;
    loaded.env.for_each_constant(|_, ci| {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| { tc.infer_type(&ci.type_) })) {
            Ok(_) => { ok += 1; }
            Err(_) => { fail += 1; }
        }
    });
    let verify_time = t1.elapsed();

    eprintln!("=== Verify ===");
    eprintln!("  {}/{} OK in {:.2}s", ok, ok+fail, verify_time.as_secs_f64());
    eprintln!("=== Total: {:.2}s ===", t0.elapsed().as_secs_f64());
}
