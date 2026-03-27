use std::time::Instant;
use std::path::PathBuf;
use lean4_kernel::name::Name;
#[test]
fn bench_load_trust() {
    let sp = vec![
        PathBuf::from("/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean"),
        PathBuf::from("/r/study/mathlib-v4.25.2/.lake/build/lib/lean"),
        PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/batteries/.lake/build/lib/lean"),
        PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/Qq/.lake/build/lib/lean"),
        PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/aesop/.lake/build/lib/lean"),
        PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/proofwidgets/.lake/build/lib/lean"),
        PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/importGraph/.lake/build/lib/lean"),
        PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/LeanSearchClient/.lake/build/lib/lean"),
        PathBuf::from("/r/study/mathlib-v4.25.2/.lake/packages/plausible/.lake/build/lib/lean"),
    ];

    // C++ mode: just load, don't verify
    let t0 = Instant::now();
    let loaded = lean4_kernel::olean_fast::load_module_tree_fast(&Name::str("Mathlib"), &sp).unwrap();
    let load_time = t0.elapsed();

    // Just check a few constants exist (sanity, not full verify)
    assert!(loaded.env.find(&Name::str("Nat")).is_some());
    assert!(loaded.env.find(&Name::str("Nat.add")).is_some());
    assert!(loaded.env.find(&Name::str("List")).is_some());

    eprintln!("=== Rust load-only (trust .olean, like C++): {:.2}s ===", load_time.as_secs_f64());
    eprintln!("  {} modules, {} constants", loaded.modules_loaded.len(), loaded.env.num_constants());
    eprintln!("  C++ equivalent: 5.6s");
    eprintln!("  Ratio: {:.1}x", load_time.as_secs_f64() / 5.6);
}
