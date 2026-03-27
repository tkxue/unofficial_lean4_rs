use std::time::Instant;
use std::path::PathBuf;
use lean4_kernel::name::Name;
#[test]
fn bench_load_only() {
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
    // Run 3 times to warm cache
    for i in 0..3 {
        let t0 = Instant::now();
        let loaded = lean4_kernel::olean_fast::load_module_tree_fast(&Name::str("Mathlib"), &sp).unwrap();
        eprintln!("Run {}: {:.2}s, {} constants", i, t0.elapsed().as_secs_f64(), loaded.env.num_constants());
    }
}
