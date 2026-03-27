use std::path::PathBuf;
use std::sync::OnceLock;
use lean4_kernel::env::Environment;
use lean4_kernel::name::Name;
use lean4_kernel::elaborator::Elaborator;
use lean4_kernel::parser::parse_file;

static MATHLIB_ENV: OnceLock<Environment> = OnceLock::new();
fn get_env() -> &'static Environment {
    MATHLIB_ENV.get_or_init(|| {
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
        eprintln!("Loading Mathlib env...");
        let r = lean4_kernel::olean_fast::load_module_tree_fast(&Name::str("Mathlib"), &sp).unwrap().env;
        eprintln!("Loaded: {} constants", r.num_constants());
        r
    })
}
fn collect(dir: &str, out: &mut Vec<String>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() { collect(p.to_str().unwrap_or(""), out); }
            else if p.extension().map_or(false, |e| e == "lean") { out.push(p.to_string_lossy().to_string()); }
        }
    }
}

#[test]
fn test_all_mathlib() {
    let env = get_env();
    let mut all = Vec::new();
    collect("/r/study/mathlib-v4.25.2/Mathlib", &mut all);
    all.sort();
    let total = all.len();
    eprintln!("Files: {}", total);
    let mut ok = 0u32;
    let mut fail = 0u32;
    let mut new = 0usize;
    let t0 = std::time::Instant::now();
    for (i, path) in all.iter().enumerate() {
        let src = match std::fs::read_to_string(path) { Ok(s) => s, Err(_) => continue };
        let (_, _, cmds) = parse_file(&src);
        match std::panic::catch_unwind(|| {
            let mut e = Elaborator::new(env.clone());
            for c in &cmds { let _ = e.elab_command(c); }
            e.env.num_constants().saturating_sub(env.num_constants())
        }) {
            Ok(n) => { ok += 1; new += n; }
            Err(_) => { fail += 1; }
        }
        if (i + 1) % 1000 == 0 {
            eprintln!("  [{}/{}] ok={} fail={} new={} ({:.1}s)", i+1, total, ok, fail, new, t0.elapsed().as_secs_f64());
        }
    }
    let elapsed = t0.elapsed().as_secs_f64();
    eprintln!("=== ALL MATHLIB: {}/{} files ({:.1}%), {} new constants, {} failed, {:.1}s ===",
        ok, total, 100.0 * ok as f64 / total as f64, new, fail, elapsed);
}
