//! Scale test: load Mathlib env ONCE, then interpret many files against it.
use std::path::PathBuf;
use std::sync::OnceLock;
use lean4_kernel::env::Environment;
use lean4_kernel::name::Name;
use lean4_kernel::elaborator::Elaborator;
use lean4_kernel::parser::parse_file;

static MATHLIB_ENV: OnceLock<Environment> = OnceLock::new();

fn get_mathlib_env() -> &'static Environment {
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
        lean4_kernel::olean_fast::load_module_tree_fast(&Name::str("Mathlib"), &sp)
            .unwrap().env
    })
}

fn collect_all(dir: &str, out: &mut Vec<String>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() { collect_all(p.to_str().unwrap_or(""), out); }
            else if p.extension().map_or(false, |e| e == "lean") {
                out.push(p.to_string_lossy().to_string());
            }
        }
    }
}

#[test]
fn test_mathlib_scale() {
    let env = get_mathlib_env();
    eprintln!("Mathlib env: {} constants", env.num_constants());

    let mut all_files = Vec::new();
    collect_all("/r/study/mathlib-v4.25.2/Mathlib", &mut all_files);
    all_files.sort();

    let total = all_files.len();
    let sample: Vec<&str> = all_files.iter().step_by(total / 200 + 1).map(|s| s.as_str()).collect();
    eprintln!("Testing {} / {} files", sample.len(), total);

    let mut loaded = 0u32;
    let mut new_consts = 0usize;
    let mut failed = 0u32;
    let mut errs: Vec<String> = Vec::new();

    for path in &sample {
        let src = match std::fs::read_to_string(path) { Ok(s) => s, Err(_) => continue };
        let (_, _, commands) = parse_file(&src);
        let result = std::panic::catch_unwind(|| {
            let mut elab = Elaborator::new(env.clone());
            let mut cmd_ok = 0;
            for cmd in &commands {
                if elab.elab_command(cmd).is_ok() { cmd_ok += 1; }
            }
            (elab.env.num_constants().saturating_sub(env.num_constants()), cmd_ok)
        });
        match result {
            Ok((new, _)) => { loaded += 1; new_consts += new; }
            Err(_) => {
                failed += 1;
                if errs.len() < 20 {
                    errs.push(path.rsplit('/').next().unwrap_or(path).to_string());
                }
            }
        }
    }
    eprintln!("=== Mathlib Scale: {}/{} files, {} new constants ===", loaded, loaded + failed, new_consts);
    if !errs.is_empty() {
        eprintln!("Failed files: {:?}", &errs[..errs.len().min(10)]);
    }
}
