//! Parse all Init .lean files — zero panics expected.

use lean4_kernel::parser::parse_file;

#[test]
fn test_parse_all_init_files() {
    let base = "/r/study/lean4/src";
    let mut files = Vec::new();
    collect_lean_files(&format!("{}/Init", base), &mut files);

    let mut total = 0;
    let mut total_cmds = 0;
    let mut failures = 0;
    for path in &files {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(_) => continue,
        };
        total += 1;
        let result = std::panic::catch_unwind(|| parse_file(&src));
        match result {
            Ok((_, _, cmds)) => total_cmds += cmds.len(),
            Err(_) => {
                failures += 1;
                if failures <= 5 { eprintln!("PANIC: {}", path); }
            }
        }
    }
    eprintln!("Parsed {} Init files: {} commands, {} failures", total, total_cmds, failures);
    assert_eq!(failures, 0);
}

fn collect_lean_files(dir: &str, out: &mut Vec<String>) {
    let entries = match std::fs::read_dir(dir) { Ok(e) => e, Err(_) => return };
    for entry in entries {
        let entry = match entry { Ok(e) => e, Err(_) => continue };
        let path = entry.path();
        if path.is_dir() {
            collect_lean_files(path.to_str().unwrap_or(""), out);
        } else if path.extension().map_or(false, |e| e == "lean") {
            out.push(path.to_string_lossy().to_string());
        }
    }
}
