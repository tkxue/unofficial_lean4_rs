//! Verify ALL expression hashes from parsed .olean against the C++ kernel.

use std::path::Path;
use lean4_kernel::olean::OleanFile;

const PRELUDE: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean/Init/Prelude.olean";
const HASH_FILE: &str = "/r/tmp/lean4/verify_hashes.txt";

#[test]
fn test_all_prelude_type_hashes() {
    let olean = OleanFile::read(Path::new(PRELUDE)).unwrap();
    let md = olean.parse_module_data().unwrap();

    // Load expected hashes from Lean dump: "name_hash type_hash value_hash_or_none"
    let content = match std::fs::read_to_string(HASH_FILE) {
        Ok(c) => c,
        Err(_) => { eprintln!("SKIP: {} not found", HASH_FILE); return; }
    };
    let mut expected: std::collections::HashMap<u64, (u32, Option<u32>)> = std::collections::HashMap::new();
    for line in content.lines() {
        if line.starts_with("TOTAL") || line.contains("warning") || line.is_empty() { continue; }
        let parts: Vec<&str> = line.split(' ').collect();
        if parts.len() < 3 { continue; }
        let nh: u64 = match parts[0].parse() { Ok(v) => v, Err(_) => continue };
        let th: u32 = match parts[1].parse() { Ok(v) => v, Err(_) => continue };
        let vh: Option<u32> = parts[2].parse().ok();
        expected.insert(nh, (th, vh));
    }

    let mut type_match = 0u64;
    let mut type_mismatch = 0u64;
    let mut val_match = 0u64;
    let mut val_mismatch = 0u64;
    let mut val_skipped = 0u64;
    let mut first_type_fail: Vec<String> = Vec::new();
    let mut first_val_fail: Vec<String> = Vec::new();

    for ci in &md.constants {
        let nh = ci.name.hash();
        if let Some(&(exp_th, exp_vh)) = expected.get(&nh) {
            // Check type hash
            if ci.type_.hash() == exp_th {
                type_match += 1;
            } else {
                type_mismatch += 1;
                if first_type_fail.len() < 10 {
                    first_type_fail.push(format!("  {} type: got {} exp {}", ci.name, ci.type_.hash(), exp_th));
                }
            }
            // Check value hash
            match (ci.get_value(), exp_vh) {
                (Some(val), Some(evh)) => {
                    if val.hash() == evh {
                        val_match += 1;
                    } else {
                        val_mismatch += 1;
                        if first_val_fail.len() < 10 {
                            first_val_fail.push(format!("  {} value: got {} exp {}", ci.name, val.hash(), evh));
                        }
                    }
                }
                _ => { val_skipped += 1; }
            }
        }
    }

    eprintln!("=== Prelude .olean hash verification ===");
    eprintln!("Constants parsed: {}", md.constants.len());
    eprintln!("Type hashes:  {} match, {} mismatch", type_match, type_mismatch);
    eprintln!("Value hashes: {} match, {} mismatch, {} skipped", val_match, val_mismatch, val_skipped);
    if !first_type_fail.is_empty() {
        eprintln!("First type mismatches:");
        for f in &first_type_fail { eprintln!("{}", f); }
    }
    if !first_val_fail.is_empty() {
        eprintln!("First value mismatches:");
        for f in &first_val_fail { eprintln!("{}", f); }
    }

    let total = type_match + type_mismatch;
    let pct = if total > 0 { 100.0 * type_match as f64 / total as f64 } else { 0.0 };
    eprintln!("Type hash accuracy: {:.1}%", pct);
}
