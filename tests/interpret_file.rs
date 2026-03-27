//! Test interpreting a real .lean file from disk.

use std::path::PathBuf;
use lean4_kernel::elaborator::interpret_lean_file;
use lean4_kernel::name::Name;

const LEAN_LIB: &str = "/home/y/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean";

#[test]
fn test_interpret_file() {
    let src = std::fs::read_to_string("/r/tmp/lean4/test_rust.lean").unwrap();
    let sp = vec![PathBuf::from(LEAN_LIB)];
    let env = interpret_lean_file(&src, &sp).unwrap();

    let expected = vec![
        "myZero", "myOne", "myId", "myConst", "myApp",
        "inc", "double", "add3", "myId2",
        "myRefl", "trivial_proof",
        "myAxiom",
        "NatToNat", "MyProp", "myPair",
        "Foo.bar", "Foo.baz", "Foo.Inner.deep",
        "mySucc",
    ];
    let mut ok = 0;
    let mut fail = 0;
    for name in &expected {
        if env.find(&Name::str(name)).is_some() {
            ok += 1;
        } else {
            fail += 1;
            eprintln!("MISSING: {}", name);
        }
    }
    eprintln!("=== File interpretation: {}/{} constants found ===", ok, ok + fail);
    assert_eq!(fail, 0, "{} constants missing", fail);
}
