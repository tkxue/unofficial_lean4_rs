//! Tests against real Lean 4.25.2 kernel output.
//!
//! The expected values were produced by running ExportDecls.lean with
//! `lean --run` which calls the actual C++ kernel's hash functions.

use lean4_kernel::name::Name;
use lean4_kernel::level::Level;
use lean4_kernel::expr::Expr;

// ============================================================================
// Name hash tests — exact values from Lean 4.25.2 C++ kernel
// ============================================================================

#[test]
fn test_name_hashes_match_lean() {
    let cases: &[(&str, u64)] = &[
        ("Nat",        11442535297760353691),
        ("Nat.zero",   13428217069302927667),
        ("Nat.succ",   16112798088292836701),
        ("Bool",       12882480457794858234),
        ("Bool.true",  9255189395584251158),
        ("Bool.false", 15761733860085307253),
        ("Eq",         16122875713692181903),
        ("Eq.refl",    13480818501600609864),
        ("True",       11870096045526947150),
        ("True.intro", 18067798339771668657),
        ("Quot",       14456664134214385499),
        ("Quot.mk",    17886754359162270207),
        ("Quot.lift",  5821404849734319451),
        ("Quot.ind",   4362047871608542614),
        ("id",         6041859491766292191),
        ("List",       9582258842178272501),
        ("List.nil",   18135193680607614554),
        ("List.cons",  8614124190858717794),
        ("String",     3136308715950998022),
        ("Char",       14164462494711235346),
    ];
    for &(name_str, expected_hash) in cases {
        let name = Name::str(name_str);
        assert_eq!(name.hash(), expected_hash,
            "Name hash mismatch for '{}': got {} expected {}",
            name_str, name.hash(), expected_hash);
    }
}

// ============================================================================
// Level hash tests — exact values from Lean 4.25.2 C++ kernel
// ============================================================================

#[test]
fn test_level_hashes_match_lean() {
    // zero => 2221
    assert_eq!(Level::zero().hash(), 2221, "Level.zero hash");

    // one => 1521422772
    let one = Level::mk_succ(&Level::zero());
    assert_eq!(one.hash(), 1521422772, "Level.one hash");

    // two => 2794655678
    let two = Level::mk_succ(&one);
    assert_eq!(two.hash(), 2794655678, "Level.two hash");

    // param u => 2600233236
    let u = Level::mk_param(&Name::str("u"));
    assert_eq!(u.hash(), 2600233236, "Level.param u hash");

    // param v => 689783931
    let v = Level::mk_param(&Name::str("v"));
    assert_eq!(v.hash(), 689783931, "Level.param v hash");

    // succ u => 2271366212
    let su = Level::mk_succ(&u);
    assert_eq!(su.hash(), 2271366212, "Level.succ u hash");
}

// ============================================================================
// Expression type hash tests — exact values from Lean 4.25.2 C++ kernel
//
// These test that when we construct the types of well-known constants
// using the same structure Lean uses, we get the same Expr.Data.hash.
// ============================================================================

/// Nat : Sort 1  (i.e. Type)
/// type of Nat = Sort(succ(zero))
#[test]
fn test_expr_hash_nat_type() {
    // Nat's type is Sort(1) = Type
    // The Lean output says: EXPR_DATA Nat hash:3931117990
    let ty = Expr::mk_sort(&Level::one());
    assert_eq!(ty.hash(), 3931117990, "Nat type hash (Sort 1)");
}

/// Nat.zero : Nat
/// type = Const("Nat", [])
#[test]
fn test_expr_hash_nat_zero_type() {
    // Lean says: EXPR_DATA Nat.zero hash:421340980
    let ty = Expr::mk_const(&Name::str("Nat"), &[]);
    assert_eq!(ty.hash(), 421340980, "Nat.zero type hash");
}

/// Bool.true : Bool  and  Bool.false : Bool
/// Both have the same type hash since they're both Const("Bool", [])
#[test]
fn test_expr_hash_bool_type() {
    let ty = Expr::mk_const(&Name::str("Bool"), &[]);
    assert_eq!(ty.hash(), 183048209, "Bool constant type hash");
}

/// True : Prop
/// type = Sort(0) = Prop
#[test]
fn test_expr_hash_true_type() {
    // Lean says: EXPR_DATA True hash:3944470172
    // True's type is Prop = Sort(0)
    let ty = Expr::mk_sort(&Level::zero());
    // But wait — Lean says Nat and Bool and String and Char all have hash 3931117990
    // which is Sort(1). True has 3944470172 which is Sort(0).
    assert_eq!(ty.hash(), 3944470172, "True type hash (Prop = Sort 0)");
}

/// True.intro : True
/// type = Const("True", [])
#[test]
fn test_expr_hash_true_intro_type() {
    let ty = Expr::mk_const(&Name::str("True"), &[]);
    assert_eq!(ty.hash(), 3270818714, "True.intro type hash");
}

/// String : Sort 1 — same hash as Nat's type
#[test]
fn test_expr_hash_string_type() {
    let ty = Expr::mk_sort(&Level::one());
    assert_eq!(ty.hash(), 3931117990, "String type hash");
}

/// Char : Sort 1 — same hash
#[test]
fn test_expr_hash_char_type() {
    let ty = Expr::mk_sort(&Level::one());
    assert_eq!(ty.hash(), 3931117990, "Char type hash");
}

/// Nat.succ : Nat → Nat
/// type = Pi("n", Const("Nat",[]), Const("Nat",[]))
#[test]
fn test_expr_hash_nat_succ_type() {
    // Lean says: hash:2546708756 depth:1
    use lean4_kernel::expr::BinderInfo;
    let nat = Expr::mk_const(&Name::str("Nat"), &[]);
    let ty = Expr::mk_pi(&Name::str("n"), BinderInfo::Default, &nat, &nat);
    assert_eq!(ty.hash(), 2546708756, "Nat.succ type hash");
    assert_eq!(ty.approx_depth(), 1, "Nat.succ type depth");
    assert_eq!(ty.loose_bvar_range(), 0);
    assert!(!ty.has_fvar());
    assert!(!ty.has_expr_mvar());
    assert!(!ty.has_level_mvar());
    assert!(!ty.has_univ_param());
}

/// List : Sort(succ u) → Sort(succ u)
/// type = Pi(α, Sort(succ(param u)), Sort(succ(param u)))
/// But actually List's type is: Type u → Type u = Sort(succ u) → Sort(succ u)
/// which is Pi("α", Sort(succ(param u)), Sort(succ(param u)))
#[test]
fn test_expr_hash_list_type() {
    // Lean says: EXPR_DATA List hash:3807510281 depth:1 lparam:true
    use lean4_kernel::expr::BinderInfo;
    let u = Level::mk_param(&Name::str("u"));
    let su = Level::mk_succ(&u);
    let sort_su = Expr::mk_sort(&su);
    let ty = Expr::mk_pi(&Name::str("α"), BinderInfo::Default, &sort_su, &sort_su);
    assert_eq!(ty.hash(), 3807510281, "List type hash");
    assert_eq!(ty.approx_depth(), 1);
    assert!(ty.has_univ_param());
    assert!(!ty.has_fvar());
}

// ============================================================================
// Cross-validation: verify flags match Lean output exactly
// ============================================================================

#[test]
fn test_expr_flags_match_lean() {
    use lean4_kernel::expr::BinderInfo;

    // Nat.succ type: Pi Nat Nat — depth:1 bvr:0 fvar:false emvar:false lmvar:false lparam:false
    let nat = Expr::mk_const(&Name::str("Nat"), &[]);
    let succ_ty = Expr::mk_pi(&Name::str("n"), BinderInfo::Default, &nat, &nat);
    assert_eq!(succ_ty.approx_depth(), 1);
    assert_eq!(succ_ty.loose_bvar_range(), 0);
    assert!(!succ_ty.has_fvar());
    assert!(!succ_ty.has_expr_mvar());
    assert!(!succ_ty.has_level_mvar());
    assert!(!succ_ty.has_univ_param());

    // List type: Pi Sort(succ u) Sort(succ u) — depth:1 lparam:true
    let u = Level::mk_param(&Name::str("u"));
    let su = Level::mk_succ(&u);
    let sort_su = Expr::mk_sort(&su);
    let list_ty = Expr::mk_pi(&Name::str("α"), BinderInfo::Default, &sort_su, &sort_su);
    assert_eq!(list_ty.approx_depth(), 1);
    assert_eq!(list_ty.loose_bvar_range(), 0);
    assert!(!list_ty.has_fvar());
    assert!(!list_ty.has_expr_mvar());
    assert!(!list_ty.has_level_mvar());
    assert!(list_ty.has_univ_param());
}
