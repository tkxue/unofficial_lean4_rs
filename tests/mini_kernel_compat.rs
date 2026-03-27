//! Tests against MiniKernel.lean output from Lean 4.25.2.
//! Every value here was produced by the actual C++ kernel.

use lean4_kernel::name::Name;
use lean4_kernel::level::Level;
use lean4_kernel::expr::{Expr, BinderInfo, Literal};
use lean4_kernel::hash::hash_str;

// ============================================================================
// Name hashes — exact u64 from Lean's Name.hash computed_field
// ============================================================================

#[test]
fn test_name_hashes() {
    let cases: &[(&str, u64)] = &[
        ("Nat",        11442535297760353691),
        ("Nat.zero",   13428217069302927667),
        ("Nat.succ",   16112798088292836701),
        ("Bool",       12882480457794858234),
        ("Bool.true",  9255189395584251158),
        ("Bool.false", 15761733860085307253),
        ("Eq",         16122875713692181903),
        ("True",       11870096045526947150),
        ("True.intro", 18067798339771668657),
        ("List",       9582258842178272501),
        ("List.nil",   18135193680607614554),
        ("List.cons",  8614124190858717794),
        ("Prod",       15289851429949568889),
        ("Prod.mk",    6466355875042130293),
        ("id",         6041859491766292191),
    ];
    for &(s, expected) in cases {
        let n = Name::str(s);
        assert_eq!(n.hash(), expected, "Name('{}') hash mismatch", s);
    }
}

// ============================================================================
// Level hashes — u32 from Level.data.hash (low 32 bits of packed Data u64)
// ============================================================================

#[test]
fn test_level_hashes() {
    assert_eq!(Level::zero().hash(), 2221, "Level.zero");
    assert_eq!(Level::mk_succ(&Level::zero()).hash(), 1521422772, "Level.one");
    assert_eq!(Level::mk_succ(&Level::mk_succ(&Level::zero())).hash(), 2794655678, "Level.two");
    assert_eq!(Level::mk_param(&Name::str("u")).hash(), 2600233236, "Level.param u");
    assert_eq!(Level::mk_param(&Name::str("v")).hash(), 689783931, "Level.param v");
    assert_eq!(Level::mk_succ(&Level::mk_param(&Name::str("u"))).hash(), 2271366212, "Level.succ(param u)");
}

// ============================================================================
// Expression Data — hash, approxDepth, looseBVarRange, flags
// From EXPR lines in mini.txt, each constructed identically to the Lean code.
// ============================================================================

fn nat() -> Expr { Expr::mk_const(&Name::str("Nat"), &[]) }
fn zero() -> Expr { Expr::mk_const(&Name::str("Nat.zero"), &[]) }
fn succ() -> Expr { Expr::mk_const(&Name::str("Nat.succ"), &[]) }

struct ExprCheck {
    name: &'static str,
    hash: u32,
    depth: u32,
    bvr: u32,
    has_fvar: bool,
    has_expr_mvar: bool,
    has_level_mvar: bool,
    has_level_param: bool,
}

fn check(e: &Expr, c: &ExprCheck) {
    assert_eq!(e.hash(), c.hash, "{}: hash mismatch (got {}, want {})", c.name, e.hash(), c.hash);
    assert_eq!(e.approx_depth(), c.depth, "{}: depth", c.name);
    assert_eq!(e.loose_bvar_range(), c.bvr, "{}: looseBVarRange", c.name);
    assert_eq!(e.has_fvar(), c.has_fvar, "{}: hasFVar", c.name);
    assert_eq!(e.has_expr_mvar(), c.has_expr_mvar, "{}: hasExprMVar", c.name);
    assert_eq!(e.has_level_mvar(), c.has_level_mvar, "{}: hasLevelMVar", c.name);
    assert_eq!(e.has_univ_param(), c.has_level_param, "{}: hasLevelParam", c.name);
}

#[test]
fn test_expr_nat() {
    // Const("Nat", [])
    check(&nat(), &ExprCheck { name: "nat", hash: 421340980, depth: 0, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_zero() {
    // Const("Nat.zero", [])
    check(&zero(), &ExprCheck { name: "zero", hash: 3727131470, depth: 0, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_succ() {
    // Const("Nat.succ", [])
    check(&succ(), &ExprCheck { name: "succ", hash: 1268112261, depth: 0, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_succ_zero() {
    // App(Const("Nat.succ", []), Const("Nat.zero", []))
    let e = Expr::mk_app(&succ(), &zero());
    check(&e, &ExprCheck { name: "succZero", hash: 3644655442, depth: 1, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_prop() {
    // Sort(Zero) = Prop
    let e = Expr::mk_sort(&Level::zero());
    check(&e, &ExprCheck { name: "prop", hash: 3944470172, depth: 0, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_type0() {
    // Sort(Succ(Zero)) = Type
    let e = Expr::mk_sort(&Level::one());
    check(&e, &ExprCheck { name: "type0", hash: 3931117990, depth: 0, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_type_u() {
    // Sort(Succ(Param("u")))
    let u = Level::mk_param(&Name::str("u"));
    let e = Expr::mk_sort(&Level::mk_succ(&u));
    check(&e, &ExprCheck { name: "typeU", hash: 4105528776, depth: 0, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: true });
}

#[test]
fn test_expr_bvar0() {
    let e = Expr::mk_bvar(0);
    check(&e, &ExprCheck { name: "bv0", hash: 351589370, depth: 0, bvr: 1,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_bvar1() {
    let e = Expr::mk_bvar(1);
    check(&e, &ExprCheck { name: "bv1", hash: 2167487590, depth: 0, bvr: 2,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_id_nat() {
    // Lam("x", Const("Nat",[]), BVar(0), Default)
    let e = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
    check(&e, &ExprCheck { name: "idNat", hash: 951834654, depth: 1, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_nat_to_nat() {
    // Pi("x", Const("Nat",[]), Const("Nat",[]), Default)  i.e. Nat → Nat
    let e = Expr::mk_pi(&Name::str("x"), BinderInfo::Default, &nat(), &nat());
    check(&e, &ExprCheck { name: "natToNat", hash: 2546708756, depth: 1, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_dep_pi() {
    // Pi("x", Const("Nat",[]), BVar(0), Default)  dependent: ∀ (x : Nat), x
    let e = Expr::mk_pi(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
    // NOTE: same hash as idNat because Lambda and Pi hash identically (same formula)
    check(&e, &ExprCheck { name: "depPi", hash: 951834654, depth: 1, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_app_id_zero() {
    // App(Lam("x", Nat, #0), Const("Nat.zero",[]))
    let id_nat = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &Expr::mk_bvar(0));
    let e = Expr::mk_app(&id_nat, &zero());
    check(&e, &ExprCheck { name: "appIdZero", hash: 1204892901, depth: 2, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_let() {
    // Let("x", Nat, Nat.zero, App(Nat.succ, #0), false)
    let e = Expr::mk_let(
        &Name::str("x"), &nat(), &zero(),
        &Expr::mk_app(&succ(), &Expr::mk_bvar(0)), false,
    );
    check(&e, &ExprCheck { name: "letExpr", hash: 1619888146, depth: 2, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_lit_nat() {
    let e = Expr::mk_lit(Literal::Nat(42));
    check(&e, &ExprCheck { name: "litNat42", hash: 3764645514, depth: 0, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_lit_str() {
    let e = Expr::mk_lit(Literal::Str("hello".into()));
    check(&e, &ExprCheck { name: "litHello", hash: 1570600290, depth: 0, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_nested_lam() {
    // Lam("x", Nat, Lam("y", Nat, #1, D), D)
    let inner = Expr::mk_lambda(&Name::str("y"), BinderInfo::Default, &nat(), &Expr::mk_bvar(1));
    let e = Expr::mk_lambda(&Name::str("x"), BinderInfo::Default, &nat(), &inner);
    check(&e, &ExprCheck { name: "nestedLam", hash: 1898214596, depth: 2, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}

#[test]
fn test_expr_implicit_pi() {
    // Pi("α", Sort(1), Const("Nat",[]), Implicit)
    let type0 = Expr::mk_sort(&Level::one());
    let e = Expr::mk_pi(&Name::str("α"), BinderInfo::Implicit, &type0, &nat());
    check(&e, &ExprCheck { name: "implPi", hash: 3082712640, depth: 1, bvr: 0,
        has_fvar: false, has_expr_mvar: false, has_level_mvar: false, has_level_param: false });
}
