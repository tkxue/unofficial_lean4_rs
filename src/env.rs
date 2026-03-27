//! Stage 03: Declarations & Environment.

use std::collections::HashMap;
use std::sync::Arc;

use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

// ============================================================================
// Reducibility hints
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReducibilityHints {
    Opaque,
    Abbreviation,
    Regular(u32),
}

impl ReducibilityHints {
    /// C++ `compare(h1, h2)`:
    /// <0 if f1 should be unfolded, ==0 both, >0 if f2 should be unfolded.
    pub fn cmp_unfold(&self, other: &ReducibilityHints) -> i32 {
        use ReducibilityHints::*;
        match (self, other) {
            (Opaque, Opaque) => 0,
            (Opaque, _) => 1,       // unfold other
            (_, Opaque) => -1,      // unfold self
            (Abbreviation, Abbreviation) => 0,
            (Abbreviation, _) => -1, // unfold self (abbrev always unfolds)
            (_, Abbreviation) => 1,  // unfold other
            (Regular(h1), Regular(h2)) => {
                if h1 == h2 { 0 }
                else if h1 > h2 { -1 } // unfold higher height first
                else { 1 }
            }
        }
    }
}

// ============================================================================
// Definition safety
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

// ============================================================================
// Quotient kind
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Mk,
    Lift,
    Ind,
}

// ============================================================================
// Recursor rule
// ============================================================================

#[derive(Clone, Debug)]
pub struct RecursorRule {
    pub ctor_name: Name,
    pub nfields: u32,
    pub rhs: Expr,
}

// ============================================================================
// ConstantInfo — what is stored in the environment
// ============================================================================

#[derive(Clone, Debug)]
pub struct ConstantInfo {
    pub name: Name,
    pub lparams: Vec<Name>,
    pub type_: Expr,
    pub kind: ConstantInfoKind,
}

#[derive(Clone, Debug)]
pub enum ConstantInfoKind {
    Axiom {
        is_unsafe: bool,
    },
    Definition {
        value: Expr,
        hints: ReducibilityHints,
        safety: DefinitionSafety,
    },
    Theorem {
        value: Expr,
    },
    Opaque {
        value: Expr,
        is_unsafe: bool,
    },
    Inductive {
        nparams: u32,
        nindices: u32,
        all: Vec<Name>,
        ctors: Vec<Name>,
        nnested: u32,
        is_rec: bool,
        is_unsafe: bool,
        is_reflexive: bool,
    },
    Constructor {
        induct_name: Name,
        cidx: u32,
        nparams: u32,
        nfields: u32,
        is_unsafe: bool,
    },
    Recursor {
        all: Vec<Name>,
        nparams: u32,
        nindices: u32,
        nmotives: u32,
        nminors: u32,
        rules: Vec<RecursorRule>,
        k: bool,
        is_unsafe: bool,
    },
    Quot {
        kind: QuotKind,
    },
}

impl ConstantInfo {
    pub fn get_name(&self) -> &Name { &self.name }
    pub fn get_lparams(&self) -> &[Name] { &self.lparams }
    pub fn get_num_lparams(&self) -> usize { self.lparams.len() }
    pub fn get_type(&self) -> &Expr { &self.type_ }

    pub fn get_value(&self) -> Option<&Expr> {
        match &self.kind {
            ConstantInfoKind::Definition { value, .. }
            | ConstantInfoKind::Theorem { value, .. }
            | ConstantInfoKind::Opaque { value, .. } => Some(value),
            _ => None,
        }
    }

    pub fn has_value(&self) -> bool { self.get_value().is_some() }

    pub fn get_hints(&self) -> Option<&ReducibilityHints> {
        match &self.kind {
            ConstantInfoKind::Definition { hints, .. } => Some(hints),
            _ => None,
        }
    }

    pub fn is_definition(&self) -> bool { matches!(&self.kind, ConstantInfoKind::Definition { .. }) }
    pub fn is_axiom(&self) -> bool { matches!(&self.kind, ConstantInfoKind::Axiom { .. }) }
    pub fn is_theorem(&self) -> bool { matches!(&self.kind, ConstantInfoKind::Theorem { .. }) }
    pub fn is_opaque(&self) -> bool { matches!(&self.kind, ConstantInfoKind::Opaque { .. }) }
    pub fn is_inductive(&self) -> bool { matches!(&self.kind, ConstantInfoKind::Inductive { .. }) }
    pub fn is_constructor(&self) -> bool { matches!(&self.kind, ConstantInfoKind::Constructor { .. }) }
    pub fn is_recursor(&self) -> bool { matches!(&self.kind, ConstantInfoKind::Recursor { .. }) }
    pub fn is_quot(&self) -> bool { matches!(&self.kind, ConstantInfoKind::Quot { .. }) }

    pub fn is_unsafe(&self) -> bool {
        match &self.kind {
            ConstantInfoKind::Axiom { is_unsafe, .. }
            | ConstantInfoKind::Opaque { is_unsafe, .. }
            | ConstantInfoKind::Inductive { is_unsafe, .. }
            | ConstantInfoKind::Constructor { is_unsafe, .. }
            | ConstantInfoKind::Recursor { is_unsafe, .. } => *is_unsafe,
            ConstantInfoKind::Definition { safety, .. } => *safety == DefinitionSafety::Unsafe,
            ConstantInfoKind::Theorem { .. } | ConstantInfoKind::Quot { .. } => false,
        }
    }
}

// ============================================================================
// Declaration — submitted to kernel for checking
// ============================================================================

#[derive(Clone, Debug)]
pub enum Declaration {
    Axiom {
        name: Name,
        lparams: Vec<Name>,
        type_: Expr,
        is_unsafe: bool,
    },
    Definition {
        name: Name,
        lparams: Vec<Name>,
        type_: Expr,
        value: Expr,
        hints: ReducibilityHints,
        safety: DefinitionSafety,
    },
    Theorem {
        name: Name,
        lparams: Vec<Name>,
        type_: Expr,
        value: Expr,
    },
    Opaque {
        name: Name,
        lparams: Vec<Name>,
        type_: Expr,
        value: Expr,
        is_unsafe: bool,
    },
    Mutual {
        defs: Vec<Declaration>,
    },
    Inductive {
        lparams: Vec<Name>,
        nparams: u32,
        types: Vec<InductiveType>,
        is_unsafe: bool,
    },
}

#[derive(Clone, Debug)]
pub struct InductiveType {
    pub name: Name,
    pub type_: Expr,
    pub ctors: Vec<Constructor>,
}

#[derive(Clone, Debug)]
pub struct Constructor {
    pub name: Name,
    pub type_: Expr,
}

// ============================================================================
// Environment
// ============================================================================

#[derive(Clone, Debug)]
pub struct Environment {
    constants: Arc<HashMap<Name, Arc<ConstantInfo>>>,
    quot_initialized: bool,
    trust_level: u32,
}

/// Believer trust threshold: when trust >= this, skip type-checking.
pub const LEAN_BELIEVER_TRUST_LEVEL: u32 = 1024;

#[derive(Debug, Clone)]
pub struct EnvError(pub String);

impl std::fmt::Display for EnvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for EnvError {}

impl Environment {
    pub fn new(trust_level: u32) -> Self {
        Environment {
            constants: Arc::new(HashMap::new()),
            quot_initialized: false,
            trust_level,
        }
    }

    pub fn trust_level(&self) -> u32 { self.trust_level }

    /// Bulk-construct an environment from a pre-built map.
    pub fn from_constants(constants: HashMap<Name, Arc<ConstantInfo>>, trust_level: u32) -> Self {
        Environment {
            constants: Arc::new(constants),
            quot_initialized: false,
            trust_level,
        }
    }

    /// Look up a constant by name.
    pub fn find(&self, name: &Name) -> Option<Arc<ConstantInfo>> {
        self.constants.get(name).cloned()
    }

    /// Look up a constant, panic if missing.
    pub fn get(&self, name: &Name) -> Arc<ConstantInfo> {
        self.find(name).unwrap_or_else(|| panic!("unknown constant: {}", name))
    }

    /// Check that a name is not already in the environment.
    pub fn check_name(&self, name: &Name) -> Result<(), EnvError> {
        if self.constants.contains_key(name) {
            Err(EnvError(format!("already declared: {}", name)))
        } else {
            Ok(())
        }
    }

    /// Check that level parameters have no duplicates.
    pub fn check_no_dup_lparams(lparams: &[Name]) -> Result<(), EnvError> {
        for (i, p) in lparams.iter().enumerate() {
            for q in &lparams[i + 1..] {
                if p == q {
                    return Err(EnvError(format!("duplicate universe parameter: {}", p)));
                }
            }
        }
        Ok(())
    }

    /// Add a pre-checked constant info to the environment. Returns a new environment.
    pub fn add_constant_info(&self, info: ConstantInfo) -> Result<Environment, EnvError> {
        self.check_name(&info.name)?;
        let mut new_map = (*self.constants).clone();
        new_map.insert(info.name.clone(), Arc::new(info));
        Ok(Environment {
            constants: Arc::new(new_map),
            quot_initialized: self.quot_initialized,
            trust_level: self.trust_level,
        })
    }

    /// Replace a constant (or add if new). Used for recursive defs.
    pub fn replace_constant_info(&self, info: ConstantInfo) -> Environment {
        let mut new_map = (*self.constants).clone();
        new_map.insert(info.name.clone(), Arc::new(info));
        Environment {
            constants: Arc::new(new_map),
            quot_initialized: self.quot_initialized,
            trust_level: self.trust_level,
        }
    }

    /// Iterate over all constants.
    pub fn for_each_constant(&self, mut f: impl FnMut(&Name, &ConstantInfo)) {
        for (name, info) in self.constants.iter() {
            f(name, info);
        }
    }

    /// Number of constants in the environment.
    pub fn num_constants(&self) -> usize { self.constants.len() }

    /// Whether quotient types have been initialized.
    pub fn is_quot_initialized(&self) -> bool { self.quot_initialized }

    /// Mark quotient as initialized (called after adding Quot constants).
    pub fn set_quot_initialized(mut self) -> Self {
        self.quot_initialized = true;
        self
    }

    /// Is this a "believer" environment that skips type-checking?
    pub fn is_believer(&self) -> bool {
        self.trust_level >= LEAN_BELIEVER_TRUST_LEVEL
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Expr;
    use crate::level::Level;
    use crate::name::Name;

    fn nat_type() -> Expr { Expr::mk_const(&Name::str("Nat"), &[]) }

    fn mk_axiom_info(name: &str, ty: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::str(name),
            lparams: vec![],
            type_: ty,
            kind: ConstantInfoKind::Axiom { is_unsafe: false },
        }
    }

    fn mk_def_info(name: &str, ty: Expr, val: Expr, height: u32) -> ConstantInfo {
        ConstantInfo {
            name: Name::str(name),
            lparams: vec![],
            type_: ty,
            kind: ConstantInfoKind::Definition {
                value: val,
                hints: ReducibilityHints::Regular(height),
                safety: DefinitionSafety::Safe,
            },
        }
    }

    #[test]
    fn test_empty_env() {
        let env = Environment::new(0);
        assert_eq!(env.num_constants(), 0);
        assert!(env.find(&Name::str("Nat")).is_none());
    }

    #[test]
    fn test_add_and_find() {
        let env = Environment::new(0);
        let info = mk_axiom_info("Nat", Expr::mk_type());
        let env2 = env.add_constant_info(info).unwrap();
        assert_eq!(env2.num_constants(), 1);
        let found = env2.find(&Name::str("Nat")).unwrap();
        assert_eq!(found.get_name(), &Name::str("Nat"));
        assert!(found.is_axiom());
    }

    #[test]
    fn test_immutability() {
        let env = Environment::new(0);
        let info = mk_axiom_info("Nat", Expr::mk_type());
        let env2 = env.add_constant_info(info).unwrap();
        // env still has 0 constants
        assert_eq!(env.num_constants(), 0);
        assert_eq!(env2.num_constants(), 1);
    }

    #[test]
    fn test_duplicate_rejected() {
        let env = Environment::new(0);
        let info = mk_axiom_info("Nat", Expr::mk_type());
        let env2 = env.add_constant_info(info.clone()).unwrap();
        let result = env2.add_constant_info(info);
        assert!(result.is_err());
    }

    #[test]
    fn test_multiple_adds() {
        let env = Environment::new(0);
        let env = env.add_constant_info(mk_axiom_info("Nat", Expr::mk_type())).unwrap();
        let env = env.add_constant_info(mk_axiom_info("Bool", Expr::mk_type())).unwrap();
        let env = env.add_constant_info(mk_axiom_info("String", Expr::mk_type())).unwrap();
        assert_eq!(env.num_constants(), 3);
        assert!(env.find(&Name::str("Bool")).is_some());
    }

    #[test]
    fn test_for_each_constant() {
        let env = Environment::new(0);
        let env = env.add_constant_info(mk_axiom_info("A", Expr::mk_type())).unwrap();
        let env = env.add_constant_info(mk_axiom_info("B", Expr::mk_type())).unwrap();
        let mut names = Vec::new();
        env.for_each_constant(|n, _| names.push(n.to_string()));
        names.sort();
        assert_eq!(names, vec!["A", "B"]);
    }

    #[test]
    fn test_get_panics() {
        let env = Environment::new(0);
        let result = std::panic::catch_unwind(|| env.get(&Name::str("missing")));
        assert!(result.is_err());
    }

    #[test]
    fn test_definition_info() {
        let val = Expr::mk_const(&Name::str("Nat.zero"), &[]);
        let info = mk_def_info("myConst", nat_type(), val.clone(), 5);
        assert!(info.is_definition());
        assert_eq!(info.get_value(), Some(&val));
        assert_eq!(info.get_hints(), Some(&ReducibilityHints::Regular(5)));
        assert!(!info.is_unsafe());
    }

    #[test]
    fn test_theorem_info() {
        let val = Expr::mk_const(&Name::str("trivial"), &[]);
        let info = ConstantInfo {
            name: Name::str("myThm"),
            lparams: vec![],
            type_: Expr::mk_prop(),
            kind: ConstantInfoKind::Theorem { value: val.clone() },
        };
        assert!(info.is_theorem());
        assert_eq!(info.get_value(), Some(&val));
        assert!(!info.is_unsafe());
    }

    #[test]
    fn test_opaque_info() {
        let info = ConstantInfo {
            name: Name::str("myOpaque"),
            lparams: vec![],
            type_: nat_type(),
            kind: ConstantInfoKind::Opaque {
                value: Expr::mk_const(&Name::str("Nat.zero"), &[]),
                is_unsafe: true,
            },
        };
        assert!(info.is_opaque());
        assert!(info.is_unsafe());
    }

    #[test]
    fn test_reducibility_hints_cmp() {
        let opaque = ReducibilityHints::Opaque;
        let abbrev = ReducibilityHints::Abbreviation;
        let r5 = ReducibilityHints::Regular(5);
        let r10 = ReducibilityHints::Regular(10);

        // Opaque vs Regular: unfold Regular
        assert!(opaque.cmp_unfold(&r5) > 0);
        // Abbrev vs Regular: unfold Abbrev
        assert!(abbrev.cmp_unfold(&r5) < 0);
        // Regular(10) vs Regular(5): unfold 10 (higher)
        assert!(r10.cmp_unfold(&r5) < 0);
        // Same height: unfold both
        assert_eq!(r5.cmp_unfold(&r5), 0);
    }

    #[test]
    fn test_check_no_dup_lparams() {
        assert!(Environment::check_no_dup_lparams(&[Name::str("u"), Name::str("v")]).is_ok());
        assert!(Environment::check_no_dup_lparams(&[Name::str("u"), Name::str("u")]).is_err());
    }

    #[test]
    fn test_quot_initialized() {
        let env = Environment::new(0);
        assert!(!env.is_quot_initialized());
        let env = env.set_quot_initialized();
        assert!(env.is_quot_initialized());
    }

    #[test]
    fn test_trust_level() {
        let env = Environment::new(0);
        assert!(!env.is_believer());
        let env2 = Environment::new(LEAN_BELIEVER_TRUST_LEVEL);
        assert!(env2.is_believer());
    }

    #[test]
    fn test_constructor_info() {
        let info = ConstantInfo {
            name: Name::str("Nat.zero"),
            lparams: vec![],
            type_: nat_type(),
            kind: ConstantInfoKind::Constructor {
                induct_name: Name::str("Nat"),
                cidx: 0,
                nparams: 0,
                nfields: 0,
                is_unsafe: false,
            },
        };
        assert!(info.is_constructor());
        assert!(!info.is_unsafe());
    }

    #[test]
    fn test_recursor_info() {
        let info = ConstantInfo {
            name: Name::str("Nat.rec"),
            lparams: vec![Name::str("u")],
            type_: Expr::mk_type(), // simplified
            kind: ConstantInfoKind::Recursor {
                all: vec![Name::str("Nat")],
                nparams: 0,
                nindices: 0,
                nmotives: 1,
                nminors: 2,
                rules: vec![
                    RecursorRule { ctor_name: Name::str("Nat.zero"), nfields: 0, rhs: Expr::mk_bvar(0) },
                    RecursorRule { ctor_name: Name::str("Nat.succ"), nfields: 2, rhs: Expr::mk_bvar(0) },
                ],
                k: false,
                is_unsafe: false,
            },
        };
        assert!(info.is_recursor());
        assert_eq!(info.get_num_lparams(), 1);
    }

    #[test]
    fn test_quot_info() {
        let info = ConstantInfo {
            name: Name::str("Quot"),
            lparams: vec![Name::str("u")],
            type_: Expr::mk_type(),
            kind: ConstantInfoKind::Quot { kind: QuotKind::Type },
        };
        assert!(info.is_quot());
        assert!(!info.is_unsafe());
    }

    #[test]
    fn test_inductive_info() {
        let info = ConstantInfo {
            name: Name::str("Nat"),
            lparams: vec![],
            type_: Expr::mk_type(),
            kind: ConstantInfoKind::Inductive {
                nparams: 0,
                nindices: 0,
                all: vec![Name::str("Nat")],
                ctors: vec![Name::str("Nat.zero"), Name::str("Nat.succ")],
                nnested: 0,
                is_rec: true,
                is_unsafe: false,
                is_reflexive: false,
            },
        };
        assert!(info.is_inductive());
    }

    #[test]
    fn test_with_lparams() {
        let u = Level::mk_param(&Name::str("u"));
        let info = ConstantInfo {
            name: Name::str("List"),
            lparams: vec![Name::str("u")],
            type_: Expr::mk_sort(&Level::mk_succ(&u)),
            kind: ConstantInfoKind::Inductive {
                nparams: 1,
                nindices: 0,
                all: vec![Name::str("List")],
                ctors: vec![Name::str("List.nil"), Name::str("List.cons")],
                nnested: 0,
                is_rec: true,
                is_unsafe: false,
                is_reflexive: false,
            },
        };
        assert_eq!(info.get_num_lparams(), 1);
        assert_eq!(info.get_lparams()[0], Name::str("u"));
    }
}
