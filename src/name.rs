use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::hash::{hash_str, mix_hash};

// ---------------------------------------------------------------------------
// Name
// ---------------------------------------------------------------------------

/// Lean 4 hierarchical name.
///
/// Hash algorithm (from Init/Prelude.lean):
///   anonymous => 1723
///   str p s   => mixHash(p.hash, string_hash(s))
///   num p v   => mixHash(p.hash, v as u64)   (or 17 if v >= 2^64)
#[derive(Clone)]
pub struct Name(Arc<NameInner>);

#[derive(Clone)]
enum NameInner {
    Anonymous,
    Str { prefix: Name, s: String, hash: u64 },
    Num { prefix: Name, n: u64, hash: u64 },
}

impl Name {
    // -- Construction -------------------------------------------------------

    pub fn anonymous() -> Self {
        Name(Arc::new(NameInner::Anonymous))
    }

    pub fn mk_string(prefix: &Name, s: &str) -> Self {
        let sh = hash_str(s.as_bytes(), 11);
        let h = mix_hash(prefix.hash(), sh);
        Name(Arc::new(NameInner::Str {
            prefix: prefix.clone(),
            s: s.to_owned(),
            hash: h,
        }))
    }

    pub fn mk_numeral(prefix: &Name, n: u64) -> Self {
        let h = mix_hash(prefix.hash(), n);
        Name(Arc::new(NameInner::Num {
            prefix: prefix.clone(),
            n,
            hash: h,
        }))
    }

    /// Convenience: `Name::from_str("foo.bar.baz")` → hierarchical name
    pub fn from_parts(parts: &[&str]) -> Self {
        let mut n = Name::anonymous();
        for p in parts {
            n = Name::mk_string(&n, p);
        }
        n
    }

    /// Parse dot-separated string into a name.
    pub fn str(s: &str) -> Self {
        let parts: Vec<&str> = s.split('.').collect();
        Name::from_parts(&parts)
    }

    // -- Decomposition ------------------------------------------------------

    pub fn kind(&self) -> NameKind {
        match &*self.0 {
            NameInner::Anonymous => NameKind::Anonymous,
            NameInner::Str { .. } => NameKind::Str,
            NameInner::Num { .. } => NameKind::Num,
        }
    }

    pub fn is_anonymous(&self) -> bool {
        matches!(&*self.0, NameInner::Anonymous)
    }

    pub fn is_string(&self) -> bool {
        matches!(&*self.0, NameInner::Str { .. })
    }

    pub fn is_numeral(&self) -> bool {
        matches!(&*self.0, NameInner::Num { .. })
    }

    pub fn get_prefix(&self) -> &Name {
        match &*self.0 {
            NameInner::Anonymous => self,
            NameInner::Str { prefix, .. } | NameInner::Num { prefix, .. } => prefix,
        }
    }

    pub fn get_string(&self) -> &str {
        match &*self.0 {
            NameInner::Str { s, .. } => s,
            _ => panic!("Name::get_string on non-string name"),
        }
    }

    pub fn get_numeral(&self) -> u64 {
        match &*self.0 {
            NameInner::Num { n, .. } => *n,
            _ => panic!("Name::get_numeral on non-numeral name"),
        }
    }

    pub fn get_root(&self) -> Name {
        let mut n = self.clone();
        while !n.get_prefix().is_anonymous() {
            n = n.get_prefix().clone();
        }
        n
    }

    pub fn is_atomic(&self) -> bool {
        self.is_anonymous() || self.get_prefix().is_anonymous()
    }

    // -- Hash ---------------------------------------------------------------

    pub fn hash(&self) -> u64 {
        match &*self.0 {
            NameInner::Anonymous => 1723,
            NameInner::Str { hash, .. } | NameInner::Num { hash, .. } => *hash,
        }
    }

    // -- Equality (structural, like C++ lean_name_eq) -----------------------

    fn eq_inner(&self, other: &Name) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        match (&*self.0, &*other.0) {
            (NameInner::Anonymous, NameInner::Anonymous) => true,
            (
                NameInner::Str { prefix: p1, s: s1, hash: h1 },
                NameInner::Str { prefix: p2, s: s2, hash: h2 },
            ) => h1 == h2 && s1 == s2 && p1 == p2,
            (
                NameInner::Num { prefix: p1, n: n1, hash: h1 },
                NameInner::Num { prefix: p2, n: n2, hash: h2 },
            ) => h1 == h2 && n1 == n2 && p1 == p2,
            _ => false,
        }
    }

    // -- Ordering -----------------------------------------------------------
    // Matches C++ name::cmp_core: collects limbs root-to-leaf, compares
    // component-by-component. Strings sort after numerals at the same position.

    fn limbs(&self) -> Vec<Limb> {
        let mut out = Vec::new();
        let mut cur = self;
        loop {
            match &*cur.0 {
                NameInner::Anonymous => break,
                NameInner::Str { prefix, s, .. } => {
                    out.push(Limb::Str(s.clone()));
                    cur = prefix;
                }
                NameInner::Num { prefix, n, .. } => {
                    out.push(Limb::Num(*n));
                    cur = prefix;
                }
            }
        }
        out.reverse();
        out
    }

    pub fn cmp_name(&self, other: &Name) -> std::cmp::Ordering {
        let l1 = self.limbs();
        let l2 = other.limbs();
        let mut i1 = l1.iter();
        let mut i2 = l2.iter();
        loop {
            match (i1.next(), i2.next()) {
                (None, None) => return std::cmp::Ordering::Equal,
                (None, Some(_)) => return std::cmp::Ordering::Less,
                (Some(_), None) => return std::cmp::Ordering::Greater,
                (Some(a), Some(b)) => {
                    let c = a.cmp_limb(b);
                    if c != std::cmp::Ordering::Equal {
                        return c;
                    }
                }
            }
        }
    }

    pub fn quick_cmp(&self, other: &Name) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        let h1 = self.hash();
        let h2 = other.hash();
        if h1 != h2 {
            return h1.cmp(&h2);
        }
        if self == other {
            return std::cmp::Ordering::Equal;
        }
        self.cmp_name(other)
    }

    // -- Predicates ---------------------------------------------------------

    pub fn is_prefix_of(&self, other: &Name) -> bool {
        let l1 = self.limbs();
        let l2 = other.limbs();
        if l1.len() > l2.len() {
            return false;
        }
        if l1.len() == l2.len() && self.hash() != other.hash() {
            return false;
        }
        l1.iter().zip(l2.iter()).all(|(a, b)| a == b)
    }

    pub fn is_internal_name(&self) -> bool {
        let mut cur = self;
        loop {
            match &*cur.0 {
                NameInner::Anonymous => return false,
                NameInner::Str { prefix, s, .. } => {
                    if s.starts_with('_') {
                        return true;
                    }
                    cur = prefix;
                }
                NameInner::Num { prefix, .. } => {
                    cur = prefix;
                }
            }
        }
    }

    // -- String conversion --------------------------------------------------

    pub fn to_string_with_sep(&self, sep: &str) -> String {
        if self.is_anonymous() {
            return "[anonymous]".to_owned();
        }
        let limbs = self.limbs();
        let mut out = String::new();
        for (i, limb) in limbs.iter().enumerate() {
            if i > 0 {
                out.push_str(sep);
            }
            match limb {
                Limb::Str(s) => out.push_str(s),
                Limb::Num(n) => out.push_str(&n.to_string()),
            }
        }
        out
    }

    // -- Modification -------------------------------------------------------

    /// Concatenate two names: `n1 + n2`.
    pub fn append(&self, other: &Name) -> Name {
        if other.is_anonymous() {
            return self.clone();
        }
        if self.is_anonymous() {
            return other.clone();
        }
        let prefix = if other.is_atomic() {
            self.clone()
        } else {
            self.append(other.get_prefix())
        };
        match &*other.0 {
            NameInner::Str { s, .. } => Name::mk_string(&prefix, s),
            NameInner::Num { n, .. } => Name::mk_numeral(&prefix, *n),
            NameInner::Anonymous => unreachable!(),
        }
    }

    pub fn replace_prefix(&self, prefix: &Name, new_prefix: &Name) -> Name {
        if self == prefix {
            return new_prefix.clone();
        }
        if self.is_anonymous() {
            return self.clone();
        }
        let p = self.get_prefix().replace_prefix(prefix, new_prefix);
        match &*self.0 {
            NameInner::Str { s, .. } => Name::mk_string(&p, s),
            NameInner::Num { n, .. } => Name::mk_numeral(&p, *n),
            NameInner::Anonymous => unreachable!(),
        }
    }

    pub fn append_after_str(&self, suffix: &str) -> Name {
        match &*self.0 {
            NameInner::Str { prefix, s, .. } => {
                let new_s = format!("{}{}", s, suffix);
                Name::mk_string(prefix, &new_s)
            }
            _ => Name::mk_string(self, suffix),
        }
    }

    pub fn append_after_num(&self, i: u64) -> Name {
        match &*self.0 {
            NameInner::Str { prefix, s, .. } => {
                let new_s = format!("{}_{}", s, i);
                Name::mk_string(prefix, &new_s)
            }
            _ => {
                let new_s = format!("_{}", i);
                Name::mk_string(self, &new_s)
            }
        }
    }
}

// -- Unique name generator ---------------------------------------------------

static NEXT_UNIQUE_ID: AtomicU64 = AtomicU64::new(0);

pub fn mk_internal_unique_name() -> Name {
    let id = NEXT_UNIQUE_ID.fetch_add(1, Ordering::Relaxed);
    Name::mk_numeral(&Name::anonymous(), id)
}

// -- Limb helper for ordering ------------------------------------------------

#[derive(Clone, PartialEq, Eq)]
enum Limb {
    Str(String),
    Num(u64),
}

impl Limb {
    fn cmp_limb(&self, other: &Limb) -> std::cmp::Ordering {
        match (self, other) {
            (Limb::Str(a), Limb::Str(b)) => a.cmp(b),
            (Limb::Num(a), Limb::Num(b)) => a.cmp(b),
            // C++: STRING kind > NUMERAL kind, so Str sorts after Num
            (Limb::Str(_), Limb::Num(_)) => std::cmp::Ordering::Greater,
            (Limb::Num(_), Limb::Str(_)) => std::cmp::Ordering::Less,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NameKind {
    Anonymous,
    Str,
    Num,
}

// -- Trait impls -------------------------------------------------------------

impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        self.eq_inner(other)
    }
}
impl Eq for Name {}

impl std::hash::Hash for Name {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash());
    }
}

impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp_name(other))
    }
}

impl Ord for Name {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.cmp_name(other)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_string_with_sep("."))
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Name({})", self)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_anonymous() {
        let a = Name::anonymous();
        assert!(a.is_anonymous());
        assert_eq!(a.hash(), 1723);
        assert_eq!(a.to_string(), "[anonymous]");
    }

    #[test]
    fn test_simple_string() {
        let n = Name::mk_string(&Name::anonymous(), "Nat");
        assert!(n.is_string());
        assert_eq!(n.get_string(), "Nat");
        assert!(n.get_prefix().is_anonymous());
        assert_eq!(n.to_string(), "Nat");
    }

    #[test]
    fn test_hierarchical() {
        let n = Name::str("Lean.Elab.Term");
        assert_eq!(n.to_string(), "Lean.Elab.Term");
        assert_eq!(n.get_string(), "Term");
        assert_eq!(n.get_prefix().to_string(), "Lean.Elab");
    }

    #[test]
    fn test_numeral() {
        let a = Name::anonymous();
        let n = Name::mk_numeral(&a, 42);
        assert!(n.is_numeral());
        assert_eq!(n.get_numeral(), 42);
        assert_eq!(n.to_string(), "42");
    }

    #[test]
    fn test_mixed() {
        let a = Name::anonymous();
        let n1 = Name::mk_string(&a, "_uniq");
        let n2 = Name::mk_numeral(&n1, 231);
        assert_eq!(n2.to_string(), "_uniq.231");
    }

    #[test]
    fn test_equality() {
        let a = Name::str("Nat.succ");
        let b = Name::str("Nat.succ");
        let c = Name::str("Nat.pred");
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn test_hash_consistency() {
        let a = Name::str("Nat.succ");
        let b = Name::str("Nat.succ");
        assert_eq!(a.hash(), b.hash());
    }

    #[test]
    fn test_ordering() {
        // Numerals sort before strings at the same position
        let num = Name::mk_numeral(&Name::anonymous(), 1);
        let str_ = Name::mk_string(&Name::anonymous(), "a");
        assert!(num < str_);

        // Lexicographic for strings
        let a = Name::str("A");
        let b = Name::str("B");
        assert!(a < b);
    }

    #[test]
    fn test_is_prefix_of() {
        let lean = Name::str("Lean");
        let lean_elab = Name::str("Lean.Elab");
        let lean_elab_term = Name::str("Lean.Elab.Term");
        let other = Name::str("Std");

        assert!(lean.is_prefix_of(&lean));
        assert!(lean.is_prefix_of(&lean_elab));
        assert!(lean.is_prefix_of(&lean_elab_term));
        assert!(!lean_elab.is_prefix_of(&lean));
        assert!(!other.is_prefix_of(&lean_elab));
    }

    #[test]
    fn test_append() {
        let a = Name::str("Lean");
        let b = Name::str("Elab.Term");
        let c = a.append(&b);
        assert_eq!(c.to_string(), "Lean.Elab.Term");
    }

    #[test]
    fn test_get_root() {
        let n = Name::str("Lean.Elab.Term");
        let root = n.get_root();
        assert_eq!(root.to_string(), "Lean");
    }

    #[test]
    fn test_replace_prefix() {
        let n = Name::str("Lean.Elab.Term");
        let old_prefix = Name::str("Lean");
        let new_prefix = Name::str("My");
        let result = n.replace_prefix(&old_prefix, &new_prefix);
        assert_eq!(result.to_string(), "My.Elab.Term");
    }

    #[test]
    fn test_is_internal_name() {
        let n = Name::str("_private.Lean.Elab");
        assert!(n.is_internal_name());
        let n2 = Name::str("Lean.Elab");
        assert!(!n2.is_internal_name());
    }

    #[test]
    fn test_unique_names() {
        let a = mk_internal_unique_name();
        let b = mk_internal_unique_name();
        assert_ne!(a, b);
    }

    #[test]
    fn test_append_after() {
        let n = Name::str("Lean.foo");
        let n2 = n.append_after_num(3);
        assert_eq!(n2.to_string(), "Lean.foo_3");
    }

    #[test]
    fn test_sort_stability() {
        // Sort a list of names, verify deterministic
        let mut names: Vec<Name> = vec![
            Name::str("C"), Name::str("A"), Name::str("B"),
            Name::str("A.B"), Name::str("A.A"),
        ];
        names.sort();
        let strs: Vec<String> = names.iter().map(|n| n.to_string()).collect();
        assert_eq!(strs, vec!["A", "A.A", "A.B", "B", "C"]);
    }
}
