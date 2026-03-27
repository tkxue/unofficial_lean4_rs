use std::fmt;
use std::sync::Arc;

use crate::hash::mix_hash;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Level
// ---------------------------------------------------------------------------

/// Lean 4 universe level.
///
/// Hash algorithm (from Lean/Level.lean):
///   zero       => mkData 2221
///   succ u     => mkData (mixHash 2243 u.data.hash)
///   max u v    => mkData (mixHash 2251 (mixHash u.data.hash v.data.hash))
///   imax u v   => mkData (mixHash 2267 (mixHash u.data.hash v.data.hash))
///   param n    => mkData (mixHash 2239 (hash n))
///   mvar n     => mkData (mixHash 2237 (hash n))
#[derive(Clone)]
pub struct Level(Arc<LevelInner>);

struct LevelInner {
    kind: LevelKindData,
    data: LevelData,
}

/// Cached metadata, matches Lean's `Level.Data` (packed u64).
/// Hash is truncated to u32 to match `lean_level_mk_data` which does `uint32_t h1 = h;`.
#[derive(Clone, Copy)]
struct LevelData {
    hash: u64,      // stored as full u64 but only low 32 bits are the hash
    depth: u32,     // 24 bits in Lean, we use u32
    has_mvar: bool,
    has_param: bool,
}

/// Truncate hash to u32 like C++ `lean_level_mk_data` does.
#[inline]
fn level_hash(h: u64) -> u64 {
    (h as u32) as u64
}

#[derive(Clone)]
enum LevelKindData {
    Zero,
    Succ(Level),
    Max(Level, Level),
    IMax(Level, Level),
    Param(Name),
    MVar(Name),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LevelKind {
    Zero = 0,
    Succ = 1,
    Max = 2,
    IMax = 3,
    Param = 4,
    MVar = 5,
}

impl Level {
    // -- Internal construction with data ------------------------------------

    fn new(kind: LevelKindData, data: LevelData) -> Self {
        Level(Arc::new(LevelInner { kind, data }))
    }

    // -- Construction -------------------------------------------------------

    pub fn zero() -> Self {
        Level::new(
            LevelKindData::Zero,
            LevelData { hash: 2221, depth: 0, has_mvar: false, has_param: false },
        )
    }

    pub fn mk_succ(l: &Level) -> Self {
        let d = l.data();
        let depth = d.depth.saturating_add(1);
        Level::new(
            LevelKindData::Succ(l.clone()),
            LevelData {
                hash: level_hash(mix_hash(2243, d.hash)),
                depth,
                has_mvar: d.has_mvar,
                has_param: d.has_param,
            },
        )
    }

    pub fn mk_max_core(l1: &Level, l2: &Level) -> Self {
        let d1 = l1.data();
        let d2 = l2.data();
        let depth = d1.depth.max(d2.depth).saturating_add(1);
        Level::new(
            LevelKindData::Max(l1.clone(), l2.clone()),
            LevelData {
                hash: level_hash(mix_hash(2251, mix_hash(d1.hash, d2.hash))),
                depth,
                has_mvar: d1.has_mvar || d2.has_mvar,
                has_param: d1.has_param || d2.has_param,
            },
        )
    }

    pub fn mk_imax_core(l1: &Level, l2: &Level) -> Self {
        let d1 = l1.data();
        let d2 = l2.data();
        let depth = d1.depth.max(d2.depth).saturating_add(1);
        Level::new(
            LevelKindData::IMax(l1.clone(), l2.clone()),
            LevelData {
                hash: level_hash(mix_hash(2267, mix_hash(d1.hash, d2.hash))),
                depth,
                has_mvar: d1.has_mvar || d2.has_mvar,
                has_param: d1.has_param || d2.has_param,
            },
        )
    }

    /// Smart constructor for max with simplifications (matches C++ mk_max).
    pub fn mk_max(l1: &Level, l2: &Level) -> Self {
        if l1.is_explicit() && l2.is_explicit() {
            return if l1.depth() >= l2.depth() { l1.clone() } else { l2.clone() };
        }
        if l1 == l2 {
            return l1.clone();
        }
        if l1.is_zero() {
            return l2.clone();
        }
        if l2.is_zero() {
            return l1.clone();
        }
        // if l2 == max l1 _, then max l1 l2 == l2
        if let LevelKindData::Max(lhs, rhs) = &l2.0.kind {
            if lhs == l1 || rhs == l1 {
                return l2.clone();
            }
        }
        if let LevelKindData::Max(lhs, rhs) = &l1.0.kind {
            if lhs == l2 || rhs == l2 {
                return l1.clone();
            }
        }
        // Same base, different offsets
        let (b1, o1) = l1.to_offset();
        let (b2, o2) = l2.to_offset();
        if b1 == b2 {
            return if o1 > o2 { l1.clone() } else { l2.clone() };
        }
        Level::mk_max_core(l1, l2)
    }

    /// Smart constructor for imax with simplifications (matches C++ mk_imax).
    pub fn mk_imax(l1: &Level, l2: &Level) -> Self {
        if l2.is_not_zero() {
            return Level::mk_max(l1, l2);
        }
        if l2.is_zero() {
            return l2.clone(); // imax u 0 = 0
        }
        if l1.is_zero() || l1.is_one() {
            return l2.clone(); // imax 0 u = imax 1 u = u
        }
        if l1 == l2 {
            return l1.clone(); // imax u u = u
        }
        Level::mk_imax_core(l1, l2)
    }

    pub fn mk_param(n: &Name) -> Self {
        Level::new(
            LevelKindData::Param(n.clone()),
            LevelData {
                hash: level_hash(mix_hash(2239, n.hash())),
                depth: 0,
                has_mvar: false,
                has_param: true,
            },
        )
    }

    pub fn mk_mvar(n: &Name) -> Self {
        Level::new(
            LevelKindData::MVar(n.clone()),
            LevelData {
                hash: level_hash(mix_hash(2237, n.hash())),
                depth: 0,
                has_mvar: true,
                has_param: false,
            },
        )
    }

    pub fn one() -> Self {
        Level::mk_succ(&Level::zero())
    }

    /// Build succ^k(l)
    pub fn mk_succ_n(l: &Level, k: u32) -> Self {
        let mut r = l.clone();
        for _ in 0..k {
            r = Level::mk_succ(&r);
        }
        r
    }

    // -- Accessors ----------------------------------------------------------

    fn data(&self) -> &LevelData {
        &self.0.data
    }

    pub fn hash(&self) -> u64 {
        self.data().hash
    }

    pub fn depth(&self) -> u32 {
        self.data().depth
    }

    pub fn has_mvar(&self) -> bool {
        self.data().has_mvar
    }

    pub fn has_param(&self) -> bool {
        self.data().has_param
    }

    pub fn kind(&self) -> LevelKind {
        match &self.0.kind {
            LevelKindData::Zero => LevelKind::Zero,
            LevelKindData::Succ(_) => LevelKind::Succ,
            LevelKindData::Max(_, _) => LevelKind::Max,
            LevelKindData::IMax(_, _) => LevelKind::IMax,
            LevelKindData::Param(_) => LevelKind::Param,
            LevelKindData::MVar(_) => LevelKind::MVar,
        }
    }

    pub fn is_zero(&self) -> bool { matches!(&self.0.kind, LevelKindData::Zero) }
    pub fn is_succ(&self) -> bool { matches!(&self.0.kind, LevelKindData::Succ(_)) }
    pub fn is_max(&self)  -> bool { matches!(&self.0.kind, LevelKindData::Max(_, _)) }
    pub fn is_imax(&self) -> bool { matches!(&self.0.kind, LevelKindData::IMax(_, _)) }
    pub fn is_param(&self) -> bool { matches!(&self.0.kind, LevelKindData::Param(_)) }
    pub fn is_mvar(&self) -> bool { matches!(&self.0.kind, LevelKindData::MVar(_)) }

    pub fn succ_of(&self) -> &Level {
        match &self.0.kind {
            LevelKindData::Succ(l) => l,
            _ => panic!("succ_of on non-succ level"),
        }
    }

    pub fn max_lhs(&self) -> &Level {
        match &self.0.kind {
            LevelKindData::Max(l, _) | LevelKindData::IMax(l, _) => l,
            _ => panic!("max_lhs on non-max/imax level"),
        }
    }

    pub fn max_rhs(&self) -> &Level {
        match &self.0.kind {
            LevelKindData::Max(_, r) | LevelKindData::IMax(_, r) => r,
            _ => panic!("max_rhs on non-max/imax level"),
        }
    }

    pub fn param_name(&self) -> &Name {
        match &self.0.kind {
            LevelKindData::Param(n) | LevelKindData::MVar(n) => n,
            _ => panic!("param_name on non-param/mvar level"),
        }
    }

    // -- Predicates ---------------------------------------------------------

    /// True if level is succ^k(zero) for some k.
    pub fn is_explicit(&self) -> bool {
        match &self.0.kind {
            LevelKindData::Zero => true,
            LevelKindData::Succ(l) => l.is_explicit(),
            _ => false,
        }
    }

    pub fn to_explicit(&self) -> u32 {
        self.to_offset().1
    }

    pub fn ptr_eq(&self, other: &Level) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    pub fn is_one(&self) -> bool {
        matches!(&self.0.kind, LevelKindData::Succ(l) if l.is_zero())
    }

    /// True if for all assignments, l != 0.
    pub fn is_not_zero(&self) -> bool {
        match &self.0.kind {
            LevelKindData::Zero | LevelKindData::Param(_) | LevelKindData::MVar(_) => false,
            LevelKindData::Succ(_) => true,
            LevelKindData::Max(l, r) => l.is_not_zero() || r.is_not_zero(),
            LevelKindData::IMax(_, r) => r.is_not_zero(),
        }
    }

    /// Convert succ^k(base) into (base, k).
    pub fn to_offset(&self) -> (Level, u32) {
        let mut l = self.clone();
        let mut k = 0u32;
        while l.is_succ() {
            l = l.succ_of().clone();
            k += 1;
        }
        (l, k)
    }

    // -- Traversal ----------------------------------------------------------

    pub fn for_each<F: FnMut(&Level) -> bool>(&self, f: &mut F) {
        if !f(self) {
            return;
        }
        match &self.0.kind {
            LevelKindData::Succ(l) => l.for_each(f),
            LevelKindData::Max(a, b) | LevelKindData::IMax(a, b) => {
                a.for_each(f);
                b.for_each(f);
            }
            _ => {}
        }
    }

    pub fn replace<F: FnMut(&Level) -> Option<Level>>(&self, f: &mut F) -> Level {
        if let Some(r) = f(self) {
            return r;
        }
        match &self.0.kind {
            LevelKindData::Succ(l) => {
                let new_l = l.replace(f);
                if Arc::ptr_eq(&l.0, &new_l.0) { self.clone() } else { Level::mk_succ(&new_l) }
            }
            LevelKindData::Max(a, b) => {
                let na = a.replace(f);
                let nb = b.replace(f);
                if Arc::ptr_eq(&a.0, &na.0) && Arc::ptr_eq(&b.0, &nb.0) {
                    self.clone()
                } else {
                    Level::mk_max(&na, &nb)
                }
            }
            LevelKindData::IMax(a, b) => {
                let na = a.replace(f);
                let nb = b.replace(f);
                if Arc::ptr_eq(&a.0, &na.0) && Arc::ptr_eq(&b.0, &nb.0) {
                    self.clone()
                } else {
                    Level::mk_imax(&na, &nb)
                }
            }
            _ => self.clone(),
        }
    }

    pub fn occurs(&self, target: &Level) -> bool {
        let mut found = false;
        self.for_each(&mut |l| {
            if found { return false; }
            if l == target { found = true; return false; }
            true
        });
        found
    }

    // -- Instantiation ------------------------------------------------------

    /// Substitute universe params: replace Param(ps[i]) with ls[i].
    pub fn instantiate(&self, ps: &[Name], ls: &[Level]) -> Level {
        debug_assert_eq!(ps.len(), ls.len());
        self.replace(&mut |l| {
            if !l.has_param() {
                return Some(l.clone());
            }
            if l.is_param() {
                let id = l.param_name();
                for (p, lv) in ps.iter().zip(ls.iter()) {
                    if p == id {
                        return Some(lv.clone());
                    }
                }
                return Some(l.clone());
            }
            None
        })
    }

    // -- Normalization (matches C++ normalize) ------------------------------

    fn push_max_args(l: &Level, out: &mut Vec<Level>) {
        if l.is_max() {
            Level::push_max_args(l.max_lhs(), out);
            Level::push_max_args(l.max_rhs(), out);
        } else {
            out.push(l.clone());
        }
    }

    fn mk_max_from_buf(args: &[Level]) -> Level {
        assert!(!args.is_empty());
        if args.len() == 1 {
            return args[0].clone();
        }
        let mut r = Level::mk_max(&args[args.len() - 2], &args[args.len() - 1]);
        let mut i = args.len().wrapping_sub(2);
        while i > 0 {
            i -= 1;
            r = Level::mk_max(&args[i], &r);
        }
        r
    }

    /// Normalize: flatten Max, sort, remove dominated terms.
    pub fn normalize(&self) -> Level {
        let (base, offset) = self.to_offset();
        match &base.0.kind {
            LevelKindData::Zero | LevelKindData::Param(_) | LevelKindData::MVar(_) => {
                self.clone()
            }
            LevelKindData::Succ(_) => unreachable!(),
            LevelKindData::IMax(a, b) => {
                let na = a.normalize();
                let nb = b.normalize();
                Level::mk_succ_n(&Level::mk_imax(&na, &nb), offset)
            }
            LevelKindData::Max(_, _) => {
                let mut todo = Vec::new();
                Level::push_max_args(&base, &mut todo);
                let mut args = Vec::new();
                for a in &todo {
                    let na = a.normalize();
                    Level::push_max_args(&na, &mut args);
                }
                args.sort_by(Level::is_norm_lt);
                let mut rargs: Vec<Level> = Vec::new();
                let mut i = 0;
                // Skip dominated explicit levels
                if args[i].is_explicit() {
                    while i + 1 < args.len() && args[i + 1].is_explicit() {
                        i += 1;
                    }
                    let k = args[i].to_offset().1;
                    // Check if explicit is subsumed by succ^k'(l) where k' >= k
                    let mut j = i + 1;
                    while j < args.len() {
                        if args[j].to_offset().1 >= k {
                            break;
                        }
                        j += 1;
                    }
                    if j < args.len() {
                        i += 1; // skip the explicit, it's subsumed
                    }
                }
                rargs.push(args[i].clone());
                let mut prev = args[i].to_offset();
                i += 1;
                while i < args.len() {
                    let curr = args[i].to_offset();
                    if prev.0 == curr.0 {
                        if prev.1 < curr.1 {
                            prev = curr.clone();
                            rargs.pop();
                            rargs.push(args[i].clone());
                        }
                    } else {
                        prev = curr;
                        rargs.push(args[i].clone());
                    }
                    i += 1;
                }
                for a in rargs.iter_mut() {
                    *a = Level::mk_succ_n(a, offset);
                }
                Level::mk_max_from_buf(&rargs)
            }
        }
    }

    /// Normalization total order (matches C++ is_norm_lt).
    fn is_norm_lt(a: &Level, b: &Level) -> std::cmp::Ordering {
        if Arc::ptr_eq(&a.0, &b.0) {
            return std::cmp::Ordering::Equal;
        }
        let (b1, o1) = a.to_offset();
        let (b2, o2) = b.to_offset();
        if b1 != b2 {
            if b1.kind() != b2.kind() {
                return b1.kind().cmp(&b2.kind());
            }
            match (&b1.0.kind, &b2.0.kind) {
                (LevelKindData::Param(n1), LevelKindData::Param(n2))
                | (LevelKindData::MVar(n1), LevelKindData::MVar(n2)) => {
                    return n1.cmp(n2);
                }
                (LevelKindData::Max(la, ra), LevelKindData::Max(lb, rb))
                | (LevelKindData::IMax(la, ra), LevelKindData::IMax(lb, rb)) => {
                    if la != lb {
                        return Level::is_norm_lt(la, lb);
                    }
                    return Level::is_norm_lt(ra, rb);
                }
                _ => unreachable!(),
            }
        }
        o1.cmp(&o2)
    }

    // -- Equivalence & Comparison -------------------------------------------

    pub fn is_equivalent(&self, other: &Level) -> bool {
        self == other || self.normalize() == other.normalize()
    }

    /// Matches C++ is_geq_core (assumes normalized inputs).
    fn is_geq_core(l1: &Level, l2: &Level) -> bool {
        if l1 == l2 || l2.is_zero() {
            return true;
        }
        if l2.is_max() {
            return Level::is_geq(l1, l2.max_lhs()) && Level::is_geq(l1, l2.max_rhs());
        }
        if l1.is_max() {
            if Level::is_geq(l1.max_lhs(), l2) || Level::is_geq(l1.max_rhs(), l2) {
                return true;
            }
        }
        if l2.is_imax() {
            return Level::is_geq(l1, l2.max_lhs()) && Level::is_geq(l1, l2.max_rhs());
        }
        if l1.is_imax() {
            return Level::is_geq(l1.max_rhs(), l2);
        }
        let (b1, o1) = l1.to_offset();
        let (b2, o2) = l2.to_offset();
        if b1 == b2 || b2.is_zero() {
            return o1 >= o2;
        }
        if o1 == o2 && o1 > 0 {
            return Level::is_geq(&b1, &b2);
        }
        false
    }

    pub fn is_geq(l1: &Level, l2: &Level) -> bool {
        Level::is_geq_core(&l1.normalize(), &l2.normalize())
    }

    /// Total order (matches C++ is_lt).
    pub fn is_lt(a: &Level, b: &Level, use_hash: bool) -> bool {
        if Arc::ptr_eq(&a.0, &b.0) { return false; }
        let da = a.depth();
        let db = b.depth();
        if da != db { return da < db; }
        if a.kind() != b.kind() { return a.kind() < b.kind(); }
        if use_hash {
            if a.hash() != b.hash() { return a.hash() < b.hash(); }
        }
        if a == b { return false; }
        match (&a.0.kind, &b.0.kind) {
            (LevelKindData::Zero, LevelKindData::Zero) => unreachable!(),
            (LevelKindData::Param(n1), LevelKindData::Param(n2))
            | (LevelKindData::MVar(n1), LevelKindData::MVar(n2)) => n1 < n2,
            (LevelKindData::Max(la, ra), LevelKindData::Max(lb, rb))
            | (LevelKindData::IMax(la, ra), LevelKindData::IMax(lb, rb)) => {
                if la != lb { Level::is_lt(la, lb, use_hash) }
                else { Level::is_lt(ra, rb, use_hash) }
            }
            (LevelKindData::Succ(a), LevelKindData::Succ(b)) => Level::is_lt(a, b, use_hash),
            _ => unreachable!(),
        }
    }

    pub fn get_undef_param(&self, params: &[Name]) -> Option<Name> {
        let mut result = None;
        self.for_each(&mut |l| {
            if !l.has_param() || result.is_some() {
                return false;
            }
            if l.is_param() {
                let id = l.param_name();
                if !params.contains(id) {
                    result = Some(id.clone());
                }
            }
            true
        });
        result
    }
}

// -- Equality (structural, matches C++ operator==) ---------------------------

impl PartialEq for Level {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) { return true; }
        if self.kind() != other.kind() { return false; }
        if self.hash() != other.hash() { return false; }
        match (&self.0.kind, &other.0.kind) {
            (LevelKindData::Zero, LevelKindData::Zero) => true,
            (LevelKindData::Param(a), LevelKindData::Param(b))
            | (LevelKindData::MVar(a), LevelKindData::MVar(b)) => a == b,
            (LevelKindData::Succ(a), LevelKindData::Succ(b)) => {
                if self.depth() != other.depth() { return false; }
                a == b
            }
            (LevelKindData::Max(la, ra), LevelKindData::Max(lb, rb))
            | (LevelKindData::IMax(la, ra), LevelKindData::IMax(lb, rb)) => {
                if self.depth() != other.depth() { return false; }
                la == lb && ra == rb
            }
            _ => false,
        }
    }
}

impl Eq for Level {}

impl std::hash::Hash for Level {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash());
    }
}

// -- Display ----------------------------------------------------------------

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn print(f: &mut fmt::Formatter<'_>, l: &Level) -> fmt::Result {
            if l.is_explicit() {
                write!(f, "{}", l.depth())
            } else {
                match &l.0.kind {
                    LevelKindData::Zero => unreachable!(),
                    LevelKindData::Param(n) => write!(f, "{}", n),
                    LevelKindData::MVar(n) => write!(f, "?{}", n),
                    LevelKindData::Succ(inner) => {
                        write!(f, "succ ")?;
                        print_child(f, inner)
                    }
                    LevelKindData::Max(a, b) => {
                        write!(f, "max ")?;
                        print_child(f, a)?;
                        write!(f, " ")?;
                        print_child(f, b)
                    }
                    LevelKindData::IMax(a, b) => {
                        write!(f, "imax ")?;
                        print_child(f, a)?;
                        write!(f, " ")?;
                        print_child(f, b)
                    }
                }
            }
        }
        fn print_child(f: &mut fmt::Formatter<'_>, l: &Level) -> fmt::Result {
            if l.is_explicit() || l.is_param() || l.is_mvar() {
                print(f, l)
            } else {
                write!(f, "(")?;
                print(f, l)?;
                write!(f, ")")
            }
        }
        print(f, self)
    }
}

impl fmt::Debug for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Level({})", self)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero() {
        let z = Level::zero();
        assert!(z.is_zero());
        assert!(z.is_explicit());
        assert_eq!(z.depth(), 0);
        assert_eq!(z.hash(), 2221);
        assert_eq!(z.to_string(), "0");
    }

    #[test]
    fn test_one() {
        let o = Level::one();
        assert!(o.is_succ());
        assert!(o.is_explicit());
        assert_eq!(o.depth(), 1);
        assert_eq!(o.to_string(), "1");
    }

    #[test]
    fn test_succ() {
        let z = Level::zero();
        let s1 = Level::mk_succ(&z);
        let s2 = Level::mk_succ(&s1);
        assert_eq!(s2.to_string(), "2");
        assert!(s2.is_explicit());
        assert_eq!(s2.to_explicit(), 2);
    }

    #[test]
    fn test_param() {
        let u = Level::mk_param(&Name::str("u"));
        assert!(u.is_param());
        assert!(!u.is_explicit());
        assert!(u.has_param());
        assert!(!u.has_mvar());
        assert_eq!(u.to_string(), "u");
    }

    #[test]
    fn test_mvar() {
        let m = Level::mk_mvar(&Name::str("m"));
        assert!(m.is_mvar());
        assert!(m.has_mvar());
        assert_eq!(m.to_string(), "?m");
    }

    #[test]
    fn test_max_explicit() {
        let l1 = Level::mk_succ_n(&Level::zero(), 3);
        let l2 = Level::mk_succ_n(&Level::zero(), 5);
        let m = Level::mk_max(&l1, &l2);
        assert!(m.is_explicit());
        assert_eq!(m.to_explicit(), 5);
    }

    #[test]
    fn test_max_identity() {
        let u = Level::mk_param(&Name::str("u"));
        let m = Level::mk_max(&u, &u);
        // max u u = u
        assert_eq!(m, u);
    }

    #[test]
    fn test_max_zero() {
        let u = Level::mk_param(&Name::str("u"));
        let z = Level::zero();
        assert_eq!(Level::mk_max(&z, &u), u);
        assert_eq!(Level::mk_max(&u, &z), u);
    }

    #[test]
    fn test_imax_zero() {
        let u = Level::mk_param(&Name::str("u"));
        let z = Level::zero();
        // imax u 0 = 0
        assert_eq!(Level::mk_imax(&u, &z), z);
    }

    #[test]
    fn test_imax_not_zero() {
        let u = Level::mk_param(&Name::str("u"));
        let one = Level::one();
        // imax u 1 = max u 1 (since 1 is_not_zero)
        let im = Level::mk_imax(&u, &one);
        let m = Level::mk_max(&u, &one);
        assert_eq!(im, m);
    }

    #[test]
    fn test_to_offset() {
        let u = Level::mk_param(&Name::str("u"));
        let s = Level::mk_succ_n(&u, 3);
        let (base, offset) = s.to_offset();
        assert_eq!(base, u);
        assert_eq!(offset, 3);
    }

    #[test]
    fn test_equality() {
        let u1 = Level::mk_param(&Name::str("u"));
        let u2 = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        assert_eq!(u1, u2);
        assert_ne!(u1, v);
    }

    #[test]
    fn test_hash_consistency() {
        let a = Level::mk_max(&Level::mk_param(&Name::str("u")), &Level::one());
        let b = Level::mk_max(&Level::mk_param(&Name::str("u")), &Level::one());
        assert_eq!(a.hash(), b.hash());
    }

    #[test]
    fn test_normalize_max_commutative() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let m1 = Level::mk_max_core(&u, &v);
        let m2 = Level::mk_max_core(&v, &u);
        // After normalization, max u v == max v u
        assert!(m1.is_equivalent(&m2));
    }

    #[test]
    fn test_normalize_dominated() {
        let u = Level::mk_param(&Name::str("u"));
        let su = Level::mk_succ(&u);
        // max u (succ u) normalizes to succ u
        let m = Level::mk_max_core(&u, &su);
        let n = m.normalize();
        assert_eq!(n, su);
    }

    #[test]
    fn test_is_geq() {
        let z = Level::zero();
        let u = Level::mk_param(&Name::str("u"));
        let su = Level::mk_succ(&u);

        assert!(Level::is_geq(&u, &z));
        assert!(Level::is_geq(&su, &u));
        assert!(Level::is_geq(&su, &z));
    }

    #[test]
    fn test_instantiate() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let m = Level::mk_max_core(&u, &v);

        let two = Level::mk_succ_n(&Level::zero(), 2);
        let three = Level::mk_succ_n(&Level::zero(), 3);

        let result = m.instantiate(
            &[Name::str("u"), Name::str("v")],
            &[two, three.clone()],
        );
        // max 2 3 = 3
        assert!(result.is_explicit());
        assert_eq!(result.to_explicit(), 3);
    }

    #[test]
    fn test_occurs() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let m = Level::mk_max_core(&u, &v);
        assert!(m.occurs(&u));
        assert!(m.occurs(&v));
        let w = Level::mk_param(&Name::str("w"));
        assert!(!m.occurs(&w));
    }

    #[test]
    fn test_get_undef_param() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let m = Level::mk_max_core(&u, &v);
        // Only "u" is declared
        let undef = m.get_undef_param(&[Name::str("u")]);
        assert_eq!(undef, Some(Name::str("v")));
        // Both declared
        let undef2 = m.get_undef_param(&[Name::str("u"), Name::str("v")]);
        assert_eq!(undef2, None);
    }

    #[test]
    fn test_is_lt_total_order() {
        let z = Level::zero();
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let su = Level::mk_succ(&u);

        // Antisymmetric
        assert!(!Level::is_lt(&z, &z, true));
        assert!(!Level::is_lt(&u, &u, true));

        // Some ordering relationships
        // Zero has depth 0, param has depth 0 but kind Zero < Param
        assert!(Level::is_lt(&z, &u, true));
        assert!(!Level::is_lt(&u, &z, true));
    }

    #[test]
    fn test_display() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let m = Level::mk_max_core(&u, &v);
        assert_eq!(m.to_string(), "max u v");

        let im = Level::mk_imax_core(&u, &v);
        assert_eq!(im.to_string(), "imax u v");

        let su = Level::mk_succ(&u);
        assert_eq!(su.to_string(), "succ u");
    }

    #[test]
    fn test_for_each() {
        let u = Level::mk_param(&Name::str("u"));
        let v = Level::mk_param(&Name::str("v"));
        let m = Level::mk_max_core(&u, &v);
        let sm = Level::mk_succ(&m);

        let mut count = 0;
        sm.for_each(&mut |_| { count += 1; true });
        // succ(max(u, v)) -> succ, max, u, v = 4 nodes
        assert_eq!(count, 4);
    }
}
