//! Stage 34: Name resolution — resolve identifiers to kernel constants.

use crate::env::Environment;
use crate::name::Name;

/// Resolution context — tracks namespaces, open scopes, locals.
pub struct ResCtx {
    pub current_ns: Name,
    pub ns_stack: Vec<Name>,     // namespace stack for push/pop
    pub open_scopes: Vec<Name>,
    pub locals: Vec<Name>,       // local variable names in scope
    pub universes: Vec<Name>,    // universe params in scope
}

impl ResCtx {
    pub fn new() -> Self {
        ResCtx {
            current_ns: Name::anonymous(),
            ns_stack: Vec::new(),
            open_scopes: Vec::new(),
            locals: Vec::new(),
            universes: Vec::new(),
        }
    }

    pub fn push_local(&mut self, name: Name) { self.locals.push(name); }
    pub fn pop_local(&mut self) { self.locals.pop(); }
    pub fn push_ns(&mut self, ns: Name) {
        self.ns_stack.push(self.current_ns.clone());
        self.current_ns = self.current_ns.append(&ns);
    }
    pub fn pop_ns(&mut self) {
        if let Some(prev) = self.ns_stack.pop() {
            self.current_ns = prev;
        }
    }

    pub fn open_scope(&mut self, ns: Name) { self.open_scopes.push(ns); }
}

/// Resolve an identifier to a fully qualified name.
pub fn resolve_name(name: &Name, ctx: &ResCtx, env: &Environment) -> Result<Name, ResError> {
    let s = name.to_string();

    // 1. _root_ prefix — force root lookup
    if s.starts_with("_root_.") {
        let rest = Name::str(&s[7..]);
        if env.find(&rest).is_some() {
            return Ok(rest);
        }
        return Err(ResError::NotFound(name.clone()));
    }

    // 2. Local variables
    for local in ctx.locals.iter().rev() {
        if local == name { return Ok(name.clone()); }
    }

    // 3. Current namespace + parents
    let mut ns = ctx.current_ns.clone();
    loop {
        let qualified = if ns.is_anonymous() { name.clone() } else { ns.append(name) };
        if env.find(&qualified).is_some() {
            return Ok(qualified);
        }
        if ns.is_anonymous() { break; }
        ns = ns.get_prefix().clone();
    }

    // 4. Open scopes
    for scope in &ctx.open_scopes {
        let qualified = scope.append(name);
        if env.find(&qualified).is_some() {
            return Ok(qualified);
        }
    }

    // 5. Root (already tried in step 3 when ns became anonymous)

    Err(ResError::NotFound(name.clone()))
}

/// Resolve a universe name.
pub fn resolve_universe(name: &Name, ctx: &ResCtx) -> Name {
    // If declared, use as-is. Otherwise auto-bind.
    // Either way, it becomes a Level.param.
    name.clone()
}

#[derive(Debug)]
pub enum ResError {
    NotFound(Name),
    Ambiguous(Name, Vec<Name>),
}

impl std::fmt::Display for ResError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResError::NotFound(n) => write!(f, "unknown identifier '{}'", n),
            ResError::Ambiguous(n, opts) => {
                write!(f, "ambiguous identifier '{}', could be: ", n)?;
                for (i, o) in opts.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", o)?;
                }
                Ok(())
            }
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::*;
    use crate::expr::Expr;
    use crate::level::Level;
    use std::sync::Arc;
    use std::collections::HashMap;

    fn mk_env(names: &[&str]) -> Environment {
        let mut constants = HashMap::new();
        for &n in names {
            let name = Name::str(n);
            constants.insert(name.clone(), Arc::new(ConstantInfo {
                name: name.clone(),
                lparams: vec![],
                type_: Expr::mk_type(),
                kind: ConstantInfoKind::Axiom { is_unsafe: false },
            }));
        }
        Environment::from_constants(constants, 0)
    }

    #[test]
    fn test_resolve_root() {
        let env = mk_env(&["Nat", "Nat.succ", "Nat.zero"]);
        let ctx = ResCtx::new();
        assert_eq!(resolve_name(&Name::str("Nat"), &ctx, &env).unwrap(), Name::str("Nat"));
        assert_eq!(resolve_name(&Name::str("Nat.succ"), &ctx, &env).unwrap(), Name::str("Nat.succ"));
    }

    #[test]
    fn test_resolve_in_namespace() {
        let env = mk_env(&["Nat", "Nat.succ", "Nat.zero"]);
        let mut ctx = ResCtx::new();
        ctx.push_ns(Name::str("Nat"));
        // "succ" should resolve to "Nat.succ"
        assert_eq!(resolve_name(&Name::str("succ"), &ctx, &env).unwrap(), Name::str("Nat.succ"));
    }

    #[test]
    fn test_resolve_open_scope() {
        let env = mk_env(&["Nat", "Nat.succ", "List", "List.nil"]);
        let mut ctx = ResCtx::new();
        ctx.open_scope(Name::str("List"));
        assert_eq!(resolve_name(&Name::str("nil"), &ctx, &env).unwrap(), Name::str("List.nil"));
    }

    #[test]
    fn test_resolve_root_prefix() {
        let env = mk_env(&["Nat", "Nat.succ", "Foo.Nat"]);
        let mut ctx = ResCtx::new();
        ctx.push_ns(Name::str("Foo"));
        // "Nat" in namespace Foo resolves to Foo.Nat
        assert_eq!(resolve_name(&Name::str("Nat"), &ctx, &env).unwrap(), Name::str("Foo.Nat"));
        // "_root_.Nat" forces root
        assert_eq!(resolve_name(&Name::str("_root_.Nat"), &ctx, &env).unwrap(), Name::str("Nat"));
    }

    #[test]
    fn test_resolve_local() {
        let env = mk_env(&["Nat"]);
        let mut ctx = ResCtx::new();
        ctx.push_local(Name::str("x"));
        assert_eq!(resolve_name(&Name::str("x"), &ctx, &env).unwrap(), Name::str("x"));
    }

    #[test]
    fn test_resolve_not_found() {
        let env = mk_env(&["Nat"]);
        let ctx = ResCtx::new();
        assert!(resolve_name(&Name::str("nonexistent"), &ctx, &env).is_err());
    }

    #[test]
    fn test_resolve_parent_namespace() {
        let env = mk_env(&["Foo.bar", "Foo.Baz.qux"]);
        let mut ctx = ResCtx::new();
        ctx.push_ns(Name::str("Foo.Baz"));
        // "bar" should find "Foo.bar" by walking up to parent namespace "Foo"
        assert_eq!(resolve_name(&Name::str("bar"), &ctx, &env).unwrap(), Name::str("Foo.bar"));
    }
}
