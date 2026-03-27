//! Stage 32: Syntax tree — the output of parsing.

use crate::name::Name;

/// Source position info attached to syntax nodes.
#[derive(Clone, Debug)]
pub enum SourceInfo {
    Original { pos: u32, end_pos: u32 },
    Synthetic { pos: u32, end_pos: u32 },
    None,
}

/// A syntax tree node.
#[derive(Clone, Debug)]
pub enum Syntax {
    Missing,
    Node { info: SourceInfo, kind: Name, args: Vec<Syntax> },
    Atom { info: SourceInfo, val: String },
    Ident { info: SourceInfo, val: Name },
}

impl Syntax {
    pub fn mk_node(kind: &str, args: Vec<Syntax>) -> Self {
        Syntax::Node { info: SourceInfo::None, kind: Name::str(kind), args }
    }

    pub fn mk_atom(val: &str) -> Self {
        Syntax::Atom { info: SourceInfo::None, val: val.to_string() }
    }

    pub fn mk_ident(name: Name) -> Self {
        Syntax::Ident { info: SourceInfo::None, val: name }
    }

    pub fn mk_ident_str(s: &str) -> Self {
        Syntax::Ident { info: SourceInfo::None, val: Name::str(s) }
    }

    pub fn kind_name(&self) -> Option<&Name> {
        match self { Syntax::Node { kind, .. } => Some(kind), _ => None }
    }

    pub fn is_node(&self, kind: &str) -> bool {
        matches!(self, Syntax::Node { kind: k, .. } if *k == Name::str(kind))
    }

    pub fn args(&self) -> &[Syntax] {
        match self { Syntax::Node { args, .. } => args, _ => &[] }
    }

    pub fn arg(&self, i: usize) -> &Syntax {
        &self.args()[i]
    }

    pub fn num_args(&self) -> usize {
        self.args().len()
    }

    pub fn as_ident(&self) -> Option<&Name> {
        match self { Syntax::Ident { val, .. } => Some(val), _ => None }
    }

    pub fn as_atom(&self) -> Option<&str> {
        match self { Syntax::Atom { val, .. } => Some(val), _ => None }
    }

    pub fn is_missing(&self) -> bool {
        matches!(self, Syntax::Missing)
    }
}
