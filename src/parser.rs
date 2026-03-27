//! Stage 33: Parser — produce Syntax trees from tokens.

use crate::lexer::{Lexer, SpannedToken, Token};
use crate::name::Name;
use crate::syntax::Syntax;

// ============================================================================
// Parser
// ============================================================================

pub struct Parser {
    tokens: Vec<SpannedToken>,
    pos: usize,
}

#[derive(Debug)]
pub struct ParseError {
    pub msg: String,
    pub pos: u32,
}

impl Parser {
    pub fn new(src: &str) -> Self {
        let tokens = Lexer::new(src).tokenize_all();
        Parser { tokens, pos: 0 }
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.pos.min(self.tokens.len() - 1)].token
    }

    fn peek_span(&self) -> u32 {
        self.tokens[self.pos.min(self.tokens.len() - 1)].span.start
    }

    fn advance(&mut self) -> &SpannedToken {
        let t = &self.tokens[self.pos.min(self.tokens.len() - 1)];
        if self.pos < self.tokens.len() { self.pos += 1; }
        t
    }

    fn at_eof(&self) -> bool { matches!(self.peek(), Token::Eof) }

    fn expect_keyword(&mut self, kw: &str) -> Result<(), ParseError> {
        if matches!(self.peek(), Token::Keyword(k) if k == kw) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError { msg: format!("expected '{}'", kw), pos: self.peek_span() })
        }
    }

    fn expect_symbol(&mut self, sym: &str) -> Result<(), ParseError> {
        if matches!(self.peek(), Token::Symbol(s) if s == sym) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError { msg: format!("expected '{}'", sym), pos: self.peek_span() })
        }
    }

    fn eat_keyword(&mut self, kw: &str) -> bool {
        if matches!(self.peek(), Token::Keyword(k) if k == kw) {
            self.advance(); true
        } else { false }
    }

    fn eat_symbol(&mut self, sym: &str) -> bool {
        if matches!(self.peek(), Token::Symbol(s) if s == sym) {
            self.advance(); true
        } else { false }
    }

    // ========================================================================
    // Module header
    // ========================================================================

    pub fn parse_header(&mut self) -> (bool, Vec<Name>) {
        // Skip `module` keyword if present (Lean 4.25+)
        if matches!(self.peek(), Token::Ident(n) if n.to_string() == "module") {
            self.advance();
        }
        let is_prelude = self.eat_keyword("prelude");
        let mut imports = Vec::new();
        loop {
            // Skip modifiers: public, private, protected
            while matches!(self.peek(), Token::Keyword(k) if k == "private" || k == "protected") {
                self.advance();
            }
            // Check for `public` as ident (not always a keyword)
            while matches!(self.peek(), Token::Ident(n) if n.to_string() == "public") {
                self.advance();
            }
            if !self.eat_keyword("import") { break; }
            if let Token::Ident(name) = self.peek().clone() {
                imports.push(name);
                self.advance();
            }
        }
        (is_prelude, imports)
    }

    // ========================================================================
    // Commands
    // ========================================================================

    pub fn parse_commands(&mut self) -> Vec<Syntax> {
        let mut cmds = Vec::new();
        while !self.at_eof() {
            match self.parse_command() {
                Ok(cmd) => cmds.push(cmd),
                Err(_) => { self.advance(); } // error recovery: skip token
            }
        }
        cmds
    }

    fn parse_command(&mut self) -> Result<Syntax, ParseError> {
        match self.peek() {
            Token::Keyword(k) => match k.as_str() {
                "def" | "abbrev" => self.parse_def(),
                "theorem" | "lemma" => self.parse_theorem(),
                "axiom" | "constant" => self.parse_axiom(),
                "inductive" => self.parse_inductive(),
                "structure" | "class" => self.parse_structure(),
                "instance" => self.parse_instance(),
                "namespace" => self.parse_namespace(),
                "section" => self.parse_section(),
                "end" => { self.advance(); Ok(Syntax::mk_node("Command.end", vec![])) }
                "open" => self.parse_open(),
                "variable" => self.parse_variable(),
                "universe" => self.parse_universe(),
                "#check" | "#eval" | "#print" | "#reduce" => self.parse_hash_cmd(),
                "set_option" => self.parse_set_option(),
                "attribute" => self.parse_attribute(),
                "mutual" => self.parse_mutual(),
                _ => { self.advance(); Ok(Syntax::Missing) }
            },
            Token::DocComment(_) => { self.advance(); self.parse_command() }
            _ => { self.advance(); Ok(Syntax::Missing) }
        }
    }

    fn parse_def(&mut self) -> Result<Syntax, ParseError> {
        let kw = self.advance().token.clone(); // def or abbrev
        let name = self.parse_ident()?;
        let binders = self.parse_binders();
        let ret_type = if self.eat_symbol(":") { Some(self.parse_term(0)?) } else { None };

        // Equation-style: def f : T | pat => body | pat => body
        // Or standard: def f : T := value
        let value = if self.eat_symbol(":=") {
            self.parse_term(0)?
        } else if matches!(self.peek(), Token::Symbol(s) if s == "|") || self.eat_keyword("where") {
            // Equation-style def → desugar to match on a fresh variable
            let mut arms = Vec::new();
            while self.eat_symbol("|") {
                let pat = self.parse_term(0)?;
                self.expect_symbol("=>")?;
                let body = self.parse_term(0)?;
                arms.push(Syntax::mk_node("matchArm", vec![pat, body]));
            }
            // Build: fun _x => match _x with | arms...
            let scrutinee = Syntax::mk_ident_str("_eqn_arg");
            let mut match_args = vec![scrutinee];
            match_args.extend(arms);
            let match_expr = Syntax::mk_node("Term.match", match_args);
            // Wrap in lambda
            let binder = Syntax::mk_ident_str("_eqn_arg");
            Syntax::mk_node("Term.fun", vec![binder, match_expr])
        } else {
            return Err(ParseError { msg: "expected ':=' or '|' in def".into(), pos: self.peek_span() });
        };

        // Parse `where` clause if present
        let mut where_defs = Vec::new();
        if self.eat_keyword("where") {
            while matches!(self.peek(), Token::Keyword(k) if k == "def" || k == "let") ||
                  matches!(self.peek(), Token::Ident(_)) {
                if self.eat_keyword("def") || self.eat_keyword("let") {
                    // Skip for now — eat until next def/end
                }
                let helper_name = if let Token::Ident(_) = self.peek() {
                    self.parse_ident()?
                } else { break; };
                let helper_binders = self.parse_binders();
                let helper_type = if self.eat_symbol(":") { Some(self.parse_term(0)?) } else { None };
                if self.eat_symbol(":=") {
                    let helper_val = self.parse_term(0)?;
                    let mut hargs = vec![helper_name];
                    hargs.extend(helper_binders);
                    if let Some(ht) = helper_type { hargs.push(ht); }
                    hargs.push(helper_val);
                    where_defs.push(Syntax::mk_node("where_def", hargs));
                } else if matches!(self.peek(), Token::Symbol(s) if s == "|") {
                    // Equation-style where helper
                    let mut arms = Vec::new();
                    while self.eat_symbol("|") {
                        let pat = self.parse_term(0)?;
                        self.expect_symbol("=>")?;
                        let body = self.parse_term(0)?;
                        arms.push(Syntax::mk_node("matchArm", vec![pat, body]));
                    }
                    let scrutinee = Syntax::mk_ident_str("_w");
                    let mut match_args = vec![scrutinee];
                    match_args.extend(arms);
                    let match_expr = Syntax::mk_node("Term.match", match_args);
                    let fun_expr = Syntax::mk_node("Term.fun", vec![Syntax::mk_ident_str("_w"), match_expr]);
                    let mut hargs = vec![helper_name];
                    hargs.extend(helper_binders);
                    if let Some(ht) = helper_type { hargs.push(ht); }
                    hargs.push(fun_expr);
                    where_defs.push(Syntax::mk_node("where_def", hargs));
                } else { break; }
            }
        }

        let mut args = vec![name];
        args.extend(binders);
        if let Some(rt) = ret_type { args.push(rt); }
        args.push(value);
        args.extend(where_defs); // where defs appended at end
        let kind = if matches!(kw, Token::Keyword(ref k) if k == "abbrev") {
            "Command.abbrev"
        } else { "Command.def" };
        Ok(Syntax::mk_node(kind, args))
    }

    fn parse_theorem(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // theorem/lemma
        let name = self.parse_ident()?;
        let binders = self.parse_binders();
        self.expect_symbol(":")?;
        let type_ = self.parse_term(0)?;
        self.expect_symbol(":=")?;
        let value = self.parse_term(0)?;
        let mut args = vec![name];
        args.extend(binders);
        args.push(type_);
        args.push(value);
        Ok(Syntax::mk_node("Command.theorem", args))
    }

    fn parse_axiom(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // axiom/constant
        let name = self.parse_ident()?;
        let binders = self.parse_binders();
        self.expect_symbol(":")?;
        let type_ = self.parse_term(0)?;
        let mut args = vec![name];
        args.extend(binders);
        args.push(type_);
        Ok(Syntax::mk_node("Command.axiom", args))
    }

    fn parse_inductive(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // inductive
        let name = self.parse_ident()?;
        let binders = self.parse_binders();
        let type_ = if self.eat_symbol(":") { Some(self.parse_term(0)?) } else { None };
        self.eat_keyword("where");
        let mut ctors = Vec::new();
        while self.eat_symbol("|") {
            let ctor_name = self.parse_ident()?;
            let ctor_binders = self.parse_binders();
            let ctor_type = if self.eat_symbol(":") { Some(self.parse_term(0)?) } else { None };
            let mut ctor_args = vec![ctor_name];
            ctor_args.extend(ctor_binders);
            if let Some(t) = ctor_type { ctor_args.push(t); }
            ctors.push(Syntax::mk_node("ctor", ctor_args));
        }
        let mut args = vec![name];
        args.extend(binders);
        if let Some(t) = type_ { args.push(t); }
        args.extend(ctors);
        Ok(Syntax::mk_node("Command.inductive", args))
    }

    fn parse_structure(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // structure/class
        let name = self.parse_ident()?;
        let binders = self.parse_binders();
        self.eat_keyword("extends"); // optional
        self.eat_keyword("where");
        // Simplified: parse field declarations
        let mut fields = Vec::new();
        while let Token::Ident(_) = self.peek() {
            let field_name = self.parse_ident()?;
            self.expect_symbol(":")?;
            let field_type = self.parse_term(0)?;
            fields.push(Syntax::mk_node("field", vec![field_name, field_type]));
        }
        let mut args = vec![name];
        args.extend(binders);
        args.extend(fields);
        Ok(Syntax::mk_node("Command.structure", args))
    }

    fn parse_instance(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // instance
        let name = if let Token::Ident(_) = self.peek() {
            if !matches!(self.peek(), Token::Symbol(s) if s == ":") {
                Some(self.parse_ident()?)
            } else { None }
        } else { None };
        self.expect_symbol(":")?;
        let type_ = self.parse_term(0)?;
        self.expect_symbol(":=")?;
        let value = self.parse_term(0)?;
        let mut args = Vec::new();
        if let Some(n) = name { args.push(n); }
        args.push(type_);
        args.push(value);
        Ok(Syntax::mk_node("Command.instance", args))
    }

    fn parse_namespace(&mut self) -> Result<Syntax, ParseError> {
        self.advance();
        let name = self.parse_ident()?;
        Ok(Syntax::mk_node("Command.namespace", vec![name]))
    }

    fn parse_section(&mut self) -> Result<Syntax, ParseError> {
        self.advance();
        let name = if let Token::Ident(_) = self.peek() { Some(self.parse_ident()?) } else { None };
        let mut args = Vec::new();
        if let Some(n) = name { args.push(n); }
        Ok(Syntax::mk_node("Command.section", args))
    }

    fn parse_open(&mut self) -> Result<Syntax, ParseError> {
        self.advance();
        let name = self.parse_ident()?;
        Ok(Syntax::mk_node("Command.open", vec![name]))
    }

    fn parse_variable(&mut self) -> Result<Syntax, ParseError> {
        self.advance();
        let binders = self.parse_binders();
        Ok(Syntax::mk_node("Command.variable", binders))
    }

    fn parse_universe(&mut self) -> Result<Syntax, ParseError> {
        self.advance();
        let mut names = Vec::new();
        while let Token::Ident(_) = self.peek() {
            names.push(self.parse_ident()?);
        }
        Ok(Syntax::mk_node("Command.universe", names))
    }

    fn parse_hash_cmd(&mut self) -> Result<Syntax, ParseError> {
        let kw = match self.advance().token.clone() {
            Token::Keyword(k) => k,
            _ => return Ok(Syntax::Missing),
        };
        let arg = self.parse_term(0)?;
        Ok(Syntax::mk_node(&kw, vec![arg]))
    }

    fn parse_set_option(&mut self) -> Result<Syntax, ParseError> {
        self.advance();
        let name = self.parse_ident()?;
        let val = self.parse_term(0)?;
        Ok(Syntax::mk_node("Command.set_option", vec![name, val]))
    }

    fn parse_attribute(&mut self) -> Result<Syntax, ParseError> {
        self.advance();
        // Simplified: skip until next command
        Ok(Syntax::mk_node("Command.attribute", vec![]))
    }

    fn parse_mutual(&mut self) -> Result<Syntax, ParseError> {
        self.advance();
        let mut defs = Vec::new();
        while !self.eat_keyword("end") && !self.at_eof() {
            match self.parse_command() {
                Ok(cmd) => defs.push(cmd),
                Err(_) => { self.advance(); }
            }
        }
        Ok(Syntax::mk_node("Command.mutual", defs))
    }

    // ========================================================================
    // Binders
    // ========================================================================

    fn parse_binders(&mut self) -> Vec<Syntax> {
        let mut binders = Vec::new();
        loop {
            match self.peek() {
                Token::Symbol(s) if s == "(" => {
                    self.advance();
                    let inner = self.parse_binder_inner("(", ")");
                    binders.push(Syntax::mk_node("Binder.explicit", inner));
                }
                Token::Symbol(s) if s == "{" => {
                    self.advance();
                    let inner = self.parse_binder_inner("{", "}");
                    binders.push(Syntax::mk_node("Binder.implicit", inner));
                }
                Token::Symbol(s) if s == "[" => {
                    self.advance();
                    let inner = self.parse_binder_inner("[", "]");
                    binders.push(Syntax::mk_node("Binder.inst", inner));
                }
                Token::Symbol(s) if s == "⦃" => {
                    self.advance();
                    let inner = self.parse_binder_inner("⦃", "⦄");
                    binders.push(Syntax::mk_node("Binder.strict", inner));
                }
                _ => break,
            }
        }
        binders
    }

    fn parse_binder_inner(&mut self, _open: &str, close: &str) -> Vec<Syntax> {
        let mut names = Vec::new();
        while let Token::Ident(_) = self.peek() {
            names.push(self.parse_ident().unwrap_or(Syntax::Missing));
            if matches!(self.peek(), Token::Symbol(s) if s == ":") { break; }
        }
        let type_ = if self.eat_symbol(":") {
            self.parse_term(0).unwrap_or(Syntax::Missing)
        } else {
            Syntax::Missing
        };
        self.eat_symbol(close);
        let mut args = names;
        args.push(type_);
        args
    }

    // ========================================================================
    // Term parser (Pratt)
    // ========================================================================

    pub fn parse_term(&mut self, min_bp: u32) -> Result<Syntax, ParseError> {
        let mut lhs = self.parse_leading_term()?;
        loop {
            let (bp, right_bp) = match self.peek_trailing_bp() {
                Some((bp, rbp)) if bp >= min_bp => (bp, rbp),
                _ => break,
            };
            lhs = self.parse_trailing_term(lhs, right_bp)?;
        }
        Ok(lhs)
    }

    fn parse_leading_term(&mut self) -> Result<Syntax, ParseError> {
        match self.peek().clone() {
            Token::NumLit(n) => {
                self.advance();
                Ok(Syntax::mk_node("Term.num", vec![Syntax::mk_atom(&n.to_string())]))
            }
            Token::StrLit(s) => {
                self.advance();
                Ok(Syntax::mk_node("Term.str", vec![Syntax::mk_atom(&s)]))
            }
            Token::Ident(name) => {
                self.advance();
                Ok(Syntax::mk_node("Term.ident", vec![Syntax::mk_ident(name)]))
            }
            Token::Keyword(ref k) => match k.as_str() {
                "fun" | "λ" => self.parse_fun(),
                "forall" | "∀" => self.parse_forall(),
                "if" => self.parse_if(),
                "let" => self.parse_let(),
                "have" => self.parse_have(),
                "show" => self.parse_show(),
                "match" => self.parse_match(),
                "do" => self.parse_do(),
                "calc" => self.parse_calc(),
                "return" => {
                    self.advance();
                    let e = self.parse_term(0)?;
                    Ok(Syntax::mk_node("Term.return", vec![e]))
                }
                "by" => self.parse_by(),
                "Type" => { self.advance(); Ok(Syntax::mk_node("Term.type", vec![])) }
                "Prop" => { self.advance(); Ok(Syntax::mk_node("Term.prop", vec![])) }
                "Sort" => {
                    self.advance();
                    // Sort may or may not have a level argument
                    if self.peek_trailing_bp().is_some() || matches!(self.peek(), Token::Ident(_) | Token::NumLit(_)) {
                        let l = self.parse_term(1024)?;
                        Ok(Syntax::mk_node("Term.sort", vec![l]))
                    } else {
                        Ok(Syntax::mk_node("Term.sort", vec![]))
                    }
                }
                _ => {
                    let k = k.clone(); self.advance();
                    Ok(Syntax::mk_node("Term.ident", vec![Syntax::mk_ident_str(&k)]))
                }
            },
            Token::Symbol(ref s) => match s.as_str() {
                "(" => self.parse_paren(),
                "[" => self.parse_list_literal(),
                "{" => self.parse_subtype_or_set(),
                "⟨" => self.parse_anon_ctor(),
                "∀" => self.parse_forall(),
                "∃" => self.parse_exists(),
                "λ" => self.parse_fun(),
                "@" => {
                    self.advance();
                    let e = self.parse_term(1024)?;
                    Ok(Syntax::mk_node("Term.explicit", vec![e]))
                }
                "!" => { self.advance(); let e = self.parse_term(1024)?; Ok(Syntax::mk_node("Term.bnot", vec![e])) }
                "¬" => { self.advance(); let e = self.parse_term(40)?; Ok(Syntax::mk_node("Term.not", vec![e])) }
                "_" => { self.advance(); Ok(Syntax::mk_node("Term.hole", vec![])) }
                _ => Err(ParseError { msg: format!("unexpected symbol '{}'", s), pos: self.peek_span() }),
            },
            _ => Err(ParseError { msg: "unexpected token".into(), pos: self.peek_span() }),
        }
    }

    fn peek_trailing_bp(&self) -> Option<(u32, u32)> {
        match self.peek() {
            // Application: if next token can start a term and we're not at a command boundary
            Token::Ident(_) | Token::NumLit(_) | Token::StrLit(_) => Some((1024, 1024)),
            Token::Symbol(s) => match s.as_str() {
                "(" | "⟨" => Some((1024, 1024)),
                "." => Some((1024, 1025)),
                "^" => Some((75, 75)),    // right assoc
                "*" | "/" | "%" => Some((70, 71)),
                "×" => Some((35, 35)),  // product type
                "+" | "-" => Some((65, 66)),
                "++" => Some((65, 65)),
                "=" | "==" | "!=" | "≠" | "<" | ">" | "≤" | ">=" | "≥" | "<=" => Some((50, 51)),
                "∧" | "&&" => Some((35, 35)),
                "∨" | "||" => Some((30, 30)),
                "→" | "->" => Some((25, 25)),
                "↔" | "<->" => Some((20, 20)),
                "|>" | "|>." => Some((10, 11)),
                "<|" => Some((10, 10)),
                "::" => Some((67, 67)),
                _ => None,
            },
            Token::Keyword(k) => match k.as_str() {
                "fun" | "λ" | "if" | "let" | "have" | "show" | "match" | "by"
                    | "Type" | "Prop" | "Sort" => Some((1024, 1024)),
                _ => None,
            },
            _ => None,
        }
    }

    fn is_infix_op(&self, s: &str) -> bool {
        matches!(s, "+" | "-" | "*" | "/" | "%" | "^" | "++" | "::" | "×"
            | "=" | "==" | "!=" | "≠" | "<" | ">" | "≤" | ">=" | "≥" | "<="
            | "∧" | "&&" | "∨" | "||" | "→" | "->" | "↔" | "<->"
            | "|>" | "<|")
    }

    fn parse_trailing_term(&mut self, lhs: Syntax, right_bp: u32) -> Result<Syntax, ParseError> {
        match self.peek().clone() {
            Token::Symbol(ref s) if s == "." => {
                self.advance();
                let field = self.parse_ident()?;
                Ok(Syntax::mk_node("Term.proj", vec![lhs, field]))
            }
            Token::Symbol(ref s) if self.is_infix_op(s) => {
                let op = s.clone();
                self.advance();
                let rhs = self.parse_term(right_bp)?;
                Ok(Syntax::mk_node("Term.binop", vec![Syntax::mk_atom(&op), lhs, rhs]))
            }
            _ => {
                // Application: f (arg) or f x
                let arg = self.parse_leading_term()?;
                Ok(Syntax::mk_node("Term.app", vec![lhs, arg]))
            }
        }
    }

    // ========================================================================
    // Leading term parsers
    // ========================================================================

    fn parse_fun(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // fun
        let binders = self.parse_fun_binders();
        self.expect_symbol("=>")?;
        let body = self.parse_term(0)?;
        let mut args = binders;
        args.push(body);
        Ok(Syntax::mk_node("Term.fun", args))
    }

    fn parse_fun_binders(&mut self) -> Vec<Syntax> {
        let mut binders = Vec::new();
        loop {
            match self.peek() {
                Token::Symbol(s) if s == "=>" || s == "," => break,
                Token::Symbol(s) if s == "(" || s == "{" || s == "[" => {
                    binders.extend(self.parse_binders());
                }
                Token::Ident(_) => {
                    let id = self.parse_ident().unwrap_or(Syntax::Missing);
                    // Check for `: Type` annotation (unparenthesized typed binder)
                    if self.eat_symbol(":") {
                        let ty = self.parse_term(0).unwrap_or(Syntax::Missing);
                        binders.push(Syntax::mk_node("Binder.explicit", vec![id, ty]));
                    } else {
                        binders.push(id);
                    }
                }
                _ => break,
            }
        }
        binders
    }

    fn parse_forall(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // forall/∀
        let binders = self.parse_fun_binders();
        self.expect_symbol(",")?;
        let body = self.parse_term(0)?;
        let mut args = binders;
        args.push(body);
        Ok(Syntax::mk_node("Term.forall", args))
    }

    fn parse_subtype_or_set(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // {
        // { x : T // P x } or { x | P x } or { a, b, c }
        let first = self.parse_ident()?;
        if self.eat_symbol(":") {
            let ty = self.parse_term(0)?;
            if self.eat_symbol("//") {
                let pred = self.parse_term(0)?;
                self.expect_symbol("}")?;
                Ok(Syntax::mk_node("Term.subtype", vec![first, ty, pred]))
            } else {
                self.expect_symbol("}")?;
                Ok(Syntax::mk_node("Term.set", vec![first, ty]))
            }
        } else if self.eat_symbol("//") {
            let pred = self.parse_term(0)?;
            self.expect_symbol("}")?;
            Ok(Syntax::mk_node("Term.subtype", vec![first, Syntax::Missing, pred]))
        } else {
            self.expect_symbol("}")?;
            Ok(Syntax::mk_node("Term.set", vec![first]))
        }
    }

    fn parse_list_literal(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // [
        let mut elems = Vec::new();
        if !matches!(self.peek(), Token::Symbol(s) if s == "]") {
            elems.push(self.parse_term(0)?);
            while self.eat_symbol(",") {
                elems.push(self.parse_term(0)?);
            }
        }
        self.expect_symbol("]")?;
        Ok(Syntax::mk_node("Term.list", elems))
    }

    fn parse_exists(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // ∃
        let binders = self.parse_fun_binders();
        self.expect_symbol(",")?;
        let body = self.parse_term(0)?;
        let mut args = binders;
        args.push(body);
        Ok(Syntax::mk_node("Term.exists", args))
    }

    fn parse_if(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // if
        let cond = self.parse_term(0)?;
        self.expect_keyword("then")?;
        let then_ = self.parse_term(0)?;
        self.expect_keyword("else")?;
        let else_ = self.parse_term(0)?;
        Ok(Syntax::mk_node("Term.if", vec![cond, then_, else_]))
    }

    fn parse_let(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // let
        let name = self.parse_ident()?;
        let type_ = if self.eat_symbol(":") { Some(self.parse_term(0)?) } else { None };
        self.expect_symbol(":=")?;
        let value = self.parse_term(0)?;
        // Eat optional semicolon or newline
        self.eat_symbol(";");
        let body = self.parse_term(0)?;
        let mut args = vec![name];
        if let Some(t) = type_ { args.push(t); }
        args.push(value);
        args.push(body);
        Ok(Syntax::mk_node("Term.let", args))
    }

    fn parse_have(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // have
        let name = self.parse_ident()?;
        self.expect_symbol(":")?;
        let type_ = self.parse_term(0)?;
        self.expect_symbol(":=")?;
        let proof = self.parse_term(0)?;
        self.eat_symbol(";");
        let body = self.parse_term(0)?;
        Ok(Syntax::mk_node("Term.have", vec![name, type_, proof, body]))
    }

    fn parse_show(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // show
        let type_ = self.parse_term(0)?;
        self.expect_keyword("from")?;
        let value = self.parse_term(0)?;
        Ok(Syntax::mk_node("Term.show", vec![type_, value]))
    }

    fn parse_match(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // match
        let scrutinee = self.parse_term(0)?;
        self.expect_keyword("with")?;
        let mut arms = Vec::new();
        while self.eat_symbol("|") {
            let pat = self.parse_term(0)?;
            self.expect_symbol("=>")?;
            let body = self.parse_term(0)?;
            arms.push(Syntax::mk_node("matchArm", vec![pat, body]));
        }
        let mut args = vec![scrutinee];
        args.extend(arms);
        Ok(Syntax::mk_node("Term.match", args))
    }

    fn parse_do(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // do
        // Simplified: collect statements until dedent/next command
        let mut stmts = Vec::new();
        while !self.at_eof() {
            match self.peek() {
                Token::Keyword(k) if ["def", "theorem", "lemma", "axiom", "inductive",
                    "structure", "class", "instance", "namespace", "section", "end",
                    "#check", "#eval"].contains(&k.as_str()) => break,
                _ => {
                    match self.parse_term(0) {
                        Ok(stmt) => stmts.push(stmt),
                        Err(_) => { self.advance(); break; }
                    }
                    self.eat_symbol(";");
                }
            }
        }
        Ok(Syntax::mk_node("Term.do", stmts))
    }

    fn parse_calc(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // calc
        // Parse: expr₁ op expr₂ := proof₁; expr₃ op expr₄ := proof₂; ...
        let mut steps = Vec::new();
        let first = self.parse_term(0)?;
        steps.push(first);
        while self.eat_symbol(":=") || self.eat_symbol("_") {
            let proof = self.parse_term(0)?;
            steps.push(proof);
            // Try to parse next step
            if matches!(self.peek(), Token::Symbol(s) if s == "_") ||
               matches!(self.peek(), Token::Ident(_)) {
                let next = self.parse_term(0)?;
                steps.push(next);
            } else {
                break;
            }
        }
        Ok(Syntax::mk_node("Term.calc", steps))
    }

    fn parse_by(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // by
        // Simplified: collect tokens until dedent or next command
        let mut tactics = Vec::new();
        while !self.at_eof() {
            match self.peek() {
                Token::Keyword(k) if ["def", "theorem", "lemma", "axiom", "inductive",
                    "structure", "class", "instance", "namespace", "section", "end",
                    "#check", "#eval"].contains(&k.as_str()) => break,
                _ => {
                    let t = self.advance();
                    tactics.push(Syntax::mk_atom(&format!("{:?}", t.token)));
                }
            }
        }
        Ok(Syntax::mk_node("Term.by", tactics))
    }

    fn parse_paren(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // (
        if self.eat_symbol(")") {
            return Ok(Syntax::mk_node("Term.unit", vec![]));
        }
        let inner = self.parse_term(0)?;
        // Check for tuple
        if self.eat_symbol(",") {
            let mut elems = vec![inner];
            elems.push(self.parse_term(0)?);
            while self.eat_symbol(",") {
                elems.push(self.parse_term(0)?);
            }
            self.expect_symbol(")")?;
            return Ok(Syntax::mk_node("Term.tuple", elems));
        }
        // Check for type ascription
        if self.eat_symbol(":") {
            let type_ = self.parse_term(0)?;
            self.expect_symbol(")")?;
            return Ok(Syntax::mk_node("Term.typeAscription", vec![inner, type_]));
        }
        self.expect_symbol(")")?;
        Ok(Syntax::mk_node("Term.paren", vec![inner]))
    }

    fn parse_anon_ctor(&mut self) -> Result<Syntax, ParseError> {
        self.advance(); // ⟨
        let mut args = Vec::new();
        if !matches!(self.peek(), Token::Symbol(s) if s == "⟩") {
            args.push(self.parse_term(0)?);
            while self.eat_symbol(",") {
                args.push(self.parse_term(0)?);
            }
        }
        self.expect_symbol("⟩")?;
        Ok(Syntax::mk_node("Term.anonymousCtor", args))
    }

    fn parse_ident(&mut self) -> Result<Syntax, ParseError> {
        match self.peek().clone() {
            Token::Ident(name) => { self.advance(); Ok(Syntax::mk_ident(name)) }
            _ => Err(ParseError { msg: "expected identifier".into(), pos: self.peek_span() }),
        }
    }
}

// ============================================================================
// Convenience: parse a file
// ============================================================================

pub fn parse_file(src: &str) -> (bool, Vec<Name>, Vec<Syntax>) {
    let mut parser = Parser::new(src);
    let (is_prelude, imports) = parser.parse_header();
    let commands = parser.parse_commands();
    (is_prelude, imports, commands)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_def_simple() {
        let (_, _, cmds) = parse_file("def x := 0");
        assert_eq!(cmds.len(), 1);
        assert!(cmds[0].is_node("Command.def"));
    }

    #[test]
    fn test_parse_def_typed() {
        let (_, _, cmds) = parse_file("def f (n : Nat) : Nat := n + 1");
        assert_eq!(cmds.len(), 1);
        assert!(cmds[0].is_node("Command.def"));
        assert!(cmds[0].num_args() >= 3); // name, binder, type, value
    }

    #[test]
    fn test_parse_theorem() {
        let (_, _, cmds) = parse_file("theorem foo : True := True.intro");
        assert_eq!(cmds.len(), 1);
        assert!(cmds[0].is_node("Command.theorem"));
    }

    #[test]
    fn test_parse_import() {
        let (is_p, imports, _) = parse_file("import Init\nimport Init.Data.Nat");
        assert!(!is_p);
        assert_eq!(imports.len(), 2);
        assert_eq!(imports[0], Name::str("Init"));
        assert_eq!(imports[1], Name::str("Init.Data.Nat"));
    }

    #[test]
    fn test_parse_prelude() {
        let (is_p, imports, _) = parse_file("prelude");
        assert!(is_p);
        assert_eq!(imports.len(), 0);
    }

    #[test]
    fn test_parse_lambda() {
        let mut p = Parser::new("fun x => x");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.fun"));
    }

    #[test]
    fn test_parse_app() {
        let mut p = Parser::new("f x");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.app"));
    }

    #[test]
    fn test_parse_binop() {
        let mut p = Parser::new("a + b");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.binop"));
    }

    #[test]
    fn test_parse_arrow() {
        let mut p = Parser::new("Nat → Nat");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.binop"));
        assert_eq!(t.arg(0).as_atom().unwrap(), "→");
    }

    #[test]
    fn test_parse_if() {
        let mut p = Parser::new("if True then 1 else 0");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.if"));
        assert_eq!(t.num_args(), 3);
    }

    #[test]
    fn test_parse_paren() {
        let mut p = Parser::new("(x)");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.paren"));
    }

    #[test]
    fn test_parse_tuple() {
        let mut p = Parser::new("(1, 2)");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.tuple"));
        assert_eq!(t.num_args(), 2);
    }

    #[test]
    fn test_parse_type_ascription() {
        let mut p = Parser::new("(0 : Nat)");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.typeAscription"));
    }

    #[test]
    fn test_parse_inductive() {
        let (_, _, cmds) = parse_file("inductive MyBool where\n  | tt\n  | ff");
        assert_eq!(cmds.len(), 1);
        assert!(cmds[0].is_node("Command.inductive"));
    }

    #[test]
    fn test_parse_namespace() {
        let (_, _, cmds) = parse_file("namespace Foo\ndef x := 0\nend");
        assert!(cmds.len() >= 2);
    }

    #[test]
    fn test_parse_hash_check() {
        let (_, _, cmds) = parse_file("#check Nat");
        assert_eq!(cmds.len(), 1);
        assert!(cmds[0].is_node("#check"));
    }

    #[test]
    fn test_parse_forall() {
        let mut p = Parser::new("∀ x, P x");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.forall"));
    }

    #[test]
    fn test_parse_anon_ctor() {
        let mut p = Parser::new("⟨a, b⟩");
        let t = p.parse_term(0).unwrap();
        assert!(t.is_node("Term.anonymousCtor"));
        assert_eq!(t.num_args(), 2);
    }
}
