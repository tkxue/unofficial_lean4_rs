//! Stage 31: Lexer — tokenize .lean source files.

use crate::name::Name;

// ============================================================================
// Token
// ============================================================================

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Ident(Name),
    NumLit(u64),
    StrLit(String),
    CharLit(char),
    Keyword(String),
    Symbol(String),
    DocComment(String),
    Eof,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub col: u32,
}

#[derive(Clone, Debug)]
pub struct SpannedToken {
    pub token: Token,
    pub span: Span,
}

// ============================================================================
// Unicode classification (matches C++ name.cpp exactly)
// ============================================================================

fn is_letter_like_unicode(u: u32) -> bool {
    (0x3b1 <= u && u <= 0x3c9 && u != 0x3bb) ||      // lower greek, not lambda
    (0x391 <= u && u <= 0x3A9 && u != 0x3A0 && u != 0x3A3) || // upper greek, not Pi/Sigma
    (0x3ca <= u && u <= 0x3fb) ||                      // Coptic
    (0x1f00 <= u && u <= 0x1ffe) ||                    // Polytonic Greek Extended
    (0x2100 <= u && u <= 0x214f) ||                    // Letter-like block
    (0x1d49c <= u && u <= 0x1d59f)                     // Script/Double-struck/Fraktur
}

fn is_sub_script_alnum_unicode(u: u32) -> bool {
    (0x207f <= u && u <= 0x2089) ||  // n superscript + numeric subscripts
    (0x2090 <= u && u <= 0x209c) ||  // letter-like subscripts
    (0x1d62 <= u && u <= 0x1d6a)     // letter-like subscripts
}

fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || c == '\u{ab}' || // «
    is_letter_like_unicode(c as u32)
}

fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\'' || c == '?' || c == '!' ||
    is_letter_like_unicode(c as u32) || is_sub_script_alnum_unicode(c as u32)
}

// ============================================================================
// Keywords
// ============================================================================

const KEYWORDS: &[&str] = &[
    "def", "theorem", "lemma", "abbrev", "instance", "where",
    "let", "in", "if", "then", "else", "match", "with", "do", "return",
    "fun", "forall", "import", "open", "namespace", "section", "end",
    "class", "structure", "extends", "inductive",
    "axiom", "constant", "opaque",
    "set_option", "universe", "variable",
    "private", "protected", "noncomputable", "unsafe", "partial",
    "mutual", "attribute", "deriving",
    "prelude", "by", "from", "have", "show", "suffices", "calc",
    "at", "Type", "Prop", "Sort",
];

fn is_keyword(s: &str) -> bool {
    KEYWORDS.contains(&s)
}

// ============================================================================
// Multi-char symbols (longest match)
// ============================================================================

const SYMBOLS: &[&str] = &[
    ":=", "=>", "->", "→", "←", "<-", "↔", "<->",
    "..", "...", "×", "//",
    "&&", "||", "++", "::", "<|", "|>",
    "==", "!=", "≠", "<=", "≤", ">=", "≥",
    "⟨", "⟩", "⦃", "⦄",
    // single char
    "(", ")", "{", "}", "[", "]",
    ",", ";", ":", ".", "|", "@", "#",
    "+", "-", "*", "/", "^", "%", "&",
    "=", "<", ">", "!", "~", "\\",
    "∀", "∃", "λ", "Π", "Σ",
    "¬", "∧", "∨",
];

// ============================================================================
// Lexer
// ============================================================================

pub struct Lexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
    line: u32,
    col: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer { src, bytes: src.as_bytes(), pos: 0, line: 1, col: 0 }
    }

    pub fn tokenize_all(&mut self) -> Vec<SpannedToken> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            let is_eof = tok.token == Token::Eof;
            tokens.push(tok);
            if is_eof { break; }
        }
        tokens
    }

    fn peek_char(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn advance_char(&mut self) -> Option<char> {
        let c = self.peek_char()?;
        self.pos += c.len_utf8();
        if c == '\n' {
            self.line += 1;
            self.col = 0;
        } else {
            self.col += 1;
        }
        Some(c)
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek_char() {
            if c == ' ' || c == '\t' || c == '\r' || c == '\n' {
                self.advance_char();
            } else if self.starts_with("--") && !self.starts_with("---") || self.starts_with("--") && self.pos + 2 >= self.src.len() {
                // Line comment
                self.skip_line_comment();
            } else if self.starts_with("/-") && !self.starts_with("/--") {
                // Block comment (not doc comment)
                self.skip_block_comment();
            } else {
                break;
            }
        }
    }

    fn starts_with(&self, s: &str) -> bool {
        self.src[self.pos..].starts_with(s)
    }

    fn skip_line_comment(&mut self) {
        while let Some(c) = self.advance_char() {
            if c == '\n' { break; }
        }
    }

    fn skip_block_comment(&mut self) {
        // Skip "/-"
        self.advance_char();
        self.advance_char();
        let mut depth = 1u32;
        while depth > 0 {
            match self.advance_char() {
                None => break,
                Some('/') if self.starts_with("-") => {
                    self.advance_char();
                    depth += 1;
                }
                Some('-') if self.starts_with("/") => {
                    self.advance_char();
                    depth -= 1;
                }
                _ => {}
            }
        }
    }

    fn make_span(&self, start: usize, start_line: u32, start_col: u32) -> Span {
        Span { start: start as u32, end: self.pos as u32, line: start_line, col: start_col }
    }

    pub fn next_token(&mut self) -> SpannedToken {
        self.skip_whitespace();
        let start = self.pos;
        let start_line = self.line;
        let start_col = self.col;

        let c = match self.peek_char() {
            None => return SpannedToken {
                token: Token::Eof,
                span: self.make_span(start, start_line, start_col),
            },
            Some(c) => c,
        };

        // Doc comment
        if self.starts_with("/--") {
            return self.lex_doc_comment(start, start_line, start_col);
        }

        // Line comment (edge: --- is doc?)
        if self.starts_with("--") {
            self.skip_line_comment();
            return self.next_token();
        }

        // String literal
        if c == '"' {
            return self.lex_string(start, start_line, start_col);
        }

        // Char literal
        if c == '\'' && self.src[self.pos..].len() > 1 {
            let next = self.src[self.pos+1..].chars().next();
            if next.is_some() && next != Some('\'') {
                return self.lex_char(start, start_line, start_col);
            }
        }

        // Number literal
        if c.is_ascii_digit() {
            return self.lex_number(start, start_line, start_col);
        }

        // Guillemet-escaped identifier
        if c == '«' {
            return self.lex_guillemet(start, start_line, start_col);
        }

        // Identifier or keyword
        if is_id_first(c) {
            return self.lex_ident(start, start_line, start_col);
        }

        // Hash commands
        if c == '#' {
            self.advance_char();
            // Read following identifier
            if self.peek_char().map_or(false, |c| is_id_first(c)) {
                let id_start = self.pos;
                while self.peek_char().map_or(false, |c| is_id_rest(c)) {
                    self.advance_char();
                }
                let word = &self.src[id_start..self.pos];
                let kw = format!("#{}", word);
                return SpannedToken {
                    token: Token::Keyword(kw),
                    span: self.make_span(start, start_line, start_col),
                };
            }
            return SpannedToken {
                token: Token::Symbol("#".into()),
                span: self.make_span(start, start_line, start_col),
            };
        }

        // Try multi-char symbols (longest match)
        let remaining = &self.src[self.pos..];
        let mut best_len = 0;
        let mut best_sym = "";
        for &sym in SYMBOLS {
            if remaining.starts_with(sym) && sym.len() > best_len {
                best_len = sym.len();
                best_sym = sym;
            }
        }
        if best_len > 0 {
            for _ in 0..best_sym.chars().count() {
                self.advance_char();
            }
            return SpannedToken {
                token: Token::Symbol(best_sym.to_string()),
                span: self.make_span(start, start_line, start_col),
            };
        }

        // Unknown single char → symbol
        self.advance_char();
        SpannedToken {
            token: Token::Symbol(c.to_string()),
            span: self.make_span(start, start_line, start_col),
        }
    }

    fn lex_ident(&mut self, start: usize, start_line: u32, start_col: u32) -> SpannedToken {
        // Read dotted identifier: foo.bar.baz
        let mut parts: Vec<String> = Vec::new();
        loop {
            let part_start = self.pos;
            while self.peek_char().map_or(false, |c| is_id_rest(c)) {
                self.advance_char();
            }
            parts.push(self.src[part_start..self.pos].to_string());
            // Check for dot continuation
            if self.peek_char() == Some('.') {
                let dot_pos = self.pos;
                self.advance_char(); // consume dot
                if self.peek_char().map_or(false, |c| is_id_first(c)) {
                    // Continue dotted name
                    continue;
                } else if self.peek_char().map_or(false, |c| c.is_ascii_digit()) {
                    // Numeric component: foo.42
                    continue;
                } else {
                    // Dot was not part of identifier — put it back
                    self.pos = dot_pos;
                    self.col -= 1; // approximate
                    break;
                }
            }
            break;
        }

        let full = parts.join(".");
        if parts.len() == 1 && is_keyword(&parts[0]) {
            return SpannedToken {
                token: Token::Keyword(full),
                span: self.make_span(start, start_line, start_col),
            };
        }

        // Build Name
        let mut name = Name::anonymous();
        for part in &parts {
            if let Ok(n) = part.parse::<u64>() {
                name = Name::mk_numeral(&name, n);
            } else {
                name = Name::mk_string(&name, part);
            }
        }

        SpannedToken {
            token: Token::Ident(name),
            span: self.make_span(start, start_line, start_col),
        }
    }

    fn lex_number(&mut self, start: usize, start_line: u32, start_col: u32) -> SpannedToken {
        let first = self.advance_char().unwrap();
        if first == '0' {
            match self.peek_char() {
                Some('x') | Some('X') => {
                    self.advance_char();
                    let num_start = self.pos;
                    while self.peek_char().map_or(false, |c| c.is_ascii_hexdigit() || c == '_') {
                        self.advance_char();
                    }
                    let s: String = self.src[num_start..self.pos].chars().filter(|&c| c != '_').collect();
                    let n = u64::from_str_radix(&s, 16).unwrap_or(0);
                    return SpannedToken {
                        token: Token::NumLit(n),
                        span: self.make_span(start, start_line, start_col),
                    };
                }
                Some('b') | Some('B') => {
                    self.advance_char();
                    let num_start = self.pos;
                    while self.peek_char().map_or(false, |c| c == '0' || c == '1' || c == '_') {
                        self.advance_char();
                    }
                    let s: String = self.src[num_start..self.pos].chars().filter(|&c| c != '_').collect();
                    let n = u64::from_str_radix(&s, 2).unwrap_or(0);
                    return SpannedToken {
                        token: Token::NumLit(n),
                        span: self.make_span(start, start_line, start_col),
                    };
                }
                Some('o') | Some('O') => {
                    self.advance_char();
                    let num_start = self.pos;
                    while self.peek_char().map_or(false, |c| ('0'..='7').contains(&c) || c == '_') {
                        self.advance_char();
                    }
                    let s: String = self.src[num_start..self.pos].chars().filter(|&c| c != '_').collect();
                    let n = u64::from_str_radix(&s, 8).unwrap_or(0);
                    return SpannedToken {
                        token: Token::NumLit(n),
                        span: self.make_span(start, start_line, start_col),
                    };
                }
                _ => {}
            }
        }
        // Decimal
        while self.peek_char().map_or(false, |c| c.is_ascii_digit() || c == '_') {
            self.advance_char();
        }
        let s: String = self.src[start..self.pos].chars().filter(|&c| c != '_').collect();
        let n = s.parse::<u64>().unwrap_or(0);
        SpannedToken {
            token: Token::NumLit(n),
            span: self.make_span(start, start_line, start_col),
        }
    }

    fn lex_string(&mut self, start: usize, start_line: u32, start_col: u32) -> SpannedToken {
        self.advance_char(); // skip opening "
        let mut s = String::new();
        loop {
            match self.advance_char() {
                None | Some('"') => break,
                Some('\\') => {
                    match self.advance_char() {
                        Some('n') => s.push('\n'),
                        Some('t') => s.push('\t'),
                        Some('\\') => s.push('\\'),
                        Some('"') => s.push('"'),
                        Some('0') => s.push('\0'),
                        Some(c) => { s.push('\\'); s.push(c); }
                        None => break,
                    }
                }
                Some(c) => s.push(c),
            }
        }
        SpannedToken {
            token: Token::StrLit(s),
            span: self.make_span(start, start_line, start_col),
        }
    }

    fn lex_char(&mut self, start: usize, start_line: u32, start_col: u32) -> SpannedToken {
        self.advance_char(); // skip '
        let c = self.advance_char().unwrap_or('\0');
        let ch = if c == '\\' {
            match self.advance_char() {
                Some('n') => '\n',
                Some('t') => '\t',
                Some('\\') => '\\',
                Some('\'') => '\'',
                Some('0') => '\0',
                Some(x) => x,
                None => '\0',
            }
        } else { c };
        if self.peek_char() == Some('\'') { self.advance_char(); }
        SpannedToken {
            token: Token::CharLit(ch),
            span: self.make_span(start, start_line, start_col),
        }
    }

    fn lex_guillemet(&mut self, start: usize, start_line: u32, start_col: u32) -> SpannedToken {
        self.advance_char(); // skip «
        let inner_start = self.pos;
        while let Some(c) = self.peek_char() {
            if c == '»' { break; }
            self.advance_char();
        }
        let inner = self.src[inner_start..self.pos].to_string();
        if self.peek_char() == Some('»') { self.advance_char(); }
        let name = Name::mk_string(&Name::anonymous(), &inner);
        SpannedToken {
            token: Token::Ident(name),
            span: self.make_span(start, start_line, start_col),
        }
    }

    fn lex_doc_comment(&mut self, start: usize, start_line: u32, start_col: u32) -> SpannedToken {
        // Skip "/--"
        self.advance_char(); self.advance_char(); self.advance_char();
        let content_start = self.pos;
        let mut depth = 1u32;
        while depth > 0 {
            match self.advance_char() {
                None => break,
                Some('/') if self.starts_with("-") => { self.advance_char(); depth += 1; }
                Some('-') if self.starts_with("/") => { self.advance_char(); depth -= 1; }
                _ => {}
            }
        }
        let content_end = if self.pos >= 2 { self.pos - 2 } else { self.pos };
        let content = self.src[content_start..content_end].trim().to_string();
        SpannedToken {
            token: Token::DocComment(content),
            span: self.make_span(start, start_line, start_col),
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(s: &str) -> Vec<Token> {
        Lexer::new(s).tokenize_all().into_iter().map(|t| t.token).collect()
    }

    fn tok_strs(s: &str) -> Vec<String> {
        lex(s).iter().map(|t| match t {
            Token::Ident(n) => format!("id:{}", n),
            Token::NumLit(n) => format!("num:{}", n),
            Token::StrLit(s) => format!("str:{}", s),
            Token::CharLit(c) => format!("char:{}", c),
            Token::Keyword(k) => format!("kw:{}", k),
            Token::Symbol(s) => format!("sym:{}", s),
            Token::DocComment(s) => format!("doc:{}", s),
            Token::Eof => "eof".into(),
        }).collect()
    }

    #[test]
    fn test_def_x() {
        assert_eq!(tok_strs("def x := 0"), vec![
            "kw:def", "id:x", "sym::=", "num:0", "eof"
        ]);
    }

    #[test]
    fn test_def_with_type() {
        assert_eq!(tok_strs("def f (n : Nat) : Nat := n + 1"), vec![
            "kw:def", "id:f", "sym:(", "id:n", "sym::", "id:Nat", "sym:)",
            "sym::", "id:Nat", "sym::=", "id:n", "sym:+", "num:1", "eof"
        ]);
    }

    #[test]
    fn test_theorem() {
        assert_eq!(tok_strs("theorem foo : True := True.intro"), vec![
            "kw:theorem", "id:foo", "sym::", "id:True", "sym::=", "id:True.intro", "eof"
        ]);
    }

    #[test]
    fn test_lambda() {
        assert_eq!(tok_strs("fun x => x"), vec![
            "kw:fun", "id:x", "sym:=>", "id:x", "eof"
        ]);
    }

    #[test]
    fn test_arrow() {
        let toks = tok_strs("Nat → Nat");
        assert_eq!(toks, vec!["id:Nat", "sym:→", "id:Nat", "eof"]);
    }

    #[test]
    fn test_forall() {
        assert_eq!(tok_strs("∀ x, P x"), vec![
            "sym:∀", "id:x", "sym:,", "id:P", "id:x", "eof"
        ]);
    }

    #[test]
    fn test_unicode_ident() {
        let toks = lex("α β γ");
        assert!(matches!(&toks[0], Token::Ident(n) if n.to_string() == "α"));
        assert!(matches!(&toks[1], Token::Ident(n) if n.to_string() == "β"));
        assert!(matches!(&toks[2], Token::Ident(n) if n.to_string() == "γ"));
    }

    #[test]
    fn test_subscript() {
        let toks = lex("x₁ x₂");
        assert!(matches!(&toks[0], Token::Ident(n) if n.to_string() == "x₁"));
        assert!(matches!(&toks[1], Token::Ident(n) if n.to_string() == "x₂"));
    }

    #[test]
    fn test_number_hex() {
        assert_eq!(lex("0xFF")[0], Token::NumLit(255));
    }

    #[test]
    fn test_number_bin() {
        assert_eq!(lex("0b1010")[0], Token::NumLit(10));
    }

    #[test]
    fn test_string() {
        assert_eq!(lex("\"hello\"")[0], Token::StrLit("hello".into()));
    }

    #[test]
    fn test_string_escape() {
        assert_eq!(lex("\"a\\nb\"")[0], Token::StrLit("a\nb".into()));
    }

    #[test]
    fn test_line_comment() {
        assert_eq!(tok_strs("-- comment\ndef x := 0"), vec![
            "kw:def", "id:x", "sym::=", "num:0", "eof"
        ]);
    }

    #[test]
    fn test_block_comment() {
        assert_eq!(tok_strs("/- block -/ def x := 0"), vec![
            "kw:def", "id:x", "sym::=", "num:0", "eof"
        ]);
    }

    #[test]
    fn test_nested_block_comment() {
        assert_eq!(tok_strs("/- /- nested -/ -/ def x := 0"), vec![
            "kw:def", "id:x", "sym::=", "num:0", "eof"
        ]);
    }

    #[test]
    fn test_doc_comment() {
        let toks = lex("/-- A doc comment -/ def x := 0");
        assert!(matches!(&toks[0], Token::DocComment(s) if s == "A doc comment"));
    }

    #[test]
    fn test_guillemet() {
        let toks = lex("«term_+_»");
        assert!(matches!(&toks[0], Token::Ident(n) if n.to_string() == "term_+_"));
    }

    #[test]
    fn test_hash_command() {
        assert_eq!(tok_strs("#check Nat"), vec!["kw:#check", "id:Nat", "eof"]);
        assert_eq!(tok_strs("#eval 1 + 2"), vec!["kw:#eval", "num:1", "sym:+", "num:2", "eof"]);
    }

    #[test]
    fn test_dotted_name() {
        let toks = lex("Nat.succ");
        assert!(matches!(&toks[0], Token::Ident(n) if n.to_string() == "Nat.succ"));
    }

    #[test]
    fn test_implicit_binders() {
        assert_eq!(tok_strs("{α : Type}"), vec![
            "sym:{", "id:α", "sym::", "kw:Type", "sym:}", "eof"
        ]);
    }

    #[test]
    fn test_instance_binder() {
        assert_eq!(tok_strs("[Add Nat]"), vec![
            "sym:[", "id:Add", "id:Nat", "sym:]", "eof"
        ]);
    }

    #[test]
    fn test_import() {
        assert_eq!(tok_strs("import Init.Data.Nat.Basic"), vec![
            "kw:import", "id:Init.Data.Nat.Basic", "eof"
        ]);
    }

    #[test]
    fn test_multiline() {
        let toks = Lexer::new("def x\n  := 0").tokenize_all();
        assert_eq!(toks[0].span.line, 1);
        assert_eq!(toks[2].span.line, 2); // :=
    }

    #[test]
    fn test_prelude() {
        assert_eq!(tok_strs("prelude"), vec!["kw:prelude", "eof"]);
    }

    #[test]
    fn test_by() {
        assert_eq!(tok_strs("by exact trivial"), vec![
            "kw:by", "id:exact", "id:trivial", "eof"
        ]);
    }

    #[test]
    fn test_anonymous_constructor() {
        assert_eq!(tok_strs("⟨a, b⟩"), vec![
            "sym:⟨", "id:a", "sym:,", "id:b", "sym:⟩", "eof"
        ]);
    }
}
