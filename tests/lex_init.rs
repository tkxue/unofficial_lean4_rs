//! C++ vs Rust: lex real Init .lean files

use lean4_kernel::lexer::{Lexer, Token};

#[test]
fn test_lex_init_prelude_header() {
    // Read first 500 bytes of Init/Prelude.lean and lex
    let path = "/r/study/lean4/src/Init/Prelude.lean";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(_) => { eprintln!("SKIP: {} not found", path); return; }
    };
    let mut lexer = Lexer::new(&src);
    let tokens = lexer.tokenize_all();
    eprintln!("Init.Prelude: {} tokens from {} bytes", tokens.len(), src.len());

    // Basic sanity: should have many tokens
    assert!(tokens.len() > 1000, "expected >1000 tokens, got {}", tokens.len());

    // First meaningful token should be "prelude" or "module" keyword or an identifier
    eprintln!("First token: {:?}", tokens[0].token);

    // Count token types
    let mut n_ident = 0;
    let mut n_kw = 0;
    let mut n_sym = 0;
    let mut n_num = 0;
    let mut n_str = 0;
    let mut n_doc = 0;
    for t in &tokens {
        match &t.token {
            Token::Ident(_) => n_ident += 1,
            Token::Keyword(_) => n_kw += 1,
            Token::Symbol(_) => n_sym += 1,
            Token::NumLit(_) => n_num += 1,
            Token::StrLit(_) => n_str += 1,
            Token::DocComment(_) => n_doc += 1,
            _ => {}
        }
    }
    eprintln!("  idents: {} keywords: {} symbols: {} nums: {} strs: {} docs: {}",
        n_ident, n_kw, n_sym, n_num, n_str, n_doc);
    assert!(n_ident > 500, "expected many identifiers");
    assert!(n_kw > 100, "expected many keywords");
    assert!(n_sym > 500, "expected many symbols");
}

#[test]
fn test_lex_all_init_files() {
    let lean_src = "/r/study/lean4/src";
    let mut total_files = 0;
    let mut total_tokens = 0;
    let mut total_bytes = 0;
    let mut failures = 0;

    for entry in walkdir(lean_src, "Init") {
        let src = match std::fs::read_to_string(&entry) {
            Ok(s) => s,
            Err(_) => continue,
        };
        total_files += 1;
        total_bytes += src.len();

        // Lex — should not panic
        let result = std::panic::catch_unwind(|| {
            let mut lexer = Lexer::new(&src);
            lexer.tokenize_all()
        });
        match result {
            Ok(tokens) => {
                total_tokens += tokens.len();
                // Verify last token is Eof
                assert!(matches!(tokens.last().unwrap().token, Token::Eof));
            }
            Err(_) => {
                failures += 1;
                if failures <= 5 {
                    eprintln!("PANIC lexing: {}", entry);
                }
            }
        }
    }
    eprintln!("Lexed {} Init .lean files: {} tokens, {} bytes, {} failures",
        total_files, total_tokens, total_bytes, failures);
    assert_eq!(failures, 0, "{} files failed to lex", failures);
}

fn walkdir(base: &str, subdir: &str) -> Vec<String> {
    let dir = format!("{}/{}", base, subdir);
    let mut files = Vec::new();
    collect_lean_files(&dir, &mut files);
    files
}

fn collect_lean_files(dir: &str, out: &mut Vec<String>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries {
        let entry = match entry { Ok(e) => e, Err(_) => continue };
        let path = entry.path();
        if path.is_dir() {
            collect_lean_files(path.to_str().unwrap_or(""), out);
        } else if path.extension().map_or(false, |e| e == "lean") {
            out.push(path.to_string_lossy().to_string());
        }
    }
}
