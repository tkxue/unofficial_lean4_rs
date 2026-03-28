use std::io::{self, BufRead, Write};
use std::path::PathBuf;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Parse flags
    let mut file: Option<String> = None;
    let mut olean_out: Option<String> = None;
    let mut trust_level: u32 = 1024; // default: trust (like C++)
    let mut quiet = false;
    let mut print_stats = false;
    let mut print_deps = false;
    let mut profile = false;
    let mut show_help = false;
    let mut show_version = false;
    let mut short_version = false;
    let mut show_githash = false;
    let mut print_libdir = false;
    let mut run_mode = false;
    let mut repl_mode = false;
    let mut verify = false;
    let mut search_paths: Vec<PathBuf> = Vec::new();

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => show_help = true,
            "-v" | "--version" => show_version = true,
            "-V" | "--short-version" => short_version = true,
            "-g" | "--githash" => show_githash = true,
            "-q" | "--quiet" => quiet = true,
            "--stats" => print_stats = true,
            "--deps" => print_deps = true,
            "--profile" => profile = true,
            "--print-libdir" => print_libdir = true,
            "--repl" => repl_mode = true,
            "--verify" => verify = true,
            "--check-export" => {
                // Lean Kernel Arena mode: read NDJSON from stdin, check, exit 0/1/2
                let stdin = io::stdin();
                let mut reader = io::BufReader::new(stdin.lock());
                let code = lean4_kernel::export::check_export(&mut reader);
                std::process::exit(code);
            }
            "--run" => {
                run_mode = true;
                i += 1;
                if i < args.len() { file = Some(args[i].clone()); }
            }
            "-o" => {
                i += 1;
                if i < args.len() { olean_out = Some(args[i].clone()); }
            }
            "-t" | "--trust" => {
                i += 1;
                if i < args.len() { trust_level = args[i].parse().unwrap_or(1024); }
            }
            "--root" => { i += 1; } // skip value, not implemented
            "-L" | "--search-path" => {
                i += 1;
                if i < args.len() { search_paths.push(PathBuf::from(&args[i])); }
            }
            s if s.starts_with("-o=") => olean_out = Some(s[3..].to_string()),
            s if s.starts_with("-t=") || s.starts_with("--trust=") => {
                let v = s.split('=').nth(1).unwrap_or("1024");
                trust_level = v.parse().unwrap_or(1024);
            }
            s if s.starts_with("--root=") => {} // not implemented
            s if !s.starts_with('-') && file.is_none() => file = Some(s.to_string()),
            _ => {
                if !quiet { eprintln!("unknown flag: {}", args[i]); }
            }
        }
        i += 1;
    }

    // Default search path
    if search_paths.is_empty() {
        let lean_lib = std::env::var("LEAN_PATH").unwrap_or_else(|_| {
            let home = std::env::var("HOME").unwrap_or_default();
            format!("{}/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean", home)
        });
        for p in lean_lib.split(':') {
            if !p.is_empty() { search_paths.push(PathBuf::from(p)); }
        }
    }

    // Handle info flags
    if show_help {
        print_help();
        return;
    }
    if show_version {
        println!("Lean4 Rust Kernel (version 0.1.0, {}, Rust)", std::env::consts::ARCH);
        return;
    }
    if short_version { println!("0.1.0"); return; }
    if show_githash { println!("rust-lean4-kernel"); return; }
    if print_libdir {
        if let Some(p) = search_paths.first() { println!("{}", p.display()); }
        return;
    }

    // Handle file mode
    if let Some(ref path) = file {
        // If it's an NDJSON export file, use the export checker
        if path.ends_with(".ndjson") {
            let f = std::fs::File::open(path).unwrap_or_else(|e| {
                eprintln!("error: {}: {}", path, e); std::process::exit(1);
            });
            let mut reader = io::BufReader::new(f);
            let code = lean4_kernel::export::check_export(&mut reader);
            std::process::exit(code);
        }

        let t0 = Instant::now();

        if print_deps {
            // Just print imports
            let src = std::fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("error: {}: {}", path, e); std::process::exit(1);
            });
            let (_, imports, _) = lean4_kernel::parser::parse_file(&src);
            for imp in &imports { println!("{}", imp); }
            return;
        }

        let src = std::fs::read_to_string(path).unwrap_or_else(|e| {
            eprintln!("error: {}: {}", path, e); std::process::exit(1);
        });

        if !quiet { eprintln!("Processing {}...", path); }

        let env = match lean4_kernel::elaborator::interpret_lean_file(&src, &search_paths) {
            Ok(env) => env,
            Err(e) => { eprintln!("error: {}", e); std::process::exit(1); }
        };

        if !quiet {
            eprintln!("  {} constants ({:.2}s)", env.num_constants(), t0.elapsed().as_secs_f64());
        }

        if print_stats {
            println!("constants: {}", env.num_constants());
        }

        // Write NDJSON export if --export flag
        if std::env::args().any(|a| a == "--export") {
            let stdout = io::stdout();
            let mut writer = lean4_kernel::export_write::NdjsonWriter::new(stdout.lock());
            writer.write_environment(&env).unwrap_or_else(|e| eprintln!("export error: {}", e));
            return;
        }

        // Write .olean if requested
        if let Some(ref out_path) = olean_out {
            let module_name = lean4_kernel::name::Name::str(
                &path.replace('/', ".").replace(".lean", "")
            );
            let mut consts = Vec::new();
            env.for_each_constant(|_, ci| consts.push(ci.clone()));
            match lean4_kernel::olean_write::write_olean(
                &std::path::Path::new(out_path), &module_name, &[], &consts,
            ) {
                Ok(()) => { if !quiet { eprintln!("  wrote {}", out_path); } }
                Err(e) => eprintln!("error writing olean: {}", e),
            }
        }

        if verify {
            if !quiet { eprint!("  verifying... "); }
            let tv = Instant::now();
            let mut tc = lean4_kernel::type_checker::TypeChecker::new(
                env.clone(), lean4_kernel::local_ctx::LocalContext::new(),
            );
            let mut ok = 0u64;
            let mut fail = 0u64;
            env.for_each_constant(|_, ci| {
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    tc.infer_type(&ci.type_)
                })) {
                    Ok(_) => ok += 1,
                    Err(_) => fail += 1,
                }
            });
            if !quiet {
                eprintln!("{}/{} OK ({:.2}s)", ok, ok + fail, tv.elapsed().as_secs_f64());
            }
        }

        return;
    }

    // REPL mode (default when no file given)
    run_repl(&search_paths, quiet);
}

fn run_repl(search_paths: &[PathBuf], quiet: bool) {
    if !quiet { eprintln!("Loading Init..."); }
    let env = match lean4_kernel::olean_fast::load_module_tree_fast(
        &lean4_kernel::name::Name::str("Init"), search_paths,
    ) {
        Ok(loaded) => {
            if !quiet {
                eprintln!("Loaded {} constants from {} modules",
                    loaded.env.num_constants(), loaded.modules_loaded.len());
            }
            loaded.env
        }
        Err(e) => {
            eprintln!("Failed to load Init: {}", e);
            lean4_kernel::env::Environment::new(0)
        }
    };

    let mut elab = lean4_kernel::elaborator::Elaborator::new(env);
    let mut multi_line = String::new();
    let mut line_buf = String::new();

    println!("Lean4 REPL (Rust) — type definitions, theorems, #check, etc.");
    println!("Commands: :quit :env :reset :help\n");

    loop {
        if multi_line.is_empty() { print!("> "); } else { print!("  "); }
        io::stdout().flush().ok();

        line_buf.clear();
        match io::stdin().lock().read_line(&mut line_buf) {
            Ok(0) => break,
            Ok(_) => {}
            Err(_) => break,
        }

        let line = line_buf.trim_end();

        match line {
            ":quit" | ":q" => break,
            ":env" => { println!("{} constants", elab.env.num_constants()); continue; }
            ":reset" => {
                let e = elab.env.clone();
                elab = lean4_kernel::elaborator::Elaborator::new(e);
                println!("Reset."); continue;
            }
            ":help" => {
                println!("  :quit    exit");
                println!("  :env     show constant count");
                println!("  :reset   reset elaborator");
                println!("  #check e show type of expression");
                continue;
            }
            _ => {}
        }

        multi_line.push_str(line);
        multi_line.push('\n');

        let should_process = line.is_empty() && !multi_line.trim().is_empty()
            || (!multi_line.trim().is_empty() && !line.is_empty() && {
                let t = multi_line.trim();
                t.starts_with("def ") || t.starts_with("theorem ") || t.starts_with("lemma ")
                || t.starts_with("axiom ") || t.starts_with("abbrev ")
                || t.starts_with("#check ") || t.starts_with("#eval ")
                || t.starts_with("open ") || t.starts_with("namespace ")
                || t.starts_with("end") || t.starts_with("variable ")
                || t.starts_with("universe ") || t.starts_with("inductive ")
                || t.starts_with("structure ") || t.starts_with("class ")
                || t.starts_with("instance ") || t.starts_with("mutual")
            });

        if !should_process { continue; }

        let input = multi_line.trim().to_string();
        multi_line.clear();
        if input.is_empty() { continue; }

        // #check
        if input.starts_with("#check ") {
            let term = input.trim_start_matches("#check ").trim();
            let (_, _, cmds) = lean4_kernel::parser::parse_file(&format!("def _chk := {}", term));
            for cmd in &cmds { let _ = elab.elab_command(cmd); }
            if let Some(ci) = elab.env.find(&lean4_kernel::name::Name::str("_chk")) {
                println!("{} : {}", term, ci.type_);
            } else {
                println!("error: could not check '{}'", term);
            }
            continue;
        }

        // #eval
        if input.starts_with("#eval ") {
            let term = input.trim_start_matches("#eval ").trim();
            let (_, _, cmds) = lean4_kernel::parser::parse_file(&format!("def _ev := {}", term));
            for cmd in &cmds { let _ = elab.elab_command(cmd); }
            if let Some(ci) = elab.env.find(&lean4_kernel::name::Name::str("_ev")) {
                if let Some(val) = ci.get_value() {
                    match lean4_kernel::eval::eval_expr(val, &elab.env) {
                        Ok(s) => println!("{}", s),
                        Err(e) => println!("eval error: {}", e),
                    }
                } else {
                    println!("no value to evaluate");
                }
            } else {
                println!("error: could not elaborate '{}'", term);
            }
            continue;
        }

        // Normal elaboration
        let (_, _, commands) = lean4_kernel::parser::parse_file(&input);
        let before = elab.env.num_constants();
        for cmd in &commands {
            if let Err(e) = elab.elab_command(cmd) {
                eprintln!("error: {}", e);
            }
        }
        let new = elab.env.num_constants() - before;
        if new > 0 { println!("  ({} added)", new); }
    }
    println!("Bye!");
}

fn print_help() {
    println!("Lean4 Rust Kernel (version 0.1.0)");
    println!();
    println!("USAGE:");
    println!("  lean4_kernel [FLAGS] [FILE]");
    println!();
    println!("FLAGS:");
    println!("  -h, --help         Show this help");
    println!("  -v, --version      Show version");
    println!("  -V, --short-version  Show short version");
    println!("  -g, --githash      Show git hash");
    println!("  -o FILE            Write .olean output");
    println!("  -t, --trust=N      Trust level (0=verify all, 1024=trust .olean)");
    println!("  -q, --quiet        Suppress info messages");
    println!("  --verify           Re-type-check all constants after loading");
    println!("  --stats            Print environment statistics");
    println!("  --deps             Print file dependencies and exit");
    println!("  --profile          Show timing for each declaration");
    println!("  --print-libdir     Print library directory and exit");
    println!("  --repl             Start interactive REPL (default if no file)");
    println!("  --run FILE         Interpret a .lean file");
    println!("  -L, --search-path  Add search path for .olean files");
    println!();
    println!("ENVIRONMENT:");
    println!("  LEAN_PATH          Colon-separated .olean search paths");
    println!();
    println!("EXAMPLES:");
    println!("  lean4_kernel                     # start REPL");
    println!("  lean4_kernel file.lean           # interpret file");
    println!("  lean4_kernel file.lean -o out.olean  # compile to .olean");
    println!("  lean4_kernel file.lean --verify  # interpret + verify");
    println!("  lean4_kernel file.lean --deps    # print imports");
}
