//! Parse lean4export NDJSON format and type-check declarations.
//! For the Lean Kernel Arena: https://arena.lean-lang.org

use std::collections::HashMap;
use std::io::{self, BufRead};

use crate::env::*;
use crate::expr::*;
use crate::level::Level;
use crate::local_ctx::LocalContext;
use crate::name::Name;
use crate::type_checker::TypeChecker;

/// Parse and check an NDJSON export from stdin.
/// Returns: 0 = accept, 1 = reject, 2 = decline.
pub fn check_export(input: &mut dyn BufRead) -> i32 {
    let mut names: HashMap<u64, Name> = HashMap::new();
    let mut levels: HashMap<u64, Level> = HashMap::new();
    let mut exprs: HashMap<u64, Expr> = HashMap::new();
    let mut env = Environment::new(0);
    names.insert(0, Name::anonymous());
    levels.insert(0, Level::zero());

    let mut line_num = 0u64;
    let mut decl_count = 0u64;
    let mut errors = 0u64;

    for line_result in input.lines() {
        line_num += 1;
        let line = match line_result {
            Ok(l) => l,
            Err(_) => continue,
        };
        let line = line.trim();
        if line.is_empty() { continue; }

        // Parse JSON (minimal — just extract key fields)
        let obj = match minijson::parse(line) {
            Some(o) => o,
            None => continue,
        };

        // Name definition: {"in": id, "str": {"pre": pid, "str": s}} or {"in": id, "num": {"pre": pid, "num": n}}
        if let Some(id) = obj.get_u64("in") {
            if let Some(str_obj) = obj.get_obj("str") {
                let pre = str_obj.get_u64("pre").unwrap_or(0);
                let s = str_obj.get_str("str").unwrap_or("");
                let prefix = names.get(&pre).cloned().unwrap_or_else(Name::anonymous);
                names.insert(id, Name::mk_string(&prefix, s));
            } else if let Some(num_obj) = obj.get_obj("num") {
                let pre = num_obj.get_u64("pre").unwrap_or(0);
                let n = num_obj.get_u64("num").unwrap_or(0);
                let prefix = names.get(&pre).cloned().unwrap_or_else(Name::anonymous);
                names.insert(id, Name::mk_numeral(&prefix, n));
            }
            continue;
        }

        // Level definition: {"il": id, "succ": inner} or {"il": id, "max": [a, b]} etc.
        if let Some(id) = obj.get_u64("il") {
            let level = if let Some(inner) = obj.get_u64("succ") {
                Level::mk_succ(levels.get(&inner).unwrap_or(&Level::zero()))
            } else if let Some(arr) = obj.get_arr("max") {
                let a = levels.get(&arr[0]).cloned().unwrap_or_else(Level::zero);
                let b = levels.get(&arr[1]).cloned().unwrap_or_else(Level::zero);
                Level::mk_max_core(&a, &b)
            } else if let Some(arr) = obj.get_arr("imax") {
                let a = levels.get(&arr[0]).cloned().unwrap_or_else(Level::zero);
                let b = levels.get(&arr[1]).cloned().unwrap_or_else(Level::zero);
                Level::mk_imax_core(&a, &b)
            } else if let Some(name_id) = obj.get_u64("param") {
                Level::mk_param(names.get(&name_id).unwrap_or(&Name::anonymous()))
            } else if let Some(name_id) = obj.get_u64("mvar") {
                Level::mk_mvar(names.get(&name_id).unwrap_or(&Name::anonymous()))
            } else {
                Level::zero()
            };
            levels.insert(id, level);
            continue;
        }

        // Expr definition: {"ie": id, ...}
        if let Some(id) = obj.get_u64("ie") {
            let expr = parse_expr(&obj, &names, &levels, &exprs);
            exprs.insert(id, expr);
            continue;
        }

        // Declarations
        if obj.has("axiom") {
            if let Some(decl_obj) = obj.get_obj("axiom") {
                match parse_and_add_axiom(&decl_obj, &names, &levels, &exprs, &mut env) {
                    Ok(()) => { decl_count += 1; }
                    Err(e) => { eprintln!("line {}: axiom error: {}", line_num, e); errors += 1; }
                }
            }
            continue;
        }
        if obj.has("def") {
            if let Some(decl_obj) = obj.get_obj("def") {
                match parse_and_add_def(&decl_obj, &names, &levels, &exprs, &mut env) {
                    Ok(()) => { decl_count += 1; }
                    Err(e) => { eprintln!("line {}: def error: {}", line_num, e); errors += 1; }
                }
            }
            continue;
        }
        if obj.has("theorem") {
            if let Some(decl_obj) = obj.get_obj("theorem") {
                match parse_and_add_theorem(&decl_obj, &names, &levels, &exprs, &mut env) {
                    Ok(()) => { decl_count += 1; }
                    Err(e) => { eprintln!("line {}: theorem error: {}", line_num, e); errors += 1; }
                }
            }
            continue;
        }
        if obj.has("opaque") {
            if let Some(decl_obj) = obj.get_obj("opaque") {
                match parse_and_add_opaque(&decl_obj, &names, &levels, &exprs, &mut env) {
                    Ok(()) => { decl_count += 1; }
                    Err(e) => { eprintln!("line {}: opaque error: {}", line_num, e); errors += 1; }
                }
            }
            continue;
        }
        if obj.has("inductive") {
            if let Some(decl_obj) = obj.get_obj("inductive") {
                match parse_and_add_inductive(&decl_obj, &names, &levels, &exprs, &mut env) {
                    Ok(n) => { decl_count += n; }
                    Err(e) => { eprintln!("line {}: inductive error: {}", line_num, e); errors += 1; }
                }
            }
            continue;
        }
        if obj.has("quot") {
            // Add quotient types
            let names_list = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];
            for &n in &names_list {
                let ci = ConstantInfo {
                    name: Name::str(n),
                    lparams: vec![Name::str("u")],
                    type_: Expr::mk_type(),
                    kind: ConstantInfoKind::Quot {
                        kind: match n {
                            "Quot" => QuotKind::Type,
                            "Quot.mk" => QuotKind::Mk,
                            "Quot.lift" => QuotKind::Lift,
                            "Quot.ind" => QuotKind::Ind,
                            _ => QuotKind::Type,
                        },
                    },
                };
                let _ = env.add_constant_info(ci);
            }
            decl_count += 4;
            continue;
        }
    }

    // Now verify all declarations
    let mut tc = TypeChecker::new(env.clone(), LocalContext::new());
    let mut verify_ok = 0u64;
    let mut verify_fail = 0u64;
    env.for_each_constant(|name, ci| {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // Check type is well-formed
            let _type_of_type = tc.infer_type(&ci.type_);
            // Check value type matches declared type (the real soundness check)
            if let Some(value) = ci.get_value() {
                let val_type = tc.infer_type(value);
                if !tc.is_def_eq(&val_type, &ci.type_) {
                    panic!("type mismatch for {}", name);
                }
            }
        }));
        match result {
            Ok(_) => verify_ok += 1,
            Err(e) => {
                verify_fail += 1;
                if verify_fail <= 10 {
                    let msg = if let Some(s) = e.downcast_ref::<String>() { s.clone() }
                    else if let Some(s) = e.downcast_ref::<&str>() { s.to_string() }
                    else { "unknown".to_string() };
                    eprintln!("verify fail: {} ({})", name, msg);
                }
            }
        }
    });

    eprintln!("{} declarations, {} verified OK, {} verify failures, {} parse errors",
        decl_count, verify_ok, verify_fail, errors);

    // Exit codes: 0=accept, 1=reject, 2=decline
    if errors > 0 || verify_fail > 0 { 1 } else { 0 }
}

// ============================================================================
// Expr parsing
// ============================================================================

fn parse_expr(obj: &minijson::JsonObj, names: &HashMap<u64, Name>, levels: &HashMap<u64, Level>, exprs: &HashMap<u64, Expr>) -> Expr {
    if let Some(bv) = obj.get_u64("bvar") {
        return Expr::mk_bvar(bv);
    }
    if let Some(lvl_id) = obj.get_u64("sort") {
        let lvl = levels.get(&lvl_id).cloned().unwrap_or_else(Level::zero);
        return Expr::mk_sort(&lvl);
    }
    if let Some(const_obj) = obj.get_obj("const") {
        let name_id = const_obj.get_u64("name").unwrap_or(0);
        let name = names.get(&name_id).cloned().unwrap_or_else(Name::anonymous);
        let us = const_obj.get_arr("us").unwrap_or_default();
        let lvls: Vec<Level> = us.iter()
            .map(|&id| levels.get(&id).cloned().unwrap_or_else(Level::zero))
            .collect();
        return Expr::mk_const(&name, &lvls);
    }
    if let Some(app_obj) = obj.get_obj("app") {
        let fn_id = app_obj.get_u64("fn").unwrap_or(0);
        let arg_id = app_obj.get_u64("arg").unwrap_or(0);
        let f = exprs.get(&fn_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        let a = exprs.get(&arg_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        return Expr::mk_app(&f, &a);
    }
    if let Some(lam_obj) = obj.get_obj("lam") {
        let name_id = lam_obj.get_u64("name").unwrap_or(0);
        let name = names.get(&name_id).cloned().unwrap_or_else(Name::anonymous);
        let bi = parse_binder_info(lam_obj.get_str("binderInfo").unwrap_or("default"));
        let type_id = lam_obj.get_u64("type").unwrap_or(0);
        let body_id = lam_obj.get_u64("body").unwrap_or(0);
        let ty = exprs.get(&type_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        let body = exprs.get(&body_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        return Expr::mk_lambda(&name, bi, &ty, &body);
    }
    if let Some(pi_obj) = obj.get_obj("forallE") {
        let name_id = pi_obj.get_u64("name").unwrap_or(0);
        let name = names.get(&name_id).cloned().unwrap_or_else(Name::anonymous);
        let bi = parse_binder_info(pi_obj.get_str("binderInfo").unwrap_or("default"));
        let type_id = pi_obj.get_u64("type").unwrap_or(0);
        let body_id = pi_obj.get_u64("body").unwrap_or(0);
        let ty = exprs.get(&type_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        let body = exprs.get(&body_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        return Expr::mk_pi(&name, bi, &ty, &body);
    }
    if let Some(let_obj) = obj.get_obj("letE") {
        let name_id = let_obj.get_u64("name").unwrap_or(0);
        let name = names.get(&name_id).cloned().unwrap_or_else(Name::anonymous);
        let type_id = let_obj.get_u64("type").unwrap_or(0);
        let val_id = let_obj.get_u64("value").unwrap_or(0);
        let body_id = let_obj.get_u64("body").unwrap_or(0);
        let ty = exprs.get(&type_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        let val = exprs.get(&val_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        let body = exprs.get(&body_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        return Expr::mk_let(&name, &ty, &val, &body, false);
    }
    if let Some(lit_obj) = obj.get_obj("lit") {
        if let Some(n) = lit_obj.get_u64("natVal") {
            return Expr::mk_lit(Literal::Nat(n));
        }
        if let Some(s) = lit_obj.get_str("strVal") {
            return Expr::mk_lit(Literal::Str(s.to_string()));
        }
    }
    if let Some(n) = obj.get_u64("lit") {
        return Expr::mk_lit(Literal::Nat(n));
    }
    if let Some(proj_obj) = obj.get_obj("proj") {
        let name_id = proj_obj.get_u64("typeName").unwrap_or(0);
        let name = names.get(&name_id).cloned().unwrap_or_else(Name::anonymous);
        let idx = proj_obj.get_u64("idx").unwrap_or(0);
        let expr_id = proj_obj.get_u64("expr").unwrap_or(0);
        let e = exprs.get(&expr_id).cloned().unwrap_or_else(|| Expr::mk_bvar(0));
        return Expr::mk_proj(&name, idx, &e);
    }
    Expr::mk_bvar(0)
}

fn parse_binder_info(s: &str) -> BinderInfo {
    match s {
        "implicit" => BinderInfo::Implicit,
        "strictImplicit" => BinderInfo::StrictImplicit,
        "instImplicit" => BinderInfo::InstImplicit,
        _ => BinderInfo::Default,
    }
}

fn get_name(id: u64, names: &HashMap<u64, Name>) -> Name {
    names.get(&id).cloned().unwrap_or_else(Name::anonymous)
}

fn get_level_params(ids: &[u64], names: &HashMap<u64, Name>) -> Vec<Name> {
    ids.iter().map(|&id| get_name(id, names)).collect()
}

fn get_expr(id: u64, exprs: &HashMap<u64, Expr>) -> Expr {
    exprs.get(&id).cloned().unwrap_or_else(|| Expr::mk_bvar(0))
}

// ============================================================================
// Declaration parsing
// ============================================================================

fn parse_and_add_axiom(obj: &minijson::JsonObj, names: &HashMap<u64, Name>, levels: &HashMap<u64, Level>, exprs: &HashMap<u64, Expr>, env: &mut Environment) -> Result<(), String> {
    let name = get_name(obj.get_u64("name").ok_or("no name")?, names);
    let lparams = get_level_params(&obj.get_arr("levelParams").unwrap_or_default(), names);
    let type_ = get_expr(obj.get_u64("type").ok_or("no type")?, exprs);
    let is_unsafe = obj.get_bool("isUnsafe").unwrap_or(false);
    let ci = ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Axiom { is_unsafe } };
    *env = env.add_constant_info(ci).map_err(|e| e.to_string())?;
    Ok(())
}

fn parse_and_add_def(obj: &minijson::JsonObj, names: &HashMap<u64, Name>, levels: &HashMap<u64, Level>, exprs: &HashMap<u64, Expr>, env: &mut Environment) -> Result<(), String> {
    let name = get_name(obj.get_u64("name").ok_or("no name")?, names);
    let lparams = get_level_params(&obj.get_arr("levelParams").unwrap_or_default(), names);
    let type_ = get_expr(obj.get_u64("type").ok_or("no type")?, exprs);
    let value = get_expr(obj.get_u64("value").ok_or("no value")?, exprs);
    let hints = match obj.get_str("hints") {
        Some("abbrev") => ReducibilityHints::Abbreviation,
        Some("opaque") => ReducibilityHints::Opaque,
        _ => ReducibilityHints::Regular(obj.get_u64("height").unwrap_or(1) as u32),
    };
    let safety = match obj.get_str("safety") {
        Some("unsafe") => DefinitionSafety::Unsafe,
        Some("partial") => DefinitionSafety::Partial,
        _ => DefinitionSafety::Safe,
    };
    let ci = ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Definition { value, hints, safety } };
    *env = env.add_constant_info(ci).map_err(|e| e.to_string())?;
    Ok(())
}

fn parse_and_add_theorem(obj: &minijson::JsonObj, names: &HashMap<u64, Name>, _levels: &HashMap<u64, Level>, exprs: &HashMap<u64, Expr>, env: &mut Environment) -> Result<(), String> {
    let name = get_name(obj.get_u64("name").ok_or("no name")?, names);
    let lparams = get_level_params(&obj.get_arr("levelParams").unwrap_or_default(), names);
    let type_ = get_expr(obj.get_u64("type").ok_or("no type")?, exprs);
    let value = get_expr(obj.get_u64("value").ok_or("no value")?, exprs);
    let ci = ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Theorem { value } };
    *env = env.add_constant_info(ci).map_err(|e| e.to_string())?;
    Ok(())
}

fn parse_and_add_opaque(obj: &minijson::JsonObj, names: &HashMap<u64, Name>, _levels: &HashMap<u64, Level>, exprs: &HashMap<u64, Expr>, env: &mut Environment) -> Result<(), String> {
    let name = get_name(obj.get_u64("name").ok_or("no name")?, names);
    let lparams = get_level_params(&obj.get_arr("levelParams").unwrap_or_default(), names);
    let type_ = get_expr(obj.get_u64("type").ok_or("no type")?, exprs);
    let value = get_expr(obj.get_u64("value").ok_or("no value")?, exprs);
    let is_unsafe = obj.get_bool("isUnsafe").unwrap_or(false);
    let ci = ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Opaque { value, is_unsafe } };
    *env = env.add_constant_info(ci).map_err(|e| e.to_string())?;
    Ok(())
}

fn parse_and_add_inductive(obj: &minijson::JsonObj, names: &HashMap<u64, Name>, levels: &HashMap<u64, Level>, exprs: &HashMap<u64, Expr>, env: &mut Environment) -> Result<u64, String> {
    let mut count = 0u64;
    // Types
    if let Some(types) = obj.get_arr_obj("types") {
        for ty_obj in &types {
            let name = get_name(ty_obj.get_u64("name").unwrap_or(0), names);
            let lparams = get_level_params(&ty_obj.get_arr("levelParams").unwrap_or_default(), names);
            let type_ = get_expr(ty_obj.get_u64("type").unwrap_or(0), exprs);
            let nparams = ty_obj.get_u64("numParams").unwrap_or(0) as u32;
            let nindices = ty_obj.get_u64("numIndices").unwrap_or(0) as u32;
            let all: Vec<Name> = ty_obj.get_arr("all").unwrap_or_default().iter()
                .map(|&id| get_name(id, names)).collect();
            let ctors: Vec<Name> = ty_obj.get_arr("ctors").unwrap_or_default().iter()
                .map(|&id| get_name(id, names)).collect();
            let nnested = ty_obj.get_u64("numNested").unwrap_or(0) as u32;
            let is_rec = ty_obj.get_bool("isRec").unwrap_or(false);
            let is_unsafe = ty_obj.get_bool("isUnsafe").unwrap_or(false);
            let is_reflexive = ty_obj.get_bool("isReflexive").unwrap_or(false);
            let ci = ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Inductive {
                nparams, nindices, all, ctors, nnested, is_rec, is_unsafe, is_reflexive,
            }};
            *env = env.replace_constant_info(ci);
            count += 1;
        }
    }
    // Constructors
    if let Some(ctors) = obj.get_arr_obj("ctors") {
        for ctor_obj in &ctors {
            let name = get_name(ctor_obj.get_u64("name").unwrap_or(0), names);
            let lparams = get_level_params(&ctor_obj.get_arr("levelParams").unwrap_or_default(), names);
            let type_ = get_expr(ctor_obj.get_u64("type").unwrap_or(0), exprs);
            let induct_name = get_name(ctor_obj.get_u64("induct").unwrap_or(0), names);
            let cidx = ctor_obj.get_u64("cidx").unwrap_or(0) as u32;
            let nparams = ctor_obj.get_u64("numParams").unwrap_or(0) as u32;
            let nfields = ctor_obj.get_u64("numFields").unwrap_or(0) as u32;
            let is_unsafe = ctor_obj.get_bool("isUnsafe").unwrap_or(false);
            let ci = ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Constructor {
                induct_name, cidx, nparams, nfields, is_unsafe,
            }};
            *env = env.replace_constant_info(ci);
            count += 1;
        }
    }
    // Recursors
    if let Some(recs) = obj.get_arr_obj("recs") {
        for rec_obj in &recs {
            let name = get_name(rec_obj.get_u64("name").unwrap_or(0), names);
            let lparams = get_level_params(&rec_obj.get_arr("levelParams").unwrap_or_default(), names);
            let type_ = get_expr(rec_obj.get_u64("type").unwrap_or(0), exprs);
            let all: Vec<Name> = rec_obj.get_arr("all").unwrap_or_default().iter()
                .map(|&id| get_name(id, names)).collect();
            let nparams = rec_obj.get_u64("numParams").unwrap_or(0) as u32;
            let nindices = rec_obj.get_u64("numIndices").unwrap_or(0) as u32;
            let nmotives = rec_obj.get_u64("numMotives").unwrap_or(0) as u32;
            let nminors = rec_obj.get_u64("numMinors").unwrap_or(0) as u32;
            let k = rec_obj.get_bool("k").unwrap_or(false);
            let is_unsafe = rec_obj.get_bool("isUnsafe").unwrap_or(false);
            let rules: Vec<RecursorRule> = rec_obj.get_arr_obj("rules").unwrap_or_default().iter()
                .map(|rule_obj| {
                    let ctor_name = get_name(rule_obj.get_u64("ctor").unwrap_or(0), names);
                    let nfields = rule_obj.get_u64("nfields").unwrap_or(0) as u32;
                    let rhs = get_expr(rule_obj.get_u64("rhs").unwrap_or(0), exprs);
                    RecursorRule { ctor_name, nfields, rhs }
                }).collect();
            let ci = ConstantInfo { name, lparams, type_, kind: ConstantInfoKind::Recursor {
                all, nparams, nindices, nmotives, nminors, rules, k, is_unsafe,
            }};
            *env = env.replace_constant_info(ci);
            count += 1;
        }
    }
    Ok(count)
}

// ============================================================================
// Minimal JSON parser (no serde dependency)
// ============================================================================

pub mod minijson {
    use std::collections::HashMap;

    #[derive(Clone, Debug)]
    pub struct JsonObj {
        fields: HashMap<String, JsonVal>,
    }

    #[derive(Clone, Debug)]
    enum JsonVal {
        Num(f64),
        Str(String),
        Bool(bool),
        Arr(Vec<JsonVal>),
        Obj(JsonObj),
        Null,
    }

    impl JsonObj {
        pub fn get_u64(&self, key: &str) -> Option<u64> {
            match self.fields.get(key)? {
                JsonVal::Num(n) => Some(*n as u64),
                _ => None,
            }
        }
        pub fn get_str(&self, key: &str) -> Option<&str> {
            match self.fields.get(key)? {
                JsonVal::Str(s) => Some(s),
                _ => None,
            }
        }
        pub fn get_bool(&self, key: &str) -> Option<bool> {
            match self.fields.get(key)? {
                JsonVal::Bool(b) => Some(*b),
                _ => None,
            }
        }
        pub fn get_obj(&self, key: &str) -> Option<&JsonObj> {
            match self.fields.get(key)? {
                JsonVal::Obj(o) => Some(o),
                _ => None,
            }
        }
        pub fn get_arr(&self, key: &str) -> Option<Vec<u64>> {
            match self.fields.get(key)? {
                JsonVal::Arr(arr) => {
                    Some(arr.iter().filter_map(|v| match v {
                        JsonVal::Num(n) => Some(*n as u64),
                        _ => None,
                    }).collect())
                }
                _ => None,
            }
        }
        pub fn get_arr_obj(&self, key: &str) -> Option<Vec<JsonObj>> {
            match self.fields.get(key)? {
                JsonVal::Arr(arr) => {
                    Some(arr.iter().filter_map(|v| match v {
                        JsonVal::Obj(o) => Some(o.clone()),
                        _ => None,
                    }).collect())
                }
                _ => None,
            }
        }
        pub fn has(&self, key: &str) -> bool { self.fields.contains_key(key) }
    }

    pub fn parse(s: &str) -> Option<JsonObj> {
        let s = s.trim();
        if !s.starts_with('{') { return None; }
        let (val, _) = parse_value(s)?;
        match val {
            JsonVal::Obj(o) => Some(o),
            _ => None,
        }
    }

    fn parse_value(s: &str) -> Option<(JsonVal, &str)> {
        let s = skip_ws(s);
        if s.is_empty() { return None; }
        match s.as_bytes()[0] {
            b'"' => parse_string(s),
            b'{' => parse_object(s),
            b'[' => parse_array(s),
            b't' if s.starts_with("true") => Some((JsonVal::Bool(true), &s[4..])),
            b'f' if s.starts_with("false") => Some((JsonVal::Bool(false), &s[5..])),
            b'n' if s.starts_with("null") => Some((JsonVal::Null, &s[4..])),
            _ => parse_number(s),
        }
    }

    fn parse_string(s: &str) -> Option<(JsonVal, &str)> {
        let s = &s[1..]; // skip opening "
        let mut end = 0;
        let bytes = s.as_bytes();
        while end < bytes.len() {
            if bytes[end] == b'"' { break; }
            if bytes[end] == b'\\' { end += 1; } // skip escaped char
            end += 1;
        }
        let val = s[..end].replace("\\\"", "\"").replace("\\n", "\n").replace("\\\\", "\\");
        Some((JsonVal::Str(val), &s[end + 1..]))
    }

    fn parse_number(s: &str) -> Option<(JsonVal, &str)> {
        let mut end = 0;
        let bytes = s.as_bytes();
        while end < bytes.len() && (bytes[end].is_ascii_digit() || bytes[end] == b'.' || bytes[end] == b'-' || bytes[end] == b'+' || bytes[end] == b'e' || bytes[end] == b'E') {
            end += 1;
        }
        let n: f64 = s[..end].parse().ok()?;
        Some((JsonVal::Num(n), &s[end..]))
    }

    fn parse_object(s: &str) -> Option<(JsonVal, &str)> {
        let mut s = skip_ws(&s[1..]); // skip {
        let mut fields = HashMap::new();
        loop {
            s = skip_ws(s);
            if s.starts_with('}') { return Some((JsonVal::Obj(JsonObj { fields }), &s[1..])); }
            if s.starts_with(',') { s = skip_ws(&s[1..]); }
            // Parse key
            let (key_val, rest) = parse_string(s)?;
            let key = match key_val { JsonVal::Str(k) => k, _ => return None };
            s = skip_ws(rest);
            if !s.starts_with(':') { return None; }
            s = skip_ws(&s[1..]);
            let (val, rest) = parse_value(s)?;
            fields.insert(key, val);
            s = rest;
        }
    }

    fn parse_array(s: &str) -> Option<(JsonVal, &str)> {
        let mut s = skip_ws(&s[1..]); // skip [
        let mut arr = Vec::new();
        loop {
            s = skip_ws(s);
            if s.starts_with(']') { return Some((JsonVal::Arr(arr), &s[1..])); }
            if s.starts_with(',') { s = skip_ws(&s[1..]); }
            let (val, rest) = parse_value(s)?;
            arr.push(val);
            s = rest;
        }
    }

    fn skip_ws(s: &str) -> &str { s.trim_start() }
}
