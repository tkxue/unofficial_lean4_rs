//! Write lean4export NDJSON format from our Environment.
//! This lets us generate test cases for the Lean Kernel Arena.

use std::collections::HashMap;
use std::io::Write;

use crate::env::*;
use crate::expr::*;
use crate::level::Level;
use crate::name::Name;

pub struct NdjsonWriter<W: Write> {
    out: W,
    name_ids: HashMap<String, u64>,
    level_ids: HashMap<u64, u64>,  // level hash → id
    expr_ids: HashMap<u32, u64>,   // expr hash → id
    next_name_id: u64,
    next_level_id: u64,
    next_expr_id: u64,
}

impl<W: Write> NdjsonWriter<W> {
    pub fn new(out: W) -> Self {
        NdjsonWriter {
            out,
            name_ids: HashMap::new(),
            level_ids: HashMap::new(),
            expr_ids: HashMap::new(),
            next_name_id: 1, // 0 = anonymous
            next_level_id: 1, // 0 = zero
            next_expr_id: 0,
        }
    }

    pub fn write_header(&mut self) -> std::io::Result<()> {
        writeln!(self.out, r#"{{"meta":{{"exporter":{{"name":"rust-lean4","version":"0.1.0"}},"format":{{"version":"3.1.0"}},"lean":{{"version":"4.25.2"}}}}}}"#)
    }

    pub fn write_name(&mut self, name: &Name) -> std::io::Result<u64> {
        if name.is_anonymous() { return Ok(0); }
        let key = name.to_string();
        if let Some(&id) = self.name_ids.get(&key) { return Ok(id); }
        let prefix_id = self.write_name(name.get_prefix())?;
        let id = self.next_name_id;
        self.next_name_id += 1;
        if name.is_string() {
            let s = name.get_string();
            writeln!(self.out, r#"{{"in":{},"str":{{"pre":{},"str":"{}"}}}}"#, id, prefix_id, escape_json(s))?;
        } else {
            let n = name.get_numeral();
            writeln!(self.out, r#"{{"in":{},"num":{{"pre":{},"num":{}}}}}"#, id, prefix_id, n)?;
        }
        self.name_ids.insert(key, id);
        Ok(id)
    }

    pub fn write_level(&mut self, level: &Level) -> std::io::Result<u64> {
        if level.is_zero() { return Ok(0); }
        let h = level.hash();
        if let Some(&id) = self.level_ids.get(&h) { return Ok(id); }
        let id = self.next_level_id;
        self.next_level_id += 1;
        match level.kind() {
            crate::level::LevelKind::Succ => {
                let inner = self.write_level(level.succ_of())?;
                writeln!(self.out, r#"{{"il":{},"succ":{}}}"#, id, inner)?;
            }
            crate::level::LevelKind::Max => {
                let l = self.write_level(level.max_lhs())?;
                let r = self.write_level(level.max_rhs())?;
                writeln!(self.out, r#"{{"il":{},"max":[{},{}]}}"#, id, l, r)?;
            }
            crate::level::LevelKind::IMax => {
                let l = self.write_level(level.max_lhs())?;
                let r = self.write_level(level.max_rhs())?;
                writeln!(self.out, r#"{{"il":{},"imax":[{},{}]}}"#, id, l, r)?;
            }
            crate::level::LevelKind::Param => {
                let n = self.write_name(level.param_name())?;
                writeln!(self.out, r#"{{"il":{},"param":{}}}"#, id, n)?;
            }
            crate::level::LevelKind::MVar => {
                let n = self.write_name(level.param_name())?;
                writeln!(self.out, r#"{{"il":{},"mvar":{}}}"#, id, n)?;
            }
            _ => { writeln!(self.out, r#"{{"il":{},"succ":0}}"#, id)?; }
        }
        self.level_ids.insert(h, id);
        Ok(id)
    }

    pub fn write_expr(&mut self, expr: &Expr) -> std::io::Result<u64> {
        let h = expr.hash();
        if let Some(&id) = self.expr_ids.get(&h) { return Ok(id); }
        let id = self.next_expr_id;
        self.next_expr_id += 1;
        match expr.kind() {
            ExprKind::BVar => {
                writeln!(self.out, r#"{{"ie":{},"bvar":{}}}"#, id, expr.bvar_idx())?;
            }
            ExprKind::Sort => {
                let l = self.write_level(expr.sort_level())?;
                writeln!(self.out, r#"{{"ie":{},"sort":{}}}"#, id, l)?;
            }
            ExprKind::Const => {
                let n = self.write_name(expr.const_name())?;
                let us: Vec<u64> = expr.const_levels().iter()
                    .map(|l| self.write_level(l).unwrap_or(0))
                    .collect();
                let us_str = format!("[{}]", us.iter().map(|u| u.to_string()).collect::<Vec<_>>().join(","));
                writeln!(self.out, r#"{{"ie":{},"const":{{"name":{},"us":{}}}}}"#, id, n, us_str)?;
            }
            ExprKind::App => {
                let f = self.write_expr(expr.app_fn())?;
                let a = self.write_expr(expr.app_arg())?;
                writeln!(self.out, r#"{{"ie":{},"app":{{"fn":{},"arg":{}}}}}"#, id, f, a)?;
            }
            ExprKind::Lambda => {
                let n = self.write_name(expr.binding_name())?;
                let t = self.write_expr(expr.binding_domain())?;
                let b = self.write_expr(expr.binding_body())?;
                let bi = bi_str(expr.binding_info());
                writeln!(self.out, r#"{{"ie":{},"lam":{{"name":{},"type":{},"body":{},"binderInfo":"{}"}}}}"#, id, n, t, b, bi)?;
            }
            ExprKind::Pi => {
                let n = self.write_name(expr.binding_name())?;
                let t = self.write_expr(expr.binding_domain())?;
                let b = self.write_expr(expr.binding_body())?;
                let bi = bi_str(expr.binding_info());
                writeln!(self.out, r#"{{"ie":{},"forallE":{{"name":{},"type":{},"body":{},"binderInfo":"{}"}}}}"#, id, n, t, b, bi)?;
            }
            ExprKind::Let => {
                let n = self.write_name(expr.let_name())?;
                let t = self.write_expr(expr.let_type())?;
                let v = self.write_expr(expr.let_value())?;
                let b = self.write_expr(expr.let_body())?;
                writeln!(self.out, r#"{{"ie":{},"letE":{{"name":{},"type":{},"value":{},"body":{}}}}}"#, id, n, t, v, b)?;
            }
            ExprKind::Lit => {
                match expr.lit_value() {
                    Literal::Nat(n) => writeln!(self.out, r#"{{"ie":{},"lit":{{"natVal":{}}}}}"#, id, n)?,
                    Literal::Str(s) => writeln!(self.out, r#"{{"ie":{},"lit":{{"strVal":"{}"}}}}"#, id, escape_json(s))?,
                }
            }
            ExprKind::Proj => {
                let n = self.write_name(expr.proj_sname())?;
                let e = self.write_expr(expr.proj_expr())?;
                writeln!(self.out, r#"{{"ie":{},"proj":{{"typeName":{},"idx":{},"expr":{}}}}}"#, id, n, expr.proj_idx(), e)?;
            }
            _ => {
                writeln!(self.out, r#"{{"ie":{},"bvar":0}}"#, id)?;
            }
        }
        self.expr_ids.insert(h, id);
        Ok(id)
    }

    pub fn write_constant(&mut self, ci: &ConstantInfo) -> std::io::Result<()> {
        let name_id = self.write_name(&ci.name)?;
        let type_id = self.write_expr(&ci.type_)?;
        let lparams: Vec<u64> = ci.lparams.iter()
            .map(|n| self.write_name(n).unwrap_or(0))
            .collect();
        let lp_str = format!("[{}]", lparams.iter().map(|u| u.to_string()).collect::<Vec<_>>().join(","));

        match &ci.kind {
            ConstantInfoKind::Axiom { is_unsafe } => {
                writeln!(self.out, r#"{{"axiom":{{"name":{},"levelParams":{},"type":{},"isUnsafe":{}}}}}"#,
                    name_id, lp_str, type_id, is_unsafe)?;
            }
            ConstantInfoKind::Definition { value, hints, safety } => {
                let val_id = self.write_expr(value)?;
                let safety_str = match safety {
                    DefinitionSafety::Unsafe => "unsafe",
                    DefinitionSafety::Partial => "partial",
                    DefinitionSafety::Safe => "safe",
                };
                writeln!(self.out, r#"{{"def":{{"name":{},"levelParams":{},"type":{},"value":{},"safety":"{}"}}}}"#,
                    name_id, lp_str, type_id, val_id, safety_str)?;
            }
            ConstantInfoKind::Theorem { value } => {
                let val_id = self.write_expr(value)?;
                writeln!(self.out, r#"{{"theorem":{{"name":{},"levelParams":{},"type":{},"value":{}}}}}"#,
                    name_id, lp_str, type_id, val_id)?;
            }
            ConstantInfoKind::Opaque { value, is_unsafe } => {
                let val_id = self.write_expr(value)?;
                writeln!(self.out, r#"{{"opaque":{{"name":{},"levelParams":{},"type":{},"value":{},"isUnsafe":{}}}}}"#,
                    name_id, lp_str, type_id, val_id, is_unsafe)?;
            }
            ConstantInfoKind::Quot { kind } => {
                writeln!(self.out, r#"{{"quot":{{}}}}"#)?;
            }
            ConstantInfoKind::Inductive { nparams, nindices, all, ctors, nnested, is_rec, is_unsafe, is_reflexive } => {
                // Simplified inductive export
                let all_ids: Vec<u64> = all.iter().map(|n| self.write_name(n).unwrap_or(0)).collect();
                let ctor_ids: Vec<u64> = ctors.iter().map(|n| self.write_name(n).unwrap_or(0)).collect();
                writeln!(self.out, r#"{{"inductive":{{"types":[{{"name":{},"levelParams":{},"type":{},"numParams":{},"numIndices":{},"all":[{}],"ctors":[{}],"numNested":{},"isRec":{},"isUnsafe":{},"isReflexive":{}}}]}}}}"#,
                    name_id, lp_str, type_id, nparams, nindices,
                    all_ids.iter().map(|u| u.to_string()).collect::<Vec<_>>().join(","),
                    ctor_ids.iter().map(|u| u.to_string()).collect::<Vec<_>>().join(","),
                    nnested, is_rec, is_unsafe, is_reflexive)?;
            }
            _ => {} // Constructor and Recursor are part of Inductive
        }
        Ok(())
    }

    pub fn write_environment(&mut self, env: &Environment) -> std::io::Result<()> {
        self.write_header()?;
        env.for_each_constant(|_, ci| {
            let _ = self.write_constant(ci);
        });
        Ok(())
    }
}

fn bi_str(bi: BinderInfo) -> &'static str {
    match bi {
        BinderInfo::Default => "default",
        BinderInfo::Implicit => "implicit",
        BinderInfo::StrictImplicit => "strictImplicit",
        BinderInfo::InstImplicit => "instImplicit",
    }
}

fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n").replace('\r', "\\r")
}
