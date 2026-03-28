//! Bytecode compiler + VM for #eval.
//!
//! Compiles Expr → bytecode, then executes on a stack machine.
//! Much faster than tree-walking: no Arc cloning, no pattern matching per step.

use std::collections::HashMap;

use crate::env::*;
use crate::expr::*;
use crate::name::Name;
use crate::level::Level;
use crate::debruijn::*;

// ============================================================================
// Bytecode
// ============================================================================

#[derive(Clone, Debug)]
pub enum Op {
    /// Push literal Nat
    PushNat(u64),
    /// Push literal String
    PushStr(String),
    /// Push Bool
    PushBool(bool),
    /// Push unit ()
    PushUnit,
    /// Push constructor: (tag, nfields) — pops nfields values, pushes ctor
    MkCtor(u16, u16),
    /// Push closure: (code_addr, num_captures) — captures from stack
    MkClosure(usize, u16),
    /// Load local variable (de Bruijn index from stack top)
    Load(u16),
    /// Apply closure on stack top to argument below it
    Apply,
    /// Tail-call: apply without growing the stack
    TailApply,
    /// Project field i from constructor on stack top
    Proj(u16),
    /// Branch on Nat: if 0 goto addr_zero, else decrement and goto addr_succ
    NatCase(usize, usize),
    /// Branch on Bool: if false goto addr_f, if true goto addr_t
    BoolCase(usize, usize),
    /// Branch on constructor tag: Vec<(tag, addr)>
    CtorCase(Vec<(u16, usize)>),
    /// Jump unconditionally
    Jump(usize),
    /// Return top of stack
    Ret,
    /// Pop n values
    Pop(u16),
    /// Duplicate stack top
    Dup,
    // Built-in arithmetic (fast path, no closure overhead)
    NatAdd,
    NatSub,
    NatMul,
    NatDiv,
    NatMod,
    NatBeq,
    NatBle,
    NatBlt,
    NatSucc,
    // String ops
    StrAppend,
    StrLength,
    StrEq,
    // IO ops
    IoPure,
    IoBind,
    IoPrintln,
    IoGetLine,
    // Conversion
    NatToString,
    BoolToString,
    /// Unreachable / sorry
    Panic(String),
}

// ============================================================================
// Compiled function
// ============================================================================

#[derive(Clone, Debug)]
pub struct CompiledFn {
    pub name: Name,
    pub arity: u16,
    pub code: Vec<Op>,
}

// ============================================================================
// VM Value
// ============================================================================

#[derive(Clone, Debug)]
pub enum Value {
    Nat(u64),
    Str(String),
    Bool(bool),
    Unit,
    /// Constructor: (type_name, ctor_tag, fields)
    Ctor(Name, u16, Vec<Value>),
    /// Closure: (fn_code, captured_env)
    Closure(usize, Vec<Value>),
    /// IO action (thunked)
    IoAction(Box<IoAction>),
}

#[derive(Clone, Debug)]
pub enum IoAction {
    Pure(Value),
    Bind(Value, Value),  // (action, continuation)
    Println(String),
    GetLine,
}

impl Value {
    pub fn to_display_string(&self) -> String {
        match self {
            Value::Nat(n) => n.to_string(),
            Value::Str(s) => format!("\"{}\"", s),
            Value::Bool(true) => "true".to_string(),
            Value::Bool(false) => "false".to_string(),
            Value::Unit => "()".to_string(),
            Value::Ctor(name, tag, fields) => {
                if fields.is_empty() {
                    format!("{}.{}", name, tag)
                } else {
                    let fs: Vec<String> = fields.iter().map(|f| f.to_display_string()).collect();
                    format!("({}.{} {})", name, tag, fs.join(" "))
                }
            }
            Value::Closure(_, _) => "<closure>".to_string(),
            Value::IoAction(_) => "<io>".to_string(),
        }
    }
}

// ============================================================================
// Compiler: Expr → bytecode
// ============================================================================

pub struct Compiler {
    env: Environment,
    fns: HashMap<String, CompiledFn>,
    code: Vec<Op>,
}

impl Compiler {
    pub fn new(env: Environment) -> Self {
        Compiler { env, fns: HashMap::new(), code: Vec::new() }
    }

    pub fn compile_expr(&mut self, e: &Expr) -> Vec<Op> {
        self.code.clear();
        self.compile(e, &mut Vec::new());
        self.code.push(Op::Ret);
        self.code.clone()
    }

    fn compile(&mut self, e: &Expr, locals: &mut Vec<Name>) {
        match e.kind() {
            ExprKind::Lit => {
                match e.lit_value() {
                    Literal::Nat(n) => self.code.push(Op::PushNat(*n)),
                    Literal::Str(s) => self.code.push(Op::PushStr(s.clone())),
                }
            }
            ExprKind::Const => {
                let name = e.const_name();
                // Check for built-in constants
                match name.to_string().as_str() {
                    "Nat.zero" => self.code.push(Op::PushNat(0)),
                    "Bool.true" => self.code.push(Op::PushBool(true)),
                    "Bool.false" => self.code.push(Op::PushBool(false)),
                    "True.intro" | "Unit.unit" => self.code.push(Op::PushUnit),
                    _ => {
                        // Try to inline the definition value
                        if let Some(info) = self.env.find(name) {
                            if let Some(val) = info.get_value() {
                                let val = val.clone();
                                self.compile(&val, locals);
                                return;
                            }
                        }
                        // Unknown constant — push as constructor with 0 fields
                        self.code.push(Op::PushUnit);
                    }
                }
            }
            ExprKind::BVar => {
                let idx = e.bvar_idx() as u16;
                self.code.push(Op::Load(idx));
            }
            ExprKind::App => {
                // Check for built-in binary ops
                let fn_head = e.get_app_fn();
                let args = e.get_app_args();
                if fn_head.is_const() {
                    let fname = fn_head.const_name().to_string();
                    if let Some(op) = self.builtin_binop(&fname, &args) {
                        return;
                    }
                    // Nat.succ special case
                    if fname == "Nat.succ" && args.len() == 1 {
                        self.compile(&args[0], locals);
                        self.code.push(Op::NatSucc);
                        return;
                    }
                }
                // General application: compile fn, compile arg, apply
                self.compile(e.app_fn(), locals);
                self.compile(e.app_arg(), locals);
                self.code.push(Op::Apply);
            }
            ExprKind::Lambda => {
                // Compile body as a closure
                let body_start = self.code.len();
                // Placeholder — will be patched
                self.code.push(Op::Jump(0)); // skip over closure body
                let body_addr = self.code.len();
                locals.push(e.binding_name().clone());
                self.compile(e.binding_body(), locals);
                locals.pop();
                self.code.push(Op::Ret);
                // Patch the jump
                let after_body = self.code.len();
                self.code[body_start] = Op::Jump(after_body);
                // Create closure
                let num_captures = locals.len() as u16;
                self.code.push(Op::MkClosure(body_addr, num_captures));
            }
            ExprKind::Let => {
                // Compile value, then body with it on stack
                self.compile(e.let_value(), locals);
                locals.push(e.let_name().clone());
                self.compile(e.let_body(), locals);
                locals.pop();
            }
            ExprKind::MData => self.compile(e.mdata_expr(), locals),
            ExprKind::Proj => {
                self.compile(e.proj_expr(), locals);
                self.code.push(Op::Proj(e.proj_idx() as u16));
            }
            _ => {
                // Sort, Pi, FVar, MVar — shouldn't appear in evaluated terms
                self.code.push(Op::PushUnit);
            }
        }
    }

    fn builtin_binop(&mut self, fname: &str, args: &[Expr]) -> Option<()> {
        // HAdd.hAdd and friends have 6 args: 3 types + inst + 2 values
        // Nat.add has 2 args
        let (op, a, b) = match fname {
            "Nat.add" if args.len() == 2 => (Op::NatAdd, &args[0], &args[1]),
            "Nat.sub" if args.len() == 2 => (Op::NatSub, &args[0], &args[1]),
            "Nat.mul" if args.len() == 2 => (Op::NatMul, &args[0], &args[1]),
            "Nat.div" if args.len() == 2 => (Op::NatDiv, &args[0], &args[1]),
            "Nat.mod" if args.len() == 2 => (Op::NatMod, &args[0], &args[1]),
            "Nat.beq" if args.len() == 2 => (Op::NatBeq, &args[0], &args[1]),
            "Nat.ble" if args.len() == 2 => (Op::NatBle, &args[0], &args[1]),
            "Nat.blt" if args.len() == 2 => (Op::NatBlt, &args[0], &args[1]),
            "String.append" if args.len() == 2 => (Op::StrAppend, &args[0], &args[1]),
            "String.length" if args.len() == 1 => {
                self.compile(&args[0], &mut Vec::new());
                self.code.push(Op::StrLength);
                return Some(());
            }
            "Nat.repr" | "toString" if args.len() >= 1 => {
                self.compile(args.last().unwrap(), &mut Vec::new());
                self.code.push(Op::NatToString);
                return Some(());
            }
            "HAdd.hAdd" if args.len() == 6 => (Op::NatAdd, &args[4], &args[5]),
            "HSub.hSub" if args.len() == 6 => (Op::NatSub, &args[4], &args[5]),
            "HMul.hMul" if args.len() == 6 => (Op::NatMul, &args[4], &args[5]),
            "HDiv.hDiv" if args.len() == 6 => (Op::NatDiv, &args[4], &args[5]),
            "HMod.hMod" if args.len() == 6 => (Op::NatMod, &args[4], &args[5]),
            "BEq.beq" if args.len() >= 2 => (Op::NatBeq, &args[args.len()-2], &args[args.len()-1]),
            _ => return None,
        };
        let mut locals = Vec::new();
        self.compile(a, &mut locals);
        self.compile(b, &mut locals);
        self.code.push(op);
        Some(())
    }
}

// ============================================================================
// VM: execute bytecode
// ============================================================================

pub struct VM {
    stack: Vec<Value>,
    call_stack: Vec<(usize, usize)>, // (return_addr, stack_base)
}

impl VM {
    pub fn new() -> Self {
        VM { stack: Vec::with_capacity(1024), call_stack: Vec::new() }
    }

    pub fn execute(&mut self, code: &[Op]) -> Result<Value, String> {
        let mut pc = 0usize;
        let mut fuel = 10_000_000u64; // prevent infinite loops

        while pc < code.len() && fuel > 0 {
            fuel -= 1;
            match &code[pc] {
                Op::PushNat(n) => { self.stack.push(Value::Nat(*n)); pc += 1; }
                Op::PushStr(s) => { self.stack.push(Value::Str(s.clone())); pc += 1; }
                Op::PushBool(b) => { self.stack.push(Value::Bool(*b)); pc += 1; }
                Op::PushUnit => { self.stack.push(Value::Unit); pc += 1; }
                Op::MkCtor(tag, nfields) => {
                    let n = *nfields as usize;
                    let start = self.stack.len() - n;
                    let fields: Vec<Value> = self.stack.drain(start..).collect();
                    self.stack.push(Value::Ctor(Name::anonymous(), *tag, fields));
                    pc += 1;
                }
                Op::MkClosure(addr, ncap) => {
                    let n = *ncap as usize;
                    let captured = if n > 0 && self.stack.len() >= n {
                        self.stack[self.stack.len()-n..].to_vec()
                    } else { Vec::new() };
                    self.stack.push(Value::Closure(*addr, captured));
                    pc += 1;
                }
                Op::Load(idx) => {
                    let i = self.stack.len() - 1 - *idx as usize;
                    let v = self.stack[i].clone();
                    self.stack.push(v);
                    pc += 1;
                }
                Op::Apply => {
                    let arg = self.stack.pop().ok_or("stack underflow")?;
                    let func = self.stack.pop().ok_or("stack underflow")?;
                    match func {
                        Value::Closure(addr, mut env) => {
                            env.push(arg);
                            // Push return info
                            self.call_stack.push((pc + 1, self.stack.len()));
                            // Set up new frame
                            self.stack.extend(env);
                            pc = addr;
                        }
                        _ => {
                            // Not a closure — just push the result
                            self.stack.push(func);
                            pc += 1;
                        }
                    }
                }
                Op::TailApply => {
                    let arg = self.stack.pop().ok_or("stack underflow")?;
                    let func = self.stack.pop().ok_or("stack underflow")?;
                    match func {
                        Value::Closure(addr, mut env) => {
                            env.push(arg);
                            // Reuse current frame
                            if let Some(&(_, base)) = self.call_stack.last() {
                                self.stack.truncate(base);
                            }
                            self.stack.extend(env);
                            pc = addr;
                        }
                        _ => { self.stack.push(func); pc += 1; }
                    }
                }
                Op::Proj(i) => {
                    let v = self.stack.pop().ok_or("stack underflow")?;
                    match v {
                        Value::Ctor(_, _, fields) => {
                            let idx = *i as usize;
                            if idx < fields.len() {
                                self.stack.push(fields[idx].clone());
                            } else {
                                self.stack.push(Value::Unit);
                            }
                        }
                        _ => self.stack.push(Value::Unit),
                    }
                    pc += 1;
                }
                Op::Jump(addr) => { pc = *addr; }
                Op::Ret => {
                    if let Some((ret_addr, base)) = self.call_stack.pop() {
                        let result = self.stack.pop().unwrap_or(Value::Unit);
                        self.stack.truncate(base);
                        self.stack.push(result);
                        pc = ret_addr;
                    } else {
                        break; // top-level return
                    }
                }
                Op::Pop(n) => {
                    let new_len = self.stack.len().saturating_sub(*n as usize);
                    self.stack.truncate(new_len);
                    pc += 1;
                }
                Op::Dup => {
                    let v = self.stack.last().cloned().unwrap_or(Value::Unit);
                    self.stack.push(v);
                    pc += 1;
                }
                // Arithmetic
                Op::NatAdd => { nat_binop(&mut self.stack, |a, b| a.wrapping_add(b)); pc += 1; }
                Op::NatSub => { nat_binop(&mut self.stack, |a, b| a.saturating_sub(b)); pc += 1; }
                Op::NatMul => { nat_binop(&mut self.stack, |a, b| a.wrapping_mul(b)); pc += 1; }
                Op::NatDiv => { nat_binop(&mut self.stack, |a, b| if b == 0 { 0 } else { a / b }); pc += 1; }
                Op::NatMod => { nat_binop(&mut self.stack, |a, b| if b == 0 { 0 } else { a % b }); pc += 1; }
                Op::NatBeq => { nat_cmp(&mut self.stack, |a, b| a == b); pc += 1; }
                Op::NatBle => { nat_cmp(&mut self.stack, |a, b| a <= b); pc += 1; }
                Op::NatBlt => { nat_cmp(&mut self.stack, |a, b| a < b); pc += 1; }
                Op::NatSucc => {
                    if let Some(Value::Nat(n)) = self.stack.pop() {
                        self.stack.push(Value::Nat(n + 1));
                    } else { self.stack.push(Value::Nat(1)); }
                    pc += 1;
                }
                Op::StrAppend => {
                    let b = self.stack.pop().unwrap_or(Value::Str(String::new()));
                    let a = self.stack.pop().unwrap_or(Value::Str(String::new()));
                    match (a, b) {
                        (Value::Str(a), Value::Str(b)) => self.stack.push(Value::Str(a + &b)),
                        _ => self.stack.push(Value::Str(String::new())),
                    }
                    pc += 1;
                }
                Op::StrLength => {
                    if let Some(Value::Str(s)) = self.stack.pop() {
                        self.stack.push(Value::Nat(s.len() as u64));
                    } else { self.stack.push(Value::Nat(0)); }
                    pc += 1;
                }
                Op::StrEq => {
                    let b = self.stack.pop().unwrap_or(Value::Str(String::new()));
                    let a = self.stack.pop().unwrap_or(Value::Str(String::new()));
                    match (a, b) {
                        (Value::Str(a), Value::Str(b)) => self.stack.push(Value::Bool(a == b)),
                        _ => self.stack.push(Value::Bool(false)),
                    }
                    pc += 1;
                }
                Op::NatToString => {
                    if let Some(Value::Nat(n)) = self.stack.pop() {
                        self.stack.push(Value::Str(n.to_string()));
                    } else { self.stack.push(Value::Str("?".into())); }
                    pc += 1;
                }
                Op::BoolToString => {
                    if let Some(Value::Bool(b)) = self.stack.pop() {
                        self.stack.push(Value::Str(if b { "true" } else { "false" }.into()));
                    } else { self.stack.push(Value::Str("?".into())); }
                    pc += 1;
                }
                Op::IoPure => {
                    let v = self.stack.pop().unwrap_or(Value::Unit);
                    self.stack.push(Value::IoAction(Box::new(IoAction::Pure(v))));
                    pc += 1;
                }
                Op::IoBind => {
                    let k = self.stack.pop().unwrap_or(Value::Unit);
                    let a = self.stack.pop().unwrap_or(Value::Unit);
                    self.stack.push(Value::IoAction(Box::new(IoAction::Bind(a, k))));
                    pc += 1;
                }
                Op::IoPrintln => {
                    let s = self.stack.pop().unwrap_or(Value::Str(String::new()));
                    match s {
                        Value::Str(s) => self.stack.push(Value::IoAction(Box::new(IoAction::Println(s)))),
                        v => self.stack.push(Value::IoAction(Box::new(IoAction::Println(v.to_display_string())))),
                    }
                    pc += 1;
                }
                Op::IoGetLine => {
                    self.stack.push(Value::IoAction(Box::new(IoAction::GetLine)));
                    pc += 1;
                }
                Op::NatCase(z_addr, s_addr) => {
                    let v = self.stack.pop().unwrap_or(Value::Nat(0));
                    match v {
                        Value::Nat(0) => pc = *z_addr,
                        Value::Nat(n) => { self.stack.push(Value::Nat(n - 1)); pc = *s_addr; }
                        _ => pc = *z_addr,
                    }
                }
                Op::BoolCase(f_addr, t_addr) => {
                    let v = self.stack.pop().unwrap_or(Value::Bool(false));
                    match v {
                        Value::Bool(false) => pc = *f_addr,
                        Value::Bool(true) => pc = *t_addr,
                        _ => pc = *f_addr,
                    }
                }
                Op::CtorCase(branches) => {
                    let v = self.stack.pop().unwrap_or(Value::Unit);
                    if let Value::Ctor(_, tag, fields) = v {
                        // Push fields onto stack
                        for f in fields { self.stack.push(f); }
                        if let Some(&(_, addr)) = branches.iter().find(|(t, _)| *t == tag) {
                            pc = addr;
                        } else { pc += 1; }
                    } else { pc += 1; }
                }
                Op::Panic(msg) => return Err(format!("panic: {}", msg)),
            }
        }
        if fuel == 0 { return Err("evaluation timeout (10M steps)".into()); }
        self.stack.pop().ok_or_else(|| "empty stack".into())
    }
}

fn nat_binop(stack: &mut Vec<Value>, f: impl Fn(u64, u64) -> u64) {
    let b = match stack.pop() { Some(Value::Nat(n)) => n, _ => 0 };
    let a = match stack.pop() { Some(Value::Nat(n)) => n, _ => 0 };
    stack.push(Value::Nat(f(a, b)));
}

fn nat_cmp(stack: &mut Vec<Value>, f: impl Fn(u64, u64) -> bool) {
    let b = match stack.pop() { Some(Value::Nat(n)) => n, _ => 0 };
    let a = match stack.pop() { Some(Value::Nat(n)) => n, _ => 0 };
    stack.push(Value::Bool(f(a, b)));
}

// ============================================================================
// Run IO actions
// ============================================================================

pub fn run_io(action: &Value) -> Result<Value, String> {
    match action {
        Value::IoAction(a) => match a.as_ref() {
            IoAction::Pure(v) => Ok(v.clone()),
            IoAction::Println(s) => { println!("{}", s); Ok(Value::Unit) }
            IoAction::GetLine => {
                let mut line = String::new();
                std::io::stdin().read_line(&mut line).map_err(|e| e.to_string())?;
                Ok(Value::Str(line.trim_end().to_string()))
            }
            IoAction::Bind(act, k) => {
                let v = run_io(act)?;
                // Apply continuation to result
                // For now, just return the action result
                Ok(v)
            }
        },
        v => Ok(v.clone()),
    }
}

// ============================================================================
// Top-level eval
// ============================================================================

/// Evaluate an expression and return a displayable string.
pub fn eval_expr(e: &Expr, env: &Environment) -> Result<String, String> {
    let mut compiler = Compiler::new(env.clone());
    let code = compiler.compile_expr(e);
    let mut vm = VM::new();
    let result = vm.execute(&code)?;

    // If IO action, execute it
    match &result {
        Value::IoAction(_) => {
            let io_result = run_io(&result)?;
            Ok(io_result.to_display_string())
        }
        _ => Ok(result.to_display_string()),
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn eval(s: &str, env: &Environment) -> String {
        let (_, _, cmds) = crate::parser::parse_file(&format!("def _eval := {}", s));
        let mut elab = crate::elaborator::Elaborator::new(env.clone());
        for cmd in &cmds { let _ = elab.elab_command(cmd); }
        if let Some(ci) = elab.env.find(&Name::str("_eval")) {
            if let Some(val) = ci.get_value() {
                eval_expr(val, &elab.env).unwrap_or_else(|e| format!("error: {}", e))
            } else { "no value".into() }
        } else { "elab failed".into() }
    }

    fn get_init() -> Environment {
        let sp = vec![std::path::PathBuf::from(
            format!("{}/.elan/toolchains/leanprover--lean4---v4.25.2/lib/lean",
                std::env::var("HOME").unwrap_or_default()))];
        crate::olean_fast::load_module_tree_fast(&Name::str("Init"), &sp).unwrap().env
    }

    #[test]
    fn test_eval_nat_lit() {
        let env = get_init();
        assert_eq!(eval("42", &env), "42");
    }

    #[test]
    fn test_eval_nat_add() {
        let env = get_init();
        assert_eq!(eval("Nat.add 2 3", &env), "5");
    }

    #[test]
    fn test_eval_nat_mul() {
        let env = get_init();
        assert_eq!(eval("Nat.mul 6 7", &env), "42");
    }

    #[test]
    fn test_eval_nat_succ() {
        let env = get_init();
        assert_eq!(eval("Nat.succ 0", &env), "1");
    }

    #[test]
    fn test_eval_string() {
        let env = get_init();
        assert_eq!(eval("\"hello\"", &env), "\"hello\"");
    }

    #[test]
    fn test_eval_bool() {
        let env = get_init();
        assert_eq!(eval("Bool.true", &env), "true");
        assert_eq!(eval("Bool.false", &env), "false");
    }

    #[test]
    fn test_eval_string_length() {
        let env = get_init();
        assert_eq!(eval("String.length \"hello\"", &env), "5");
    }
}
