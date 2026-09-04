// Builtin std.* dispatch, centralized across the three pipeline stages so that
// each stage no longer hard-codes the internal std.* name strings.
//
// Stage interfaces:
//   - Checker:   stdlib::StdOp::of(name) + stdlib::check_call(...)
//   - IR:        stdlib::is_log(...) + stdlib::StdOp::of(name).ir_type()
//   - Codegen:   stdlib::StdOp::of(name) + stdlib::emit_std_call(...)

use std::collections::HashMap;

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{FuncRef, Function, GlobalValue, InstBuilder, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::{DataId, FuncId};

use crate::checker::FnSig;
use crate::ir::{IrType, Ty};
use crate::Expr;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StdOp {
    Log,
    In,
    ParseNumber,
    ToCString,
    FromCString,
    FuncPtr,
    StrLen,
    CharAt,
    NetSockaddrIn,
    NetSocket,
    NetBind,
    NetListen,
    NetAccept,
    NetRecv,
    NetSend,
    NetClose,
    ProcFork,
    ProcExec1,
    ProcExec2,
    ProcPipe,
    ProcPipeRead,
    ProcPipeWrite,
    ProcWait,
    ProcExit,
}

impl StdOp {
    pub fn of(name: &str) -> Option<StdOp> {
        match name {
            "std.log" => Some(StdOp::Log),
            "std.in" => Some(StdOp::In),
            "std.parseNumber" => Some(StdOp::ParseNumber),
            "std.toCString" => Some(StdOp::ToCString),
            "std.fromCString" => Some(StdOp::FromCString),
            "std.funcPtr" => Some(StdOp::FuncPtr),
            "std.strlen" => Some(StdOp::StrLen),
            "std.charAt" => Some(StdOp::CharAt),
            "std.net.sockaddrIn" => Some(StdOp::NetSockaddrIn),
            "std.net.socket" => Some(StdOp::NetSocket),
            "std.net.bind" => Some(StdOp::NetBind),
            "std.net.listen" => Some(StdOp::NetListen),
            "std.net.accept" => Some(StdOp::NetAccept),
            "std.net.recv" => Some(StdOp::NetRecv),
            "std.net.send" => Some(StdOp::NetSend),
            "std.net.close" => Some(StdOp::NetClose),
            "std.process.fork" => Some(StdOp::ProcFork),
            "std.process.exec1" => Some(StdOp::ProcExec1),
            "std.process.exec2" => Some(StdOp::ProcExec2),
            "std.process.pipe" => Some(StdOp::ProcPipe),
            "std.process.pipeReadFd" => Some(StdOp::ProcPipeRead),
            "std.process.pipeWriteFd" => Some(StdOp::ProcPipeWrite),
            "std.process.wait" => Some(StdOp::ProcWait),
            "std.process.exit" => Some(StdOp::ProcExit),
            _ => None,
        }
    }

    pub fn ir_type(self) -> IrType {
        match self {
            StdOp::Log => IrType::Void,
            StdOp::In => IrType::String,
            StdOp::ParseNumber => IrType::Number,
            StdOp::ToCString => IrType::Pointer,
            StdOp::FromCString => IrType::String,
            StdOp::FuncPtr => IrType::Pointer,
            StdOp::StrLen => IrType::Number,
            StdOp::CharAt => IrType::String,
            StdOp::NetSockaddrIn => IrType::Pointer,
            StdOp::NetSocket
            | StdOp::NetBind
            | StdOp::NetListen
            | StdOp::NetAccept
            | StdOp::NetRecv
            | StdOp::NetSend
            | StdOp::NetClose => IrType::Number,
            StdOp::ProcPipe => IrType::Pointer,
            StdOp::ProcExit => IrType::Void,
            StdOp::ProcFork
            | StdOp::ProcExec1
            | StdOp::ProcExec2
            | StdOp::ProcPipeRead
            | StdOp::ProcPipeWrite
            | StdOp::ProcWait => IrType::Number,
        }
    }
}

// console.log is normalized to std.log at parse time, but the IR lowering's
// log-instruction detection also accepts the legacy alias, matching the
// original behaviour.
pub fn is_log(name: &str) -> bool {
    name == "console.log" || name == "std.log"
}

// Whether the op validates the types of its argument expressions. Log, In,
// ParseNumber and ToCString type-check their arguments; FuncPtr instead
// resolves a literal function name (and does not type-check the argument),
// matching the original checker ordering.
pub fn checks_argument_types(op: StdOp) -> bool {
    !matches!(op, StdOp::FuncPtr)
}

pub fn check_call(
    op: StdOp,
    n_args: usize,
    arg_types: &[Ty],
    func_ptr_literal: Option<&str>,
    env: &HashMap<String, Ty>,
    fns: &HashMap<String, FnSig>,
) -> Result<Ty, String> {
    match op {
        StdOp::Log => {
            if n_args != 1 {
                return Err("std.log accepts one argument".into());
            }
            let t = arg_types[0];
            if !matches!(t, Ty::Number | Ty::Boolean | Ty::String) {
                return Err(format!("std.log does not accept {t:?} values in the raw ABI"));
            }
            Ok(Ty::Void)
        }
        StdOp::In => {
            if n_args != 0 {
                return Err("std.in accepts no arguments".into());
            }
            Ok(Ty::String)
        }
        StdOp::ParseNumber => {
            if n_args != 1 {
                return Err("std.parseNumber accepts one argument".into());
            }
            let t = arg_types[0];
            if t != Ty::String && t != Ty::Any {
                return Err(format!("std.parseNumber expects a string, got {t:?}"));
            }
            Ok(Ty::Number)
        }
        StdOp::ToCString => {
            if n_args != 1 {
                return Err("std.toCString accepts one argument".into());
            }
            let t = arg_types[0];
            if t != Ty::String && t != Ty::Any {
                return Err(format!("std.toCString expects a string, got {t:?}"));
            }
            Ok(Ty::Pointer)
        }
        StdOp::FromCString => {
            if n_args != 2 {
                return Err("std.fromCString accepts two arguments".into());
            }
            let p = arg_types[0];
            let n = arg_types[1];
            if p != Ty::Pointer && p != Ty::Any {
                return Err(format!("std.fromCString expects a Pointer, got {p:?}"));
            }
            if n != Ty::Number && n != Ty::Any {
                return Err(format!("std.fromCString expects a number length, got {n:?}"));
            }
            Ok(Ty::String)
        }
        StdOp::FuncPtr => {
            if n_args != 1 {
                return Err("std.funcPtr accepts one argument".into());
            }
            let Some(func_name) = func_ptr_literal else {
                return Err("std.funcPtr requires a string literal naming the target function (e.g. std.funcPtr(\"main\"))".into());
            };
            if env.get(func_name) == Some(&Ty::ClosureNumber) {
                return Err(format!(
                    "std.funcPtr cannot take the address of closure/capturing function \"{func_name}\"; closures are not representable as C function pointers"
                ));
            }
            if !fns.contains_key(func_name) {
                return Err(format!("std.funcPtr: unknown function \"{func_name}\""));
            }
            Ok(Ty::Pointer)
        }
        StdOp::StrLen => {
            if n_args != 1 {
                return Err("std.strlen accepts one argument".into());
            }
            let t = arg_types[0];
            if t != Ty::String && t != Ty::Any {
                return Err(format!("std.strlen expects a string, got {t:?}"));
            }
            Ok(Ty::Number)
        }
        StdOp::CharAt => {
            if n_args != 2 {
                return Err("std.charAt accepts two arguments".into());
            }
            let t = arg_types[0];
            let i = arg_types[1];
            if t != Ty::String && t != Ty::Any {
                return Err(format!("std.charAt expects a string, got {t:?}"));
            }
            if i != Ty::Number && i != Ty::Any {
                return Err(format!("std.charAt expects a number index, got {i:?}"));
            }
            Ok(Ty::String)
        }
        StdOp::NetSockaddrIn => {
            if n_args != 2 {
                return Err("std.net.sockaddrIn accepts two arguments".into());
            }
            let port = arg_types[0];
            let addr = arg_types[1];
            if (port != Ty::Number && port != Ty::Any) || (addr != Ty::Number && addr != Ty::Any) {
                return Err("std.net.sockaddrIn expects two number arguments (port, addr)".into());
            }
            Ok(Ty::Pointer)
        }
        StdOp::NetSocket => {
            if n_args != 3 {
                return Err("std.net.socket expects three arguments (domain, type, protocol)".into());
            }
            for t in arg_types {
                if t != &Ty::Number && t != &Ty::Any {
                    return Err(format!("std.net.socket expects number arguments, got {t:?}"));
                }
            }
            Ok(Ty::Number)
        }
        StdOp::NetBind => {
            if n_args != 3 {
                return Err("std.net.bind expects three arguments (fd, addr, len)".into());
            }
            if arg_types[0] != Ty::Number && arg_types[0] != Ty::Any {
                return Err(format!("std.net.bind expects a number fd, got {:?}", arg_types[0]));
            }
            if arg_types[1] != Ty::Pointer && arg_types[1] != Ty::Any {
                return Err(format!("std.net.bind expects a Pointer addr, got {:?}", arg_types[1]));
            }
            if arg_types[2] != Ty::Number && arg_types[2] != Ty::Any {
                return Err(format!("std.net.bind expects a number len, got {:?}", arg_types[2]));
            }
            Ok(Ty::Number)
        }
        StdOp::NetListen => {
            if n_args != 2 {
                return Err("std.net.listen expects two arguments (fd, backlog)".into());
            }
            for t in arg_types {
                if t != &Ty::Number && t != &Ty::Any {
                    return Err(format!("std.net.listen expects number arguments, got {t:?}"));
                }
            }
            Ok(Ty::Number)
        }
        StdOp::NetAccept => {
            if n_args != 1 {
                return Err("std.net.accept expects one argument (fd)".into());
            }
            if arg_types[0] != Ty::Number && arg_types[0] != Ty::Any {
                return Err(format!("std.net.accept expects a number fd, got {:?}", arg_types[0]));
            }
            Ok(Ty::Number)
        }
        StdOp::NetRecv => {
            if n_args != 4 {
                return Err("std.net.recv expects four arguments (fd, buf, n, flags)".into());
            }
            if arg_types[0] != Ty::Number && arg_types[0] != Ty::Any {
                return Err(format!("std.net.recv expects a number fd, got {:?}", arg_types[0]));
            }
            if arg_types[1] != Ty::Pointer && arg_types[1] != Ty::Any {
                return Err(format!("std.net.recv expects a Pointer buf, got {:?}", arg_types[1]));
            }
            for t in &arg_types[2..] {
                if t != &Ty::Number && t != &Ty::Any {
                    return Err(format!("std.net.recv expects number n/flags, got {t:?}"));
                }
            }
            Ok(Ty::Number)
        }
        StdOp::NetSend => {
            if n_args != 4 {
                return Err("std.net.send expects four arguments (fd, buf, n, flags)".into());
            }
            if arg_types[0] != Ty::Number && arg_types[0] != Ty::Any {
                return Err(format!("std.net.send expects a number fd, got {:?}", arg_types[0]));
            }
            if arg_types[1] != Ty::Pointer && arg_types[1] != Ty::Any {
                return Err(format!("std.net.send expects a Pointer buf, got {:?}", arg_types[1]));
            }
            for t in &arg_types[2..] {
                if t != &Ty::Number && t != &Ty::Any {
                    return Err(format!("std.net.send expects number n/flags, got {t:?}"));
                }
            }
            Ok(Ty::Number)
        }
        StdOp::NetClose => {
            if n_args != 1 {
                return Err("std.net.close expects one argument (fd)".into());
            }
            if arg_types[0] != Ty::Number && arg_types[0] != Ty::Any {
                return Err(format!("std.net.close expects a number fd, got {:?}", arg_types[0]));
            }
            Ok(Ty::Number)
        }
        StdOp::ProcFork | StdOp::ProcPipe => {
            if n_args != 0 {
                return Err("std.process.fork/std.process.pipe accept no arguments".into());
            }
            Ok(match op {
                StdOp::ProcPipe => Ty::Pointer,
                _ => Ty::Number,
            })
        }
        StdOp::ProcExec1 => {
            if n_args != 1 {
                return Err("std.process.exec1 accepts one argument (path)".into());
            }
            if arg_types[0] != Ty::String && arg_types[0] != Ty::Any {
                return Err(format!("std.process.exec1 expects a string path, got {:?}", arg_types[0]));
            }
            Ok(Ty::Number)
        }
        StdOp::ProcExec2 => {
            if n_args != 2 {
                return Err("std.process.exec2 accepts two arguments (path, arg1)".into());
            }
            for t in arg_types {
                if t != &Ty::String && t != &Ty::Any {
                    return Err(format!("std.process.exec2 expects string arguments, got {t:?}"));
                }
            }
            Ok(Ty::Number)
        }
        StdOp::ProcPipeRead | StdOp::ProcPipeWrite => {
            if n_args != 1 {
                return Err("pipe fd accessors accept one argument (pipe pointer)".into());
            }
            if arg_types[0] != Ty::Pointer && arg_types[0] != Ty::Any {
                return Err(format!("std.process.pipe*Fd expects a Pointer, got {:?}", arg_types[0]));
            }
            Ok(Ty::Number)
        }
        StdOp::ProcWait => {
            if n_args != 1 {
                return Err("std.process.wait accepts one argument (pid)".into());
            }
            if arg_types[0] != Ty::Number && arg_types[0] != Ty::Any {
                return Err(format!("std.process.wait expects a number pid, got {:?}", arg_types[0]));
            }
            Ok(Ty::Number)
        }
        StdOp::ProcExit => {
            if n_args != 1 {
                return Err("std.process.exit accepts one argument (code)".into());
            }
            if arg_types[0] != Ty::Number && arg_types[0] != Ty::Any {
                return Err(format!("std.process.exit expects a number code, got {:?}", arg_types[0]));
            }
            Ok(Ty::Void)
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StdFunc {
    PrintStr,
    PrintI64,
    PrintBool,
    StdInLine,
    ParseNumber,
    FromCString,
    StrLen,
    CharAt,
    NetSockaddrIn,
    NetSocket,
    NetBind,
    NetListen,
    NetAccept,
    NetRecv,
    NetSend,
    NetClose,
    ProcFork,
    ProcExec1,
    ProcExec2,
    ProcPipe,
    ProcPipeRead,
    ProcPipeWrite,
    ProcWait,
    ProcExit,
}

/// Context surface the codegen's std.* emission needs from the compiler.
pub trait StdEmitter {
    fn emit_expr(&mut self, b: &mut FunctionBuilder, e: &Expr, vars: &HashMap<String, Variable>) -> Result<Value, String>;
    fn expr_is_boolean(&self, e: &Expr) -> bool;
    fn runtime_func(&self, f: StdFunc) -> FuncId;
    fn func_id(&self, name: &str) -> Option<FuncId>;
    fn intern_string(&mut self, s: &[u8], null_terminated: bool) -> Result<DataId, String>;
    fn declare_data_in_func(&mut self, id: DataId, func: &mut Function) -> GlobalValue;
    fn declare_func_in_func(&mut self, id: FuncId, func: &mut Function) -> FuncRef;
}

pub fn emit_std_call(
    ctx: &mut impl StdEmitter,
    b: &mut FunctionBuilder,
    op: StdOp,
    args: &[Expr],
    vars: &HashMap<String, Variable>,
) -> Result<Value, String> {
    match op {
        StdOp::Log => {
            if args.len() != 1 {
                return Err("std.log accepts one expression".into());
            }
            if let Expr::Str(s) = &args[0] {
                let id = ctx.intern_string(s, false)?;
                let gv = ctx.declare_data_in_func(id, b.func);
                let base = b.ins().symbol_value(types::I64, gv);
                let hdr = b.ins().iconst(types::I64, 8);
                let p = b.ins().iadd(base, hdr);
                let l = b.ins().iconst(types::I64, s.len() as i64);
                let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::PrintStr), b.func);
                let call = b.ins().call(callee, &[p, l]);
                return Ok(b.func.dfg.inst_results(call)[0]);
            }
            let x = ctx.emit_expr(b, &args[0], vars)?;
            let fid = if ctx.expr_is_boolean(&args[0]) {
                ctx.runtime_func(StdFunc::PrintBool)
            } else {
                ctx.runtime_func(StdFunc::PrintI64)
            };
            let callee = ctx.declare_func_in_func(fid, b.func);
            let call = b.ins().call(callee, &[x]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::In => {
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::StdInLine), b.func);
            let call = b.ins().call(callee, &[]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ParseNumber => {
            if args.len() != 1 {
                return Err("std.parseNumber accepts one expression".into());
            }
            let x = ctx.emit_expr(b, &args[0], vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ParseNumber), b.func);
            let call = b.ins().call(callee, &[x]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ToCString => {
            if args.len() != 1 {
                return Err("std.toCString accepts one expression".into());
            }
            let x = ctx.emit_expr(b, &args[0], vars)?;
            let mask = b.ins().iconst(types::I64, i64::MAX);
            Ok(b.ins().band(x, mask))
        }
        StdOp::FromCString => {
            if args.len() != 2 {
                return Err("std.fromCString accepts two expressions".into());
            }
            let ptr = ctx.emit_expr(b, &args[0], vars)?;
            let len = ctx.emit_expr(b, &args[1], vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::FromCString), b.func);
            let call = b.ins().call(callee, &[ptr, len]);
            let out = b.func.dfg.inst_results(call)[0];
            // Tag the freshly copied buffer as a Nexa string (stores the pointer
            // in the low bits, sets the same INT64_MIN tag bit that toCString
            // masks off), so the result works in concatenation, std.log, etc.
            //
            // COPYING, not sharing (the inverse direction is deliberately
            // asymmetric):
            //   - std.toCString SHARES the source string's buffer -- it just
            //     masks off the tag and hands back the same memory, so the
            //     Pointer aliases the string and is only valid while the
            //     original string lives.
            //   - std.fromCString COPIES: nexa_from_cstring allocates an
            //     independent buffer and memcpy's `len` bytes into it. The
            //     resulting string remains valid even if the source Pointer's
            //     memory is later freed or overwritten.
            let tag = b.ins().iconst(types::I64, i64::MIN);
            Ok(b.ins().bor(out, tag))
        }
        StdOp::StrLen => {
            if args.len() != 1 {
                return Err("std.strlen accepts one expression".into());
            }
            let x = ctx.emit_expr(b, &args[0], vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::StrLen), b.func);
            let call = b.ins().call(callee, &[x]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::CharAt => {
            if args.len() != 2 {
                return Err("std.charAt accepts two expressions".into());
            }
            let s = ctx.emit_expr(b, &args[0], vars)?;
            let i = ctx.emit_expr(b, &args[1], vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::CharAt), b.func);
            let call = b.ins().call(callee, &[s, i]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::NetSockaddrIn => {
            if args.len() != 2 {
                return Err("std.net.sockaddrIn accepts two expressions".into());
            }
            let port = ctx.emit_expr(b, &args[0], vars)?;
            let addr = ctx.emit_expr(b, &args[1], vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::NetSockaddrIn), b.func);
            let call = b.ins().call(callee, &[port, addr]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::NetSocket => {
            if args.len() != 3 {
                return Err("std.net.socket accepts three expressions".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::NetSocket), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::NetBind => {
            if args.len() != 3 {
                return Err("std.net.bind accepts three expressions".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::NetBind), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::NetListen => {
            if args.len() != 2 {
                return Err("std.net.listen accepts two expressions".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::NetListen), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::NetAccept => {
            if args.len() != 1 {
                return Err("std.net.accept accepts one expression".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::NetAccept), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::NetRecv => {
            if args.len() != 4 {
                return Err("std.net.recv accepts four expressions".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::NetRecv), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::NetSend => {
            if args.len() != 4 {
                return Err("std.net.send accepts four expressions".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::NetSend), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::NetClose => {
            if args.len() != 1 {
                return Err("std.net.close accepts one expression".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::NetClose), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ProcFork => {
            if !args.is_empty() {
                return Err("std.process.fork accepts no expressions".into());
            }
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ProcFork), b.func);
            let call = b.ins().call(callee, &[]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ProcExec1 => {
            if args.len() != 1 {
                return Err("std.process.exec1 accepts one expression".into());
            }
            let p = ctx.emit_expr(b, &args[0], vars)?;
            let mask = b.ins().iconst(types::I64, i64::MAX);
            let p = b.ins().band(p, mask);
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ProcExec1), b.func);
            let call = b.ins().call(callee, &[p]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ProcExec2 => {
            if args.len() != 2 {
                return Err("std.process.exec2 accepts two expressions".into());
            }
            let p = ctx.emit_expr(b, &args[0], vars)?;
            let a = ctx.emit_expr(b, &args[1], vars)?;
            let mask = b.ins().iconst(types::I64, i64::MAX);
            let p = b.ins().band(p, mask);
            let a = b.ins().band(a, mask);
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ProcExec2), b.func);
            let call = b.ins().call(callee, &[p, a]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ProcPipe => {
            if !args.is_empty() {
                return Err("std.process.pipe accepts no expressions".into());
            }
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ProcPipe), b.func);
            let call = b.ins().call(callee, &[]);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ProcPipeRead => {
            if args.len() != 1 {
                return Err("std.process.pipeReadFd accepts one expression".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ProcPipeRead), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ProcPipeWrite => {
            if args.len() != 1 {
                return Err("std.process.pipeWriteFd accepts one expression".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ProcPipeWrite), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ProcWait => {
            if args.len() != 1 {
                return Err("std.process.wait accepts one expression".into());
            }
            let xs = emit_arg_exprs(ctx, b, args, vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ProcWait), b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        StdOp::ProcExit => {
            if args.len() != 1 {
                return Err("std.process.exit accepts one expression".into());
            }
            let code = ctx.emit_expr(b, &args[0], vars)?;
            let callee = ctx.declare_func_in_func(ctx.runtime_func(StdFunc::ProcExit), b.func);
            b.ins().call(callee, &[code]);
            // nexa_process_exit does not return (and has no return value), so
            // fabricate a dummy 0 result.
            Ok(b.ins().iconst(types::I64, 0))
        }
        StdOp::FuncPtr => {
            if args.len() != 1 {
                return Err("std.funcPtr accepts one expression".into());
            }
            let func_name = if let Expr::Str(s) = &args[0] {
                String::from_utf8(s.clone()).map_err(|_| "std.funcPtr requires a UTF-8 string literal".to_string())?
            } else {
                return Err("std.funcPtr requires a string literal".into());
            };
            let id = ctx
                .func_id(&func_name)
                .ok_or_else(|| format!("std.funcPtr: unknown function \"{func_name}\""))?;
            let func_ref = ctx.declare_func_in_func(id, b.func);
            Ok(b.ins().func_addr(types::I64, func_ref))
        }
    }
}

fn emit_arg_exprs(
    ctx: &mut impl StdEmitter,
    b: &mut FunctionBuilder,
    args: &[Expr],
    vars: &HashMap<String, Variable>,
) -> Result<Vec<Value>, String> {
    let mut xs = Vec::with_capacity(args.len());
    for a in args {
        xs.push(ctx.emit_expr(b, a, vars)?);
    }
    Ok(xs)
}
