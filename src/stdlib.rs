// Builtin std.* dispatch, centralized across the three pipeline stages so that
// each stage no longer hard-codes the internal std.* name strings.
//
// Stage interfaces:
//   - Checker:   stdlib::StdOp::of(name) + stdlib::check_call(...)
//   - IR:        stdlib::is_log(...) + stdlib::StdOp::of(name).ir_type()
//   - Codegen:   stdlib::StdOp::of(name) + stdlib::emit_std_call(...)

use std::collections::HashMap;

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{FuncRef, Function, InstBuilder, Value};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::FuncId;

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
    ToF32,
    ToF64,
    ToInt,
    ProcExec1,
    ProcExec2,
    ProcPipe,
    ProcPipeRead,
    ProcPipeWrite,
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
            "std.toF32" => Some(StdOp::ToF32),
            "std.toF64" => Some(StdOp::ToF64),
            "std.toInt" => Some(StdOp::ToInt),
            "std.process.exec1" => Some(StdOp::ProcExec1),
            "std.process.exec2" => Some(StdOp::ProcExec2),
            "std.process.pipe" => Some(StdOp::ProcPipe),
            "std.process.pipeReadFd" => Some(StdOp::ProcPipeRead),
            "std.process.pipeWriteFd" => Some(StdOp::ProcPipeWrite),
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
            StdOp::ToF32 => IrType::F32,
            StdOp::ToF64 => IrType::F64,
            StdOp::ToInt => IrType::Number,
            StdOp::ProcPipe => IrType::Pointer,
            StdOp::ProcExec1
            | StdOp::ProcExec2
            | StdOp::ProcPipeRead
            | StdOp::ProcPipeWrite => IrType::Number,
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
            if !matches!(t, Ty::Number | Ty::Boolean | Ty::String | Ty::F32 | Ty::F64) {
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
        StdOp::ToF32 | StdOp::ToF64 => {
            if n_args != 1 {
                return Err(format!("{} accepts one argument", if matches!(op, StdOp::ToF32) { "std.toF32" } else { "std.toF64" }));
            }
            let t = arg_types[0];
            if !matches!(t, Ty::Number | Ty::F32 | Ty::F64 | Ty::Any) {
                return Err(format!("{} expects a number, f32, or f64 argument, got {t:?}", if matches!(op, StdOp::ToF32) { "std.toF32" } else { "std.toF64" }));
            }
            Ok(if matches!(op, StdOp::ToF32) { Ty::F32 } else { Ty::F64 })
        }
        StdOp::ToInt => {
            if n_args != 1 {
                return Err("std.toInt accepts one argument".into());
            }
            let t = arg_types[0];
            if !matches!(t, Ty::Number | Ty::F32 | Ty::F64 | Ty::Any) {
                return Err(format!("std.toInt expects a number, f32, or f64 argument, got {t:?}"));
            }
            Ok(Ty::Number)
        }
        StdOp::ProcPipe => {
            if n_args != 0 {
                return Err("std.process.pipe accepts no arguments".into());
            }
            Ok(Ty::Pointer)
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
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StdFunc {
    PrintCStr,
    PrintI64,
    PrintBool,
    PrintF64,
    PrintF32,
    StdInLine,
    ParseNumber,
    FromCString,
    StrLen,
    CharAt,
    ProcExec1,
    ProcExec2,
    ProcPipe,
    ProcPipeRead,
    ProcPipeWrite,
}

/// Context surface the codegen's std.* emission needs from the compiler.
pub trait StdEmitter {
    fn emit_expr(&mut self, b: &mut FunctionBuilder, e: &Expr, vars: &HashMap<String, Variable>) -> Result<Value, String>;
    // The statically-known type of an expression (codegen's expr_kind).
    fn expr_ir_kind(&self, _e: &Expr) -> IrType {
        IrType::Any
    }
    fn runtime_func(&self, f: StdFunc) -> FuncId;
    fn func_id(&self, name: &str) -> Option<FuncId>;
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
            let x = ctx.emit_expr(b, &args[0], vars)?;
            let fid = match ctx.expr_ir_kind(&args[0]) {
                IrType::String => ctx.runtime_func(StdFunc::PrintCStr),
                IrType::Boolean => ctx.runtime_func(StdFunc::PrintBool),
                IrType::F64 => ctx.runtime_func(StdFunc::PrintF64),
                IrType::F32 => ctx.runtime_func(StdFunc::PrintF32),
                _ => ctx.runtime_func(StdFunc::PrintI64),
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
        StdOp::ToInt => {
            if args.len() != 1 {
                return Err("std.toInt accepts one expression".into());
            }
            let x = ctx.emit_expr(b, &args[0], vars)?;
            Ok(match ctx.expr_ir_kind(&args[0]) {
                IrType::F32 | IrType::F64 => b.ins().fcvt_to_sint(types::I64, x),
                _ => x,
            })
        }
        StdOp::ToF32 => {
            if args.len() != 1 {
                return Err("std.toF32 accepts one expression".into());
            }
            let x = ctx.emit_expr(b, &args[0], vars)?;
            Ok(match ctx.expr_ir_kind(&args[0]) {
                IrType::F64 => b.ins().fdemote(types::F32, x),
                IrType::F32 => x,
                _ => b.ins().fcvt_from_sint(types::F32, x),
            })
        }
        StdOp::ToF64 => {
            if args.len() != 1 {
                return Err("std.toF64 accepts one expression".into());
            }
            let x = ctx.emit_expr(b, &args[0], vars)?;
            Ok(match ctx.expr_ir_kind(&args[0]) {
                IrType::F32 => b.ins().fpromote(types::F64, x),
                IrType::F64 => x,
                _ => b.ins().fcvt_from_sint(types::F64, x),
            })
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
