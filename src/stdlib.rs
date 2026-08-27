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
    FuncPtr,
}

impl StdOp {
    pub fn of(name: &str) -> Option<StdOp> {
        match name {
            "std.log" => Some(StdOp::Log),
            "std.in" => Some(StdOp::In),
            "std.parseNumber" => Some(StdOp::ParseNumber),
            "std.toCString" => Some(StdOp::ToCString),
            "std.funcPtr" => Some(StdOp::FuncPtr),
            _ => None,
        }
    }

    pub fn ir_type(self) -> IrType {
        match self {
            StdOp::Log => IrType::Void,
            StdOp::In => IrType::String,
            StdOp::ParseNumber => IrType::Number,
            StdOp::ToCString => IrType::Pointer,
            StdOp::FuncPtr => IrType::Pointer,
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
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StdFunc {
    PrintStr,
    PrintI64,
    PrintBool,
    StdInLine,
    ParseNumber,
}

/// Context surface the codegen's std.* emission needs from the compiler.
pub trait StdEmitter {
    fn emit_expr(&mut self, b: &mut FunctionBuilder, e: &Expr, vars: &HashMap<String, Variable>) -> Result<Value, String>;
    fn expr_is_boolean(&self, e: &Expr) -> bool;
    fn runtime_func(&self, f: StdFunc) -> FuncId;
    fn func_id(&self, name: &str) -> Option<FuncId>;
    fn intern_string(&mut self, s: &str, null_terminated: bool) -> Result<DataId, String>;
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
                let p = b.ins().symbol_value(types::I64, gv);
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
        StdOp::FuncPtr => {
            if args.len() != 1 {
                return Err("std.funcPtr accepts one expression".into());
            }
            let func_name = if let Expr::Str(s) = &args[0] {
                s.clone()
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
