use std::collections::HashMap;
use std::fmt;

use crate::stdlib;
use crate::{Expr, Fun, Stmt};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)] pub struct ValueId(pub usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)] pub struct BlockId(pub usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub enum IrType { Number, Boolean, String, NumberArray, Float32Array, Float64Array, F32, F64, ClosureNumber, Class(&'static str), Any, Void, Pointer, TParam }
#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub enum Ty { Number, Boolean, String, NumberArray, Float32Array, Float64Array, F32, F64, Void, Any, Class(&'static str), Interface(&'static str), ClosureNumber, Pointer }

// Interface types share the class-layout representation at the codegen level: a
// value whose static type is an interface is still a class instance pointer
// (the checker has already verified structural compatibility), and its fields
// are laid out at the interface's own declaration-order offsets.
pub fn ty_to_ir(ty: Ty) -> IrType { match ty { Ty::Number => IrType::Number, Ty::Boolean => IrType::Boolean, Ty::String => IrType::String, Ty::NumberArray => IrType::NumberArray, Ty::Float32Array => IrType::Float32Array, Ty::Float64Array => IrType::Float64Array, Ty::F32 => IrType::F32, Ty::F64 => IrType::F64, Ty::ClosureNumber => IrType::ClosureNumber, Ty::Class(name) => IrType::Class(name), Ty::Interface(name) => IrType::Class(name), Ty::Void => IrType::Void, Ty::Any => IrType::Any, Ty::Pointer => IrType::Pointer } }
pub fn ir_to_ty(ir_ty: IrType) -> Ty { match ir_ty { IrType::Number => Ty::Number, IrType::Boolean => Ty::Boolean, IrType::String => Ty::String, IrType::NumberArray => Ty::NumberArray, IrType::Float32Array => Ty::Float32Array, IrType::Float64Array => Ty::Float64Array, IrType::F32 => Ty::F32, IrType::F64 => Ty::F64, IrType::ClosureNumber => Ty::ClosureNumber, IrType::Class(name) => Ty::Class(name), IrType::Void => Ty::Void, IrType::Any | IrType::TParam => Ty::Any, IrType::Pointer => Ty::Pointer } }

#[derive(Clone, Debug)] pub enum Inst {
    Const(ValueId, i64),
    Copy(ValueId, ValueId),
    Add(ValueId, ValueId, ValueId),
    Sub(ValueId, ValueId, ValueId),
    Mul(ValueId, ValueId, ValueId),
    Div(ValueId, ValueId, ValueId),
    Call(ValueId, String, Vec<ValueId>),
    Print(ValueId),
    Phi(ValueId, Vec<(BlockId, ValueId)>),
    Return(Option<ValueId>),
    Note(String),
}

#[derive(Clone, Debug)] pub struct Block { pub id: BlockId, pub insts: Vec<Inst> }
#[derive(Clone, Debug)] pub struct IrFunction { pub name: String, pub params: Vec<ValueId>, pub value_types: HashMap<ValueId, IrType>, pub blocks: Vec<Block> }
#[derive(Clone, Debug, Default)] pub struct IrModule { pub functions: Vec<IrFunction> }

struct Builder { next_value: usize, blocks: Vec<Block>, current: BlockId, vars: HashMap<String, (ValueId, IrType)>, value_types: HashMap<ValueId, IrType> }
impl Builder {
    fn new() -> Self { Self { next_value: 0, blocks: vec![Block { id: BlockId(0), insts: Vec::new() }], current: BlockId(0), vars: HashMap::new(), value_types: HashMap::new() } }
    fn value(&mut self, ty: IrType) -> ValueId { let v = ValueId(self.next_value); self.next_value += 1; self.value_types.insert(v, ty); v }
    fn push(&mut self, i: Inst) { self.blocks[self.current.0].insts.push(i); }
    fn expr(&mut self, e: &Expr) -> Option<(ValueId, IrType)> { match e {
        Expr::Num(n) => { let v = self.value(IrType::Number); self.push(Inst::Const(v, *n)); Some((v, IrType::Number)) }
        Expr::Bool(b) => { let v = self.value(IrType::Boolean); self.push(Inst::Const(v, i64::from(*b))); Some((v, IrType::Boolean)) }
        Expr::Var(n) => self.vars.get(n).copied(),
        Expr::Bin(a, op, b) => { let (x, xt) = self.expr(a)?; let (y, yt) = self.expr(b)?; let ty = match op.as_str() { "+" | "-" | "*" | "/" => if xt == IrType::Number && yt == IrType::Number { IrType::Number } else { self.push(Inst::Note(format!("typed arithmetic requires number, got {xt:?} and {yt:?}"))); IrType::Any }, "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||" => IrType::Boolean, _ => { self.push(Inst::Note(format!("unsupported operator {op}"))); IrType::Any } }; let v = self.value(ty); self.push(match op.as_str() { "+" => Inst::Add(v, x, y), "-" => Inst::Sub(v, x, y), "*" => Inst::Mul(v, x, y), "/" => Inst::Div(v, x, y), _ => Inst::Note(format!("boolean operation {op} pending in Cranelift lowering")) }); Some((v, ty)) }
        Expr::Call(n, args) | Expr::CallGeneric(n, _, args) => { let values: Vec<ValueId> = args.iter().filter_map(|x| self.expr(x).map(|v| v.0)).collect(); let is_log = stdlib::is_log(n);         let ty = if is_log { IrType::Void } else { stdlib::StdOp::of(n).map(|op| op.ir_type()).unwrap_or(IrType::Any) }; let v = self.value(ty); if is_log { if let Some(x) = values.first() { self.push(Inst::Print(*x)); } else { self.push(Inst::Note("string print pending in SSA lowering".into())); } } else { self.push(Inst::Call(v, n.clone(), values)); } Some((v, ty)) }
        Expr::Unary(_, _) | Expr::Str(_) | Expr::FNum(_) | Expr::Array(_) | Expr::Index(_, _) | Expr::Closure(_) | Expr::CallClosure(_) | Expr::FieldAccess(_, _) | Expr::MethodCall(_, _, _) | Expr::New(_, _) | Expr::ObjectLiteral(_, _) => { self.push(Inst::Note("expression pending in SSA lowering".into())); None }
    } }
    fn stmt(&mut self, s: &Stmt) { match s {
        Stmt::Let(n, _, e) => if let Some(v) = self.expr(e) { self.vars.insert(n.clone(), v); },
        Stmt::Assign(n, e) => if let Some(v) = self.expr(e) { self.vars.insert(n.clone(), v); },
        Stmt::Return(e) => { let v = self.expr(e).map(|x| x.0); self.push(Inst::Return(v)); },
        Stmt::Expr(e) => { self.expr(e); },
        Stmt::Defer(ss) => for s in ss { self.stmt(s); },
        Stmt::Block(ss) => for s in ss { self.stmt(s); },
        Stmt::If(_, _, _) | Stmt::While(_, _) | Stmt::For(_, _, _, _) | Stmt::ForOf(_, _, _) | Stmt::IndexAssign(_, _, _) | Stmt::FieldAssign(_, _, _) => self.push(Inst::Note("control-flow block/phi lowering pending".into())),
    } }
}

pub fn lower_program(functions: &[Fun]) -> IrModule { let mut m = IrModule::default(); for f in functions { let mut b = Builder::new(); let mut params = Vec::new(); for (i, n) in f.params.iter().enumerate() { let ty = f.param_types.get(i).copied().unwrap_or(IrType::Any); let v = b.value(ty); params.push(v); b.vars.insert(n.clone(), (v, ty)); } for s in &f.body { b.stmt(s); } m.functions.push(IrFunction { name: f.name.clone(), params, value_types: b.value_types, blocks: b.blocks }); } m }

impl fmt::Display for IrModule { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { for fun in &self.functions { write!(f, "fn {}(", fun.name)?; for (i, p) in fun.params.iter().enumerate() { if i > 0 { write!(f, ", ")?; } write!(f, "%{}:{:?}", p.0, fun.value_types[p])?; } writeln!(f, ") {{")?; for block in &fun.blocks { writeln!(f, "  block{}:", block.id.0)?; for i in &block.insts { writeln!(f, "    {:?}", i)?; } } writeln!(f, "}}")?; } Ok(()) } }
