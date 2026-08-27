use cranelift_codegen::ir::{types, AbiParam, Function, InstBuilder, MemFlags, Signature, Value};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::{HashMap, HashSet};

use crate::checker::ClassDef;
use crate::ir;
use crate::ir::Ty;
use crate::{leak_str, ClassDecl, Expr, ExternSig, Fun, Stmt};

fn inferred_ir_type(e: &Expr) -> ir::IrType { match e { Expr::Num(_) => ir::IrType::Number, Expr::Bool(_) => ir::IrType::Boolean, Expr::Closure(_) => ir::IrType::ClosureNumber, Expr::New(name, _) => ir::IrType::Class(leak_str(name)), Expr::FieldAccess(_, _) => ir::IrType::Number, _ => ir::IrType::Any } }
fn add_ref(name: &str, refs: &mut Vec<String>) { if !refs.iter().any(|x| x == name) { refs.push(name.to_string()); } }
fn collect_expr_refs(e: &Expr, refs: &mut Vec<String>, mutated: &mut HashSet<String>) -> Result<(), String> { match e { Expr::Var(n) => add_ref(n, refs), Expr::Bin(a, _, b) => { collect_expr_refs(a, refs, mutated)?; collect_expr_refs(b, refs, mutated)?; }, Expr::Unary(_, x) => collect_expr_refs(x, refs, mutated)?, Expr::Index(a, i) => { collect_expr_refs(a, refs, mutated)?; collect_expr_refs(i, refs, mutated)?; }, Expr::Call(_, args) | Expr::CallGeneric(_, _, args) => for a in args { collect_expr_refs(a, refs, mutated)?; }, Expr::FieldAccess(obj, _) => collect_expr_refs(obj, refs, mutated)?, Expr::MethodCall(obj, _, args) => { collect_expr_refs(obj, refs, mutated)?; for a in args { collect_expr_refs(a, refs, mutated)?; } }, Expr::Closure(_) => return Err("nested closures are not supported in Nexa v1".into()), Expr::Num(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Array | Expr::New(_, _) => {} } Ok(()) }
fn collect_stmt_refs(s: &Stmt, refs: &mut Vec<String>, mutated: &mut HashSet<String>) -> Result<(), String> { match s { Stmt::Let(_, _, e) | Stmt::Return(e) | Stmt::Expr(e) => collect_expr_refs(e, refs, mutated)?, Stmt::Assign(n, e) => { add_ref(n, refs); mutated.insert(n.clone()); collect_expr_refs(e, refs, mutated)?; }, Stmt::FieldAssign(obj, _, e) => { collect_expr_refs(obj, refs, mutated)?; collect_expr_refs(e, refs, mutated)?; }, Stmt::IndexAssign(a, i, e) => { collect_expr_refs(a, refs, mutated)?; collect_expr_refs(i, refs, mutated)?; collect_expr_refs(e, refs, mutated)?; }, Stmt::Block(body) => for s in body { collect_stmt_refs(s, refs, mutated)?; }, Stmt::If(c, yes, no) => { collect_expr_refs(c, refs, mutated)?; for s in yes.iter().chain(no) { collect_stmt_refs(s, refs, mutated)?; } }, Stmt::While(c, body) => { collect_expr_refs(c, refs, mutated)?; for s in body { collect_stmt_refs(s, refs, mutated)?; } }, Stmt::For(init, c, update, body) => { collect_stmt_refs(init, refs, mutated)?; collect_expr_refs(c, refs, mutated)?; collect_stmt_refs(update, refs, mutated)?; for s in body { collect_stmt_refs(s, refs, mutated)?; } } } Ok(()) }
fn find_closure_expr(e: &Expr, found: &mut Vec<Vec<Stmt>>) -> Result<(), String> { match e { Expr::Closure(body) => { found.push(body.clone()); }, Expr::Bin(a, _, b) => { find_closure_expr(a, found)?; find_closure_expr(b, found)?; }, Expr::Unary(_, x) => find_closure_expr(x, found)?, Expr::Index(a, i) => { find_closure_expr(a, found)?; find_closure_expr(i, found)?; }, Expr::Call(_, args) | Expr::CallGeneric(_, _, args) => for a in args { find_closure_expr(a, found)?; }, Expr::FieldAccess(obj, _) => find_closure_expr(obj, found)?, Expr::MethodCall(obj, _, args) => { find_closure_expr(obj, found)?; for a in args { find_closure_expr(a, found)?; } }, Expr::Num(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Array | Expr::Var(_) | Expr::New(_, _) => {} } Ok(()) }
fn find_closure_stmt(s: &Stmt, found: &mut Vec<Vec<Stmt>>) -> Result<(), String> { match s { Stmt::Let(_, _, e) | Stmt::Return(e) | Stmt::Expr(e) => find_closure_expr(e, found)?, Stmt::Assign(_, e) => find_closure_expr(e, found)?, Stmt::FieldAssign(obj, _, e) => { find_closure_expr(obj, found)?; find_closure_expr(e, found)?; }, Stmt::IndexAssign(a, i, e) => { find_closure_expr(a, found)?; find_closure_expr(i, found)?; find_closure_expr(e, found)?; }, Stmt::Block(body) => for s in body { find_closure_stmt(s, found)?; }, Stmt::If(c, yes, no) => { find_closure_expr(c, found)?; for s in yes.iter().chain(no) { find_closure_stmt(s, found)?; } }, Stmt::While(c, body) => { find_closure_expr(c, found)?; for s in body { find_closure_stmt(s, found)?; } }, Stmt::For(init, c, update, body) => { find_closure_stmt(init, found)?; find_closure_expr(c, found)?; find_closure_stmt(update, found)?; for s in body { find_closure_stmt(s, found)?; } } } Ok(()) }
fn collect_outer_mutations(s: &Stmt, mutated: &mut HashSet<String>) { match s { Stmt::Assign(n, _) => { mutated.insert(n.clone()); }, Stmt::Block(body) => for x in body { collect_outer_mutations(x, mutated); }, Stmt::If(_, yes, no) => for x in yes.iter().chain(no) { collect_outer_mutations(x, mutated); }, Stmt::While(_, body) => for x in body { collect_outer_mutations(x, mutated); }, Stmt::For(init, _, update, body) => { collect_outer_mutations(init, mutated); collect_outer_mutations(update, mutated); for x in body { collect_outer_mutations(x, mutated); } }, Stmt::Let(_, _, _) | Stmt::Return(_) | Stmt::Expr(_) | Stmt::IndexAssign(_, _, _) | Stmt::FieldAssign(_, _, _) => {} } }

#[derive(Clone, Debug)]
struct Capture { name: String, ty: ir::IrType, mutable: bool }
#[derive(Clone, Debug)]
struct ClosureDef { name: String, parent: String, body: Vec<Stmt>, captures: Vec<Capture> }


pub(crate) struct Compiler {
    pub(crate) m: ObjectModule, funcs: HashMap<String, FuncId>, returns: HashMap<String, ir::IrType>,
    closures: HashMap<String, FuncId>, closure_defs: HashMap<String, Vec<ClosureDef>>,
    active_kinds: HashMap<String, ir::IrType>, active_cells: HashSet<String>,
    cell_vars: HashMap<String, Variable>, current_func: String,
    closure_index: HashMap<String, usize>,
    print_i64: FuncId, print_bool: FuncId, print_str: FuncId,
    array_new: FuncId, array_get: FuncId, array_set: FuncId, concat_str: FuncId,
    env_new: FuncId, env_get: FuncId, env_set: FuncId,
    cell_new: FuncId, cell_get: FuncId, cell_set: FuncId,
    closure_new: FuncId, closure_call: FuncId,
    stdin_line: FuncId,
    parse_number: FuncId,
    strings: HashMap<String, DataId>,
    class_new: FuncId,
    class_defs: HashMap<String, ClassDef>,
    extern_funcs: HashMap<String, FuncId>,
    extern_voids: HashSet<String>,
}
impl Compiler {
    pub(crate) fn new() -> Result<Self, String> { let isa = cranelift_codegen::isa::lookup(target_lexicon::HOST).map_err(|e| e.to_string())?.finish(settings::Flags::new(settings::builder())).map_err(|e| e.to_string())?; let b = ObjectBuilder::new(isa, "nexa", cranelift_module::default_libcall_names()).map_err(|e| e.to_string())?; let m = ObjectModule::new(b); let mut c = Self { m, funcs: HashMap::new(), returns: HashMap::new(), closures: HashMap::new(), closure_defs: HashMap::new(), active_kinds: HashMap::new(), active_cells: HashSet::new(), cell_vars: HashMap::new(), current_func: String::new(), closure_index: HashMap::new(), print_i64: FuncId::from_u32(0), print_bool: FuncId::from_u32(0), print_str: FuncId::from_u32(0), array_new: FuncId::from_u32(0), array_get: FuncId::from_u32(0), array_set: FuncId::from_u32(0), concat_str: FuncId::from_u32(0), env_new: FuncId::from_u32(0), env_get: FuncId::from_u32(0), env_set: FuncId::from_u32(0), cell_new: FuncId::from_u32(0), cell_get: FuncId::from_u32(0), cell_set: FuncId::from_u32(0), closure_new: FuncId::from_u32(0), closure_call: FuncId::from_u32(0), stdin_line: FuncId::from_u32(0), parse_number: FuncId::from_u32(0), strings: HashMap::new(), class_new: FuncId::from_u32(0), class_defs: HashMap::new(), extern_funcs: HashMap::new(), extern_voids: HashSet::new() }; c.print_i64 = c.import("nexa_print_i64", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.print_bool = c.import("nexa_print_bool", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.print_str = c.import("nexa_print_str", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_new = c.import("nexa_array_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_get = c.import("nexa_array_get", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_set = c.import("nexa_array_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.concat_str = c.import("nexa_concat_str", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_new = c.import("nexa_env_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_get = c.import("nexa_env_get", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_set = c.import("nexa_env_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_new = c.import("nexa_cell_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_get = c.import("nexa_cell_get", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_set = c.import("nexa_cell_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.closure_new = c.import("nexa_closure_new", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.closure_call = c.import("nexa_closure_call", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.stdin_line = c.import("nexa_stdin_line", vec![], vec![AbiParam::new(types::I64)])?; c.parse_number = c.import("nexa_std_parse_number", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.class_new = c.import("nexa_class_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; Ok(c) }
    fn import(&mut self, n: &str, params: Vec<AbiParam>, returns: Vec<AbiParam>) -> Result<FuncId, String> { let mut s = Signature::new(self.m.isa().default_call_conv()); s.params = params; s.returns = returns; self.m.declare_function(n, Linkage::Import, &s).map_err(|e| e.to_string()) }
    pub(crate) fn declare_externs(&mut self, externs: &HashMap<String, ExternSig>) -> Result<(), String> {
        for (name, sig) in externs {
            let mut s = Signature::new(self.m.isa().default_call_conv());
            s.params = (0..sig.params.len()).map(|_| AbiParam::new(types::I64)).collect();
            let has_ret = sig.ret != Ty::Void;
            if has_ret { s.returns.push(AbiParam::new(types::I64)); }
            let id = self.m.declare_function(name, Linkage::Import, &s).map_err(|e| e.to_string())?;
            self.extern_funcs.insert(name.clone(), id);
            if !has_ret { self.extern_voids.insert(name.clone()); }
        }
        Ok(())
    }
    fn prepare_closures(&mut self, fs: &[Fun]) -> Result<(), String> { for f in fs { let mut outer = HashMap::new(); for (n, t) in f.params.iter().zip(&f.param_types) { outer.insert(n.clone(), *t); } let mut outer_mutated = HashSet::new(); for s in &f.body { collect_outer_mutations(s, &mut outer_mutated); if let Stmt::Let(n, annotation, e) = s { outer.insert(n.clone(), annotation.unwrap_or_else(|| inferred_ir_type(e))); } } let mut closure_bodies = Vec::new(); for s in &f.body { find_closure_stmt(s, &mut closure_bodies)?; } for body in closure_bodies { let mut refs = Vec::new(); let mut closure_mutated = HashSet::new(); for s in &body { collect_stmt_refs(s, &mut refs, &mut closure_mutated)?; } let mut captures = Vec::new(); for name in refs { let ty = *outer.get(&name).ok_or_else(|| format!("closure in {} references non-local `{name}`", f.name))?; if !matches!(ty, ir::IrType::Number | ir::IrType::Boolean) { return Err(format!("Nexa v1 closures only capture number/boolean values, `{name}` is {ty:?}")); } captures.push(Capture { name: name.clone(), ty, mutable: closure_mutated.contains(&name) || outer_mutated.contains(&name) }); } let name = format!("__nexa_closure_{}", self.closure_defs.values().map(|v| v.len()).sum::<usize>() + self.closure_defs.get(&f.name).map(|v| v.len()).unwrap_or(0)); self.closure_defs.entry(f.name.clone()).or_default().push(ClosureDef { name, parent: f.name.clone(), body, captures }); } } Ok(()) }
    pub(crate) fn compile(&mut self, classes: &[ClassDecl], fs: &[Fun]) -> Result<(), String> {
        self.prepare_closures(fs)?;
        self.class_defs.clear();
        for c in classes {
            self.class_defs.insert(c.name.clone(), ClassDef {
                name: c.name.clone(),
                fields: c.fields.iter().map(|(n, t)| (n.clone(), *t)).collect(),
                constructor_name: c.constructor.name.clone(),
                method_names: c.methods.iter().map(|m| m.name.clone()).collect(),
            });
        }
        for c in classes {
            let mut s = Signature::new(self.m.isa().default_call_conv());
            s.params = (0..c.constructor.params.len()).map(|_| AbiParam::new(types::I64)).collect();
            s.returns.push(AbiParam::new(types::I64));
            let id = self.m.declare_function(&c.constructor.name, Linkage::Export, &s).map_err(|e| e.to_string())?;
            self.funcs.insert(c.constructor.name.clone(), id);
            self.returns.insert(c.constructor.name.clone(), c.constructor.return_type);
            for m in &c.methods {
                let mut s = Signature::new(self.m.isa().default_call_conv());
                s.params = (0..m.params.len()).map(|_| AbiParam::new(types::I64)).collect();
                s.returns.push(AbiParam::new(types::I64));
                let id = self.m.declare_function(&m.name, Linkage::Export, &s).map_err(|e| e.to_string())?;
                self.funcs.insert(m.name.clone(), id);
                self.returns.insert(m.name.clone(), m.return_type);
            }
        }
        for f in fs {
            if f.param_types.iter().any(|t| *t == ir::IrType::Any || *t == ir::IrType::TParam) || f.return_type == ir::IrType::Any || f.return_type == ir::IrType::TParam {
                return Err(format!("Nexa refuses to lower function {} with an unresolved Any or TParam type", f.name));
            }
            let mut s = Signature::new(self.m.isa().default_call_conv());
            s.params = (0..f.params.len()).map(|_| AbiParam::new(types::I64)).collect();
            s.returns.push(AbiParam::new(types::I64));
            let id = self.m.declare_function(&f.name, Linkage::Export, &s).map_err(|e| e.to_string())?;
            self.funcs.insert(f.name.clone(), id);
            self.returns.insert(f.name.clone(), f.return_type);
        }
        for defs in self.closure_defs.values() {
            for def in defs {
                let mut s = Signature::new(self.m.isa().default_call_conv());
                s.params.push(AbiParam::new(types::I64));
                s.returns.push(AbiParam::new(types::I64));
                let id = self.m.declare_function(&def.name, Linkage::Local, &s).map_err(|e| e.to_string())?;
                self.closures.insert(def.name.clone(), id);
            }
        }
        for c in classes {
            self.one(&c.constructor)?;
            for m in &c.methods {
                self.one(m)?;
            }
        }
        for f in fs { self.one(f)?; }
        let all_closures: Vec<ClosureDef> = self.closure_defs.values().flat_map(|v| v.iter().cloned()).collect();
        for def in &all_closures { self.one_closure(def)?; }
        Ok(())
    }
    fn one_closure(&mut self, def: &ClosureDef) -> Result<(), String> { self.current_func = def.parent.clone(); let id = self.closures[&def.name]; let mut fun = Function::new(); let mut sig = Signature::new(self.m.isa().default_call_conv()); sig.params.push(AbiParam::new(types::I64)); sig.returns.push(AbiParam::new(types::I64)); fun.signature = sig; let mut cx = FunctionBuilderContext::new(); let mut b = FunctionBuilder::new(&mut fun, &mut cx); let entry = b.create_block(); b.append_block_params_for_function_params(entry); b.switch_to_block(entry); self.active_kinds.clear(); self.active_cells.clear(); self.cell_vars.clear(); let env = b.block_params(entry)[0]; let mut vars = HashMap::new(); for (slot, capture) in def.captures.iter().enumerate() { let v = b.declare_var(types::I64); let slot_value = b.ins().iconst(types::I64, slot as i64); let getter = self.m.declare_func_in_func(self.env_get, b.func); let call = b.ins().call(getter, &[env, slot_value]); let raw = b.func.dfg.inst_results(call)[0]; let value = if capture.mutable { let cell_var = b.declare_var(types::I64); b.def_var(cell_var, raw); self.cell_vars.insert(capture.name.clone(), cell_var); let cell_getter = self.m.declare_func_in_func(self.cell_get, b.func); let cell_call = b.ins().call(cell_getter, &[raw]); b.func.dfg.inst_results(cell_call)[0] } else { raw }; b.def_var(v, value); vars.insert(capture.name.clone(), v); self.active_kinds.insert(capture.name.clone(), capture.ty); if capture.mutable { self.active_cells.insert(capture.name.clone()); } } let terminated = self.stmts(&mut b, &def.body, &mut vars)?; if !terminated { let z = b.ins().iconst(types::I64, 0); b.ins().return_(&[z]); } b.seal_all_blocks(); b.finalize(); let mut ctx = cranelift_codegen::Context::for_function(fun); self.m.define_function(id, &mut ctx).map_err(|e| format!("{e:?}"))?; Ok(()) }
    fn one(&mut self, f: &Fun) -> Result<(), String> { self.current_func = f.name.clone(); let id = self.funcs[&f.name]; let mut fun = Function::new(); let mut sig = Signature::new(self.m.isa().default_call_conv()); sig.params = (0..f.params.len()).map(|_| AbiParam::new(types::I64)).collect(); sig.returns.push(AbiParam::new(types::I64)); fun.signature = sig; let mut cx = FunctionBuilderContext::new(); let mut b = FunctionBuilder::new(&mut fun, &mut cx); let entry = b.create_block(); b.append_block_params_for_function_params(entry); b.switch_to_block(entry); self.active_kinds.clear(); self.active_cells.clear(); self.cell_vars.clear(); let mut vars = HashMap::new(); for (i, n) in f.params.iter().enumerate() { let v = b.declare_var(types::I64); b.def_var(v, b.block_params(entry)[i]); vars.insert(n.clone(), v); self.active_kinds.insert(n.clone(), f.param_types.get(i).copied().unwrap_or(ir::IrType::Any)); } let terminated = self.stmts(&mut b, &f.body, &mut vars)?; if !terminated { let z = b.ins().iconst(types::I64, 0); b.ins().return_(&[z]); } b.seal_all_blocks(); b.finalize(); let mut ctx = cranelift_codegen::Context::for_function(fun); self.m.define_function(id, &mut ctx).map_err(|e| format!("{e:?}"))?; Ok(()) }
    fn stmts(&mut self, b: &mut FunctionBuilder, ss: &[Stmt], vars: &mut HashMap<String, Variable>) -> Result<bool, String> { for s in ss { if self.stmt(b, s, vars)? { return Ok(true); } } Ok(false) }
    fn stmt(&mut self, b: &mut FunctionBuilder, s: &Stmt, vars: &mut HashMap<String, Variable>) -> Result<bool, String> { match s {
        Stmt::Let(n, annotation, e) => { let v = b.declare_var(types::I64); let x = self.emit(b, e, vars)?; b.def_var(v, x); vars.insert(n.clone(), v); self.active_kinds.insert(n.clone(), annotation.unwrap_or_else(|| self.expr_kind(e))); Ok(false) }
        Stmt::Assign(n, e) => { let v = *vars.get(n).ok_or_else(|| format!("unknown variable {n}"))?; let x = self.emit(b, e, vars)?; b.def_var(v, x); if let Some(&cell_var) = self.cell_vars.get(n) { let cell_ptr = b.use_var(cell_var); let callee = self.m.declare_func_in_func(self.cell_set, b.func); b.ins().call(callee, &[cell_ptr, x]); } Ok(false) }
        Stmt::FieldAssign(obj, field, e) => {
            let obj_val = self.emit(b, obj, vars)?;
            let value = self.emit(b, e, vars)?;
            let cls_name = match obj.as_ref() {
                Expr::Var(n) => {
                    self.active_kinds.get(n).and_then(|k| match k { ir::IrType::Class(c) => Some(*c), _ => None })
                }
                _ => None,
            }.ok_or_else(|| "field assignment on non-class object".to_string())?;
            let cls = self.class_defs.get(cls_name).ok_or_else(|| format!("unknown class {cls_name}"))?;
            let (field_idx, _) = cls.fields.iter().enumerate().find(|(_, (n, _))| n == field).ok_or_else(|| format!("unknown field {field}"))?;
            let offset = b.ins().iconst(types::I64, (field_idx * 8) as i64);
            let ptr = b.ins().iadd(obj_val, offset);
            b.ins().store(MemFlags::new(), value, ptr, 0);
            Ok(false)
        }
        Stmt::IndexAssign(a, i, e) => { let array = self.emit(b, a, vars)?; let index = self.emit(b, i, vars)?; let value = self.emit(b, e, vars)?; let callee = self.m.declare_func_in_func(self.array_set, b.func); b.ins().call(callee, &[array, index, value]); Ok(false) }
        Stmt::Return(e) => { let x = self.emit(b, e, vars)?; b.ins().return_(&[x]); Ok(true) }
        Stmt::Expr(e) => { self.emit(b, e, vars)?; Ok(false) }
        Stmt::Block(body) => self.stmts(b, body, vars),
        Stmt::If(c, yes, no) => { let t = b.create_block(); let f = b.create_block(); let join = b.create_block(); let x = self.emit(b, c, vars)?; b.ins().brif(x, t, &[], f, &[]); b.switch_to_block(t); let yt = self.stmts(b, yes, vars)?; if !yt { b.ins().jump(join, &[]); } b.switch_to_block(f); let ft = self.stmts(b, no, vars)?; if !ft { b.ins().jump(join, &[]); } b.switch_to_block(join); b.seal_block(t); b.seal_block(f); b.seal_block(join); Ok(yt && ft) }
        Stmt::While(c, body) => { let head = b.create_block(); let loop_b = b.create_block(); let exit = b.create_block(); b.ins().jump(head, &[]); b.switch_to_block(head); let x = self.emit(b, c, vars)?; b.ins().brif(x, loop_b, &[], exit, &[]); b.switch_to_block(loop_b); let bt = self.stmts(b, body, vars)?; if !bt { b.ins().jump(head, &[]); } b.switch_to_block(exit); b.seal_block(head); b.seal_block(loop_b); b.seal_block(exit); Ok(false) }
        Stmt::For(init, c, update, body) => { self.stmt(b, init, vars)?; let head = b.create_block(); let loop_b = b.create_block(); let exit = b.create_block(); b.ins().jump(head, &[]); b.switch_to_block(head); let x = self.emit(b, c, vars)?; b.ins().brif(x, loop_b, &[], exit, &[]); b.switch_to_block(loop_b); let bt = self.stmts(b, body, vars)?; if !bt { self.stmt(b, update, vars)?; b.ins().jump(head, &[]); } b.switch_to_block(exit); b.seal_block(head); b.seal_block(loop_b); b.seal_block(exit); Ok(false) }
    } }
    fn expr_kind(&self, e: &Expr) -> ir::IrType { match e { Expr::Num(_) => ir::IrType::Number, Expr::Bool(_) => ir::IrType::Boolean, Expr::Str(_) => ir::IrType::String, Expr::Array => ir::IrType::NumberArray, Expr::Closure(_) => ir::IrType::ClosureNumber, Expr::Index(_, _) => ir::IrType::Number, Expr::New(name, _) => ir::IrType::Class(leak_str(name)), Expr::FieldAccess(obj, field) => {
            if let Expr::Var(n) = obj.as_ref() {
                if let Some(ir::IrType::Class(cls_name)) = self.active_kinds.get(n) {
                    if let Some(cls) = self.class_defs.get(*cls_name) {
                        if let Some((_, fty)) = cls.fields.iter().find(|(fname, _)| fname == field) {
                            return *fty;
                        }
                    }
                }
            }
            ir::IrType::Number
        },
        Expr::MethodCall(obj, method, _) => {
            if let Expr::Var(n) = obj.as_ref() {
                if let Some(ir::IrType::Class(cls_name)) = self.active_kinds.get(n) {
                    let method_name = format!("{}.{}", cls_name, method);
                    if let Some(ret) = self.returns.get(&method_name) {
                        return *ret;
                    }
                }
            }
            ir::IrType::Number
        }
        Expr::Var(n) => self.active_kinds.get(n).copied().unwrap_or(ir::IrType::Any), Expr::Unary(op, _) => if *op == '!' { ir::IrType::Boolean } else { ir::IrType::Number }, Expr::Bin(a, op, c) => if op == "+" && self.expr_kind(a) == ir::IrType::String && self.expr_kind(c) == ir::IrType::String { ir::IrType::String } else if matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||") { ir::IrType::Boolean } else { ir::IrType::Number }, Expr::Call(n, _) | Expr::CallGeneric(n, _, _) => if n == "std.log" { ir::IrType::Void } else if n == "std.in" { ir::IrType::String } else if n == "std.parseNumber" { ir::IrType::Number } else if n == "std.toCString" { ir::IrType::Pointer } else if n == "std.funcPtr" { ir::IrType::Pointer } else if self.active_kinds.get(n) == Some(&ir::IrType::ClosureNumber) { ir::IrType::Number } else { self.returns.get(n).copied().unwrap_or(ir::IrType::Any) } } }
    fn emit(&mut self, b: &mut FunctionBuilder, e: &Expr, vars: &HashMap<String, Variable>) -> Result<Value, String> { match e {
        Expr::Num(x) => Ok(b.ins().iconst(types::I64, *x)), Expr::Bool(x) => Ok(b.ins().iconst(types::I64, i64::from(*x))), Expr::Array => { let callee = self.m.declare_func_in_func(self.array_new, b.func); let n = b.ins().iconst(types::I64, 1_000_000); let call = b.ins().call(callee, &[n]); Ok(b.func.dfg.inst_results(call)[0]) }, Expr::Index(a, i) => { let array = self.emit(b, a, vars)?; let index = self.emit(b, i, vars)?; let callee = self.m.declare_func_in_func(self.array_get, b.func); let call = b.ins().call(callee, &[array, index]); Ok(b.func.dfg.inst_results(call)[0]) }, Expr::Var(n) => Ok(b.use_var(*vars.get(n).ok_or_else(|| format!("unknown variable {n}"))?)),
        Expr::New(class_name, args) => {
            let cls = self.class_defs.get(class_name).ok_or_else(|| format!("unknown class {class_name}"))?;
            let field_count = cls.fields.len() as i64;
            let size = b.ins().iconst(types::I64, field_count * 8);
            let callee = self.m.declare_func_in_func(self.class_new, b.func);
            let call = b.ins().call(callee, &[size]);
            let ptr = b.func.dfg.inst_results(call)[0];
            let ctor_id = *self.funcs.get(&cls.constructor_name).ok_or_else(|| format!("unknown constructor {}", cls.constructor_name))?;
            let ctor_ref = self.m.declare_func_in_func(ctor_id, b.func);
            let mut ctor_args = vec![ptr];
            for a in args {
                ctor_args.push(self.emit(b, a, vars)?);
            }
            b.ins().call(ctor_ref, &ctor_args);
            Ok(ptr)
        }
        Expr::FieldAccess(obj, field) => {
            let obj_val = self.emit(b, obj, vars)?;
            let cls_name = match obj.as_ref() {
                Expr::Var(n) => self.active_kinds.get(n).and_then(|k| match k { ir::IrType::Class(c) => Some(*c), _ => None }),
                _ => None,
            }.ok_or_else(|| "field access on non-class object".to_string())?;
            let cls = self.class_defs.get(cls_name).ok_or_else(|| format!("unknown class {cls_name}"))?;
            let (field_idx, _) = cls.fields.iter().enumerate().find(|(_, (n, _))| n == field).ok_or_else(|| format!("unknown field {field}"))?;
            let offset = b.ins().iconst(types::I64, (field_idx * 8) as i64);
            let ptr = b.ins().iadd(obj_val, offset);
            Ok(b.ins().load(types::I64, MemFlags::new(), ptr, 0))
        }
        Expr::MethodCall(obj, method, args) => {
            let cls_name = match obj.as_ref() {
                Expr::Var(n) => self.active_kinds.get(n).and_then(|k| match k { ir::IrType::Class(c) => Some(*c), _ => None }),
                _ => None,
            }.ok_or_else(|| "method call on non-class object".to_string())?;
            let method_name = format!("{}.{}", cls_name, method);
            let id = *self.funcs.get(&method_name).ok_or_else(|| format!("unknown method {method_name}"))?;
            let obj_val = self.emit(b, obj, vars)?;
            let mut xs = vec![obj_val];
            for a in args { xs.push(self.emit(b, a, vars)?); }
            let callee = self.m.declare_func_in_func(id, b.func);
            let call = b.ins().call(callee, &xs);
            Ok(b.func.dfg.inst_results(call)[0])
        }
        Expr::Unary(op, x) => { let v = self.emit(b, x, vars)?; Ok(if *op == '-' { b.ins().ineg(v) } else { b.ins().icmp_imm(IntCC::Equal, v, 0) }) }
        Expr::Bin(a, op, c) => { let string_add = op == "+" && self.expr_kind(a) == ir::IrType::String && self.expr_kind(c) == ir::IrType::String; let x = self.emit(b, a, vars)?; let y = self.emit(b, c, vars)?; if string_add { let callee = self.m.declare_func_in_func(self.concat_str, b.func); let call = b.ins().call(callee, &[x, y]); return Ok(b.func.dfg.inst_results(call)[0]); } let v = match op.as_str() { "+" => b.ins().iadd(x, y), "-" => b.ins().isub(x, y), "*" => b.ins().imul(x, y), "/" => b.ins().sdiv(x, y), "%" => b.ins().srem(x, y), "==" => b.ins().icmp(IntCC::Equal, x, y), "!=" => b.ins().icmp(IntCC::NotEqual, x, y), "<" => b.ins().icmp(IntCC::SignedLessThan, x, y), "<=" => b.ins().icmp(IntCC::SignedLessThanOrEqual, x, y), ">" => b.ins().icmp(IntCC::SignedGreaterThan, x, y), ">=" => b.ins().icmp(IntCC::SignedGreaterThanOrEqual, x, y), "&&" => b.ins().band(x, y), "||" => b.ins().bor(x, y), _ => return Err(format!("unknown operator {op}")) }; let v = if matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") { b.ins().uextend(types::I64, v) } else { v }; Ok(v) }
        Expr::Call(n, a) | Expr::CallGeneric(n, _, a) => { if n == "std.log" { if a.len() != 1 { return Err("std.log accepts one expression".into()); } if let Expr::Str(s) = &a[0] { let id = if let Some(id) = self.strings.get(s) { *id } else { let id = self.m.declare_data(&format!("str{}", self.strings.len()), Linkage::Local, false, false).map_err(|e| e.to_string())?; let mut d = DataDescription::new(); d.define(s.as_bytes().to_vec().into_boxed_slice()); self.m.define_data(id, &d).map_err(|e| e.to_string())?; self.strings.insert(s.clone(), id); id }; let gv = self.m.declare_data_in_func(id, b.func); let p = b.ins().symbol_value(types::I64, gv); let l = b.ins().iconst(types::I64, s.len() as i64); let callee = self.m.declare_func_in_func(self.print_str, b.func); let call = b.ins().call(callee, &[p, l]); return Ok(b.func.dfg.inst_results(call)[0]); } let x = self.emit(b, &a[0], vars)?; let fid = if self.expr_kind(&a[0]) == ir::IrType::Boolean { self.print_bool } else { self.print_i64 }; let callee = self.m.declare_func_in_func(fid, b.func); let call = b.ins().call(callee, &[x]); Ok(b.func.dfg.inst_results(call)[0]) } else if n == "std.in" { let callee = self.m.declare_func_in_func(self.stdin_line, b.func); let call = b.ins().call(callee, &[]); Ok(b.func.dfg.inst_results(call)[0]) } else if n == "std.parseNumber" { if a.len() != 1 { return Err("std.parseNumber accepts one expression".into()); } let x = self.emit(b, &a[0], vars)?; let callee = self.m.declare_func_in_func(self.parse_number, b.func); let call = b.ins().call(callee, &[x]); Ok(b.func.dfg.inst_results(call)[0]) } else if n == "std.toCString" { if a.len() != 1 { return Err("std.toCString accepts one expression".into()); } let x = self.emit(b, &a[0], vars)?; let mask = b.ins().iconst(types::I64, i64::MAX); Ok(b.ins().band(x, mask)) } else if n == "std.funcPtr" { if a.len() != 1 { return Err("std.funcPtr accepts one expression".into()); } let func_name = if let Expr::Str(s) = &a[0] { s.clone() } else { return Err("std.funcPtr requires a string literal".into()); }; let id = *self.funcs.get(&func_name).ok_or_else(|| format!("std.funcPtr: unknown function \"{func_name}\""))?; let func_ref = self.m.declare_func_in_func(id, b.func); Ok(b.ins().func_addr(types::I64, func_ref)) } else if self.active_kinds.get(n) == Some(&ir::IrType::ClosureNumber) { let closure_val = b.use_var(*vars.get(n).ok_or_else(|| format!("unknown closure {n}"))?); let callee = self.m.declare_func_in_func(self.closure_call, b.func); let call = b.ins().call(callee, &[closure_val]); Ok(b.func.dfg.inst_results(call)[0]) } else if let Some(&fid) = self.extern_funcs.get(n) { let mut xs = Vec::new(); for a in a { xs.push(self.emit(b, a, vars)?); } let callee = self.m.declare_func_in_func(fid, b.func); let call = b.ins().call(callee, &xs); if self.extern_voids.contains(n) { Ok(b.ins().iconst(types::I64, 0)) } else { Ok(b.func.dfg.inst_results(call)[0]) } } else { let id = *self.funcs.get(n).ok_or_else(|| format!("unknown function {n}"))?; let mut xs = Vec::new(); for a in a { xs.push(self.emit(b, a, vars)?); } let callee = self.m.declare_func_in_func(id, b.func); let call = b.ins().call(callee, &xs); Ok(b.func.dfg.inst_results(call)[0]) } }
        Expr::Str(s) => { let id = if let Some(id) = self.strings.get(s) { *id } else { let id = self.m.declare_data(&format!("str{}", self.strings.len()), Linkage::Local, false, false).map_err(|e| e.to_string())?; let mut bytes = s.as_bytes().to_vec(); bytes.push(0); let mut d = DataDescription::new(); d.define(bytes.into_boxed_slice()); self.m.define_data(id, &d).map_err(|e| e.to_string())?; self.strings.insert(s.clone(), id); id }; let gv = self.m.declare_data_in_func(id, b.func); let p = b.ins().symbol_value(types::I64, gv); let tag = b.ins().iconst(types::I64, i64::MIN); Ok(b.ins().bor(p, tag)) }
        Expr::Closure(_) => { let defs = self.closure_defs.get(&self.current_func).ok_or_else(|| format!("no closure definitions for {}", self.current_func))?; let idx = *self.closure_index.entry(self.current_func.clone()).or_insert(0); let def = defs.get(idx).ok_or_else(|| format!("closure index {} out of range for {}", idx, self.current_func))?; self.closure_index.insert(self.current_func.clone(), idx + 1); let env_len = b.ins().iconst(types::I64, def.captures.len() as i64); let callee = self.m.declare_func_in_func(self.env_new, b.func); let call = b.ins().call(callee, &[env_len]); let env = b.func.dfg.inst_results(call)[0]; for (slot, capture) in def.captures.iter().enumerate() { let slot_val = b.ins().iconst(types::I64, slot as i64); let value = b.use_var(*vars.get(&capture.name).ok_or_else(|| format!("unknown capture `{}`", capture.name))?); if capture.mutable { let cell_callee = self.m.declare_func_in_func(self.cell_new, b.func); let cell_call = b.ins().call(cell_callee, &[value]); let cell_ptr = b.func.dfg.inst_results(cell_call)[0]; let cell_var = b.declare_var(types::I64); b.def_var(cell_var, cell_ptr); self.cell_vars.insert(capture.name.clone(), cell_var); self.active_cells.insert(capture.name.clone()); let set_callee = self.m.declare_func_in_func(self.env_set, b.func); b.ins().call(set_callee, &[env, slot_val, cell_ptr]); } else { let set_callee = self.m.declare_func_in_func(self.env_set, b.func); b.ins().call(set_callee, &[env, slot_val, value]); } } let func_ref = self.m.declare_func_in_func(self.closures[&def.name], b.func); let code_ptr = b.ins().func_addr(types::I64, func_ref); let new_callee = self.m.declare_func_in_func(self.closure_new, b.func); let call = b.ins().call(new_callee, &[code_ptr, env]); Ok(b.func.dfg.inst_results(call)[0]) }
    } }
}
