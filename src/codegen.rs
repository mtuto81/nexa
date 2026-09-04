use cranelift_codegen::ir::{types, AbiParam, ArgumentPurpose, Function, InstBuilder, MemFlags, Signature, Value};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::{HashMap, HashSet};

use crate::checker::ClassDef;
use crate::ir;
use crate::ir::Ty;
use crate::stdlib;
use crate::{leak_str, ClassDecl, Expr, ExternSig, Fun, GlobalDecl, Stmt};

fn inferred_ir_type(e: &Expr) -> ir::IrType { match e { Expr::Num(_) => ir::IrType::Number, Expr::Bool(_) => ir::IrType::Boolean, Expr::Closure(_) => ir::IrType::ClosureNumber, Expr::New(name, _) => ir::IrType::Class(leak_str(name)), Expr::FieldAccess(_, _) => ir::IrType::Number, _ => ir::IrType::Any } }
fn add_ref(name: &str, refs: &mut Vec<String>) { if !refs.iter().any(|x| x == name) { refs.push(name.to_string()); } }
fn collect_expr_refs(e: &Expr, refs: &mut Vec<String>, mutated: &mut HashSet<String>) -> Result<(), String> { match e { Expr::Var(n) => add_ref(n, refs), Expr::Bin(a, _, b) => { collect_expr_refs(a, refs, mutated)?; collect_expr_refs(b, refs, mutated)?; }, Expr::Unary(_, x) => collect_expr_refs(x, refs, mutated)?, Expr::Index(a, i) => { collect_expr_refs(a, refs, mutated)?; collect_expr_refs(i, refs, mutated)?; }, Expr::Call(_, args) | Expr::CallGeneric(_, _, args) => for a in args { collect_expr_refs(a, refs, mutated)?; }, Expr::FieldAccess(obj, _) => collect_expr_refs(obj, refs, mutated)?, Expr::MethodCall(obj, _, args) => { collect_expr_refs(obj, refs, mutated)?; for a in args { collect_expr_refs(a, refs, mutated)?; } }, Expr::Array(elems) => for a in elems { collect_expr_refs(a, refs, mutated)?; }, Expr::Closure(_) => return Err("nested closures are not supported in Nexa v1".into()), Expr::Num(_) | Expr::Bool(_) | Expr::Str(_) | Expr::New(_, _) => {} } Ok(()) }
fn collect_stmt_refs(s: &Stmt, refs: &mut Vec<String>, mutated: &mut HashSet<String>) -> Result<(), String> { match s { Stmt::Let(_, _, e) | Stmt::Return(e) | Stmt::Expr(e) => collect_expr_refs(e, refs, mutated)?, Stmt::Assign(n, e) => { add_ref(n, refs); mutated.insert(n.clone()); collect_expr_refs(e, refs, mutated)?; }, Stmt::FieldAssign(obj, _, e) => { collect_expr_refs(obj, refs, mutated)?; collect_expr_refs(e, refs, mutated)?; }, Stmt::IndexAssign(a, i, e) => { collect_expr_refs(a, refs, mutated)?; collect_expr_refs(i, refs, mutated)?; collect_expr_refs(e, refs, mutated)?; }, Stmt::Block(body) => for s in body { collect_stmt_refs(s, refs, mutated)?; }, Stmt::If(c, yes, no) => { collect_expr_refs(c, refs, mutated)?; for s in yes.iter().chain(no) { collect_stmt_refs(s, refs, mutated)?; } }, Stmt::While(c, body) => { collect_expr_refs(c, refs, mutated)?; for s in body { collect_stmt_refs(s, refs, mutated)?; } }, Stmt::For(init, c, update, body) => { collect_stmt_refs(init, refs, mutated)?; collect_expr_refs(c, refs, mutated)?; collect_stmt_refs(update, refs, mutated)?; for s in body { collect_stmt_refs(s, refs, mutated)?; } }, Stmt::ForOf(iter, bname, body) => { add_ref(bname, refs); collect_expr_refs(iter, refs, mutated)?; for s in body { collect_stmt_refs(s, refs, mutated)?; } } } Ok(()) }
fn find_closure_expr(e: &Expr, found: &mut Vec<Vec<Stmt>>) -> Result<(), String> { match e { Expr::Closure(body) => { found.push(body.clone()); }, Expr::Bin(a, _, b) => { find_closure_expr(a, found)?; find_closure_expr(b, found)?; }, Expr::Unary(_, x) => find_closure_expr(x, found)?, Expr::Index(a, i) => { find_closure_expr(a, found)?; find_closure_expr(i, found)?; }, Expr::Call(_, args) | Expr::CallGeneric(_, _, args) => for a in args { find_closure_expr(a, found)?; }, Expr::FieldAccess(obj, _) => find_closure_expr(obj, found)?, Expr::MethodCall(obj, _, args) => { find_closure_expr(obj, found)?; for a in args { find_closure_expr(a, found)?; } }, Expr::Array(elems) => for a in elems { find_closure_expr(a, found)?; }, Expr::Num(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Var(_) | Expr::New(_, _) => {} } Ok(()) }
fn find_closure_stmt(s: &Stmt, found: &mut Vec<Vec<Stmt>>) -> Result<(), String> { match s { Stmt::Let(_, _, e) | Stmt::Return(e) | Stmt::Expr(e) => find_closure_expr(e, found)?, Stmt::Assign(_, e) => find_closure_expr(e, found)?, Stmt::FieldAssign(obj, _, e) => { find_closure_expr(obj, found)?; find_closure_expr(e, found)?; }, Stmt::IndexAssign(a, i, e) => { find_closure_expr(a, found)?; find_closure_expr(i, found)?; find_closure_expr(e, found)?; }, Stmt::Block(body) => for s in body { find_closure_stmt(s, found)?; }, Stmt::If(c, yes, no) => { find_closure_expr(c, found)?; for s in yes.iter().chain(no) { find_closure_stmt(s, found)?; } }, Stmt::While(c, body) => { find_closure_expr(c, found)?; for s in body { find_closure_stmt(s, found)?; } }, Stmt::For(init, c, update, body) => { find_closure_stmt(init, found)?; find_closure_expr(c, found)?; find_closure_stmt(update, found)?; for s in body { find_closure_stmt(s, found)?; } }, Stmt::ForOf(iter, _, body) => { find_closure_expr(iter, found)?; for s in body { find_closure_stmt(s, found)?; } } } Ok(()) }
fn collect_outer_mutations(s: &Stmt, mutated: &mut HashSet<String>) { match s { Stmt::Assign(n, _) => { mutated.insert(n.clone()); }, Stmt::Block(body) => for x in body { collect_outer_mutations(x, mutated); }, Stmt::If(_, yes, no) => for x in yes.iter().chain(no) { collect_outer_mutations(x, mutated); }, Stmt::While(_, body) => for x in body { collect_outer_mutations(x, mutated); }, Stmt::For(init, _, update, body) => { collect_outer_mutations(init, mutated); collect_outer_mutations(update, mutated); for x in body { collect_outer_mutations(x, mutated); } }, Stmt::ForOf(_, _, body) => { for x in body { collect_outer_mutations(x, mutated); } }, Stmt::Let(_, _, _) | Stmt::Return(_) | Stmt::Expr(_) | Stmt::IndexAssign(_, _, _) | Stmt::FieldAssign(_, _, _) => {} } }

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
    from_cstring: FuncId,
    str_eq: FuncId,
    strlen: FuncId,
    char_at: FuncId,
    net_sockaddr_in: FuncId, net_socket: FuncId, net_bind: FuncId, net_listen: FuncId,
    net_accept: FuncId, net_recv: FuncId, net_send: FuncId, net_close: FuncId,
    proc_fork: FuncId, proc_exec1: FuncId, proc_exec2: FuncId, proc_pipe: FuncId,
    proc_pipe_read: FuncId, proc_pipe_write: FuncId, proc_wait: FuncId, proc_exit: FuncId,
    strings: HashMap<Vec<u8>, DataId>,
    class_new: FuncId,
    class_defs: HashMap<String, ClassDef>,
    extern_funcs: HashMap<String, FuncId>,
    extern_abis: HashMap<String, ExternAbi>,
    extern_rets: HashMap<String, ir::IrType>,
    globals: HashMap<String, GlobalSlot>,
}
struct GlobalSlot {
    data_id: DataId,
    ty: ir::IrType,
}

// ABI descriptors for extern "C" functions whose signatures involve
// fixed-layout struct (class) types passed/returned by value.
//
// System V AMD64 classification for INTEGER-only structs (this version's scope:
// every struct field is a single 8-byte slot, so a field IS an eightbyte):
//   - 1-2 eightbytes (<=16 bytes): register-passed.
//        args/returns occupy one GPR per eightbyte (RDI, RSI, ... / RAX, RDX).
//   - more than 2 eightbytes (>16 bytes): MEMORY class.
//        args are copied whole onto the caller's stack (Cranelift
//        ArgumentPurpose::StructArgument(size), sourced from the instance
//        pointer); returns are delivered through a hidden sret pointer in the
//        first GPR (ArgumentPurpose::StructReturn).
// Register allocation for args also accounts for the running count of consumed
// GPRs: a small struct that would not fit entirely in the remaining GPRs is
// promoted to the stack (all-or-nothing), exactly as gcc/LLVM do.
//
// LAYOUT-CONTROL GAP (do not rediscover from scratch): this ABI is only
// correct for structs whose fields are each a full, naturally 8-byte-aligned
// i64 -- the only layout Nexa classes can currently express (every field is a
// slot at field_idx*8). It does NOT reproduce arbitrary C layouts. Real-world
// structs like struct sockaddr_in mix 2-byte/4-byte fields and padding; a
// class cannot describe those, so C helpers like nexa_net_sockaddr_in remain
// necessary. Placing per-field sizes, padding, and alignment in the type
// system is the separate prerequisite that would let pure-Nexa structs replace
// those helpers.
#[derive(Clone, Copy, Debug)]
enum ExternParamAbi {
    Scalar,
    StructRegs(usize),
    StructStack,
}
#[derive(Clone, Debug)]
enum ExternRetAbi {
    Void,
    Scalar,
    StructRegs(&'static str, usize),
    Sret(&'static str),
}
#[derive(Clone, Debug)]
struct ExternAbi {
    params: Vec<ExternParamAbi>,
    ret: ExternRetAbi,
}
impl Compiler {
    pub(crate) fn new() -> Result<Self, String> { let isa = cranelift_codegen::isa::lookup(target_lexicon::HOST).map_err(|e| e.to_string())?.finish(settings::Flags::new(settings::builder())).map_err(|e| e.to_string())?; let b = ObjectBuilder::new(isa, "nexa", cranelift_module::default_libcall_names()).map_err(|e| e.to_string())?; let m = ObjectModule::new(b); let mut c = Self { m, funcs: HashMap::new(), returns: HashMap::new(), closures: HashMap::new(), closure_defs: HashMap::new(), active_kinds: HashMap::new(), active_cells: HashSet::new(), cell_vars: HashMap::new(), current_func: String::new(), closure_index: HashMap::new(), print_i64: FuncId::from_u32(0), print_bool: FuncId::from_u32(0), print_str: FuncId::from_u32(0), array_new: FuncId::from_u32(0), array_get: FuncId::from_u32(0), array_set: FuncId::from_u32(0), concat_str: FuncId::from_u32(0), env_new: FuncId::from_u32(0), env_get: FuncId::from_u32(0), env_set: FuncId::from_u32(0), cell_new: FuncId::from_u32(0), cell_get: FuncId::from_u32(0), cell_set: FuncId::from_u32(0), closure_new: FuncId::from_u32(0), closure_call: FuncId::from_u32(0), stdin_line: FuncId::from_u32(0), parse_number: FuncId::from_u32(0), from_cstring: FuncId::from_u32(0), str_eq: FuncId::from_u32(0), strlen: FuncId::from_u32(0), char_at: FuncId::from_u32(0), net_sockaddr_in: FuncId::from_u32(0), net_socket: FuncId::from_u32(0), net_bind: FuncId::from_u32(0), net_listen: FuncId::from_u32(0), net_accept: FuncId::from_u32(0), net_recv: FuncId::from_u32(0), net_send: FuncId::from_u32(0), net_close: FuncId::from_u32(0), proc_fork: FuncId::from_u32(0), proc_exec1: FuncId::from_u32(0), proc_exec2: FuncId::from_u32(0), proc_pipe: FuncId::from_u32(0), proc_pipe_read: FuncId::from_u32(0), proc_pipe_write: FuncId::from_u32(0), proc_wait: FuncId::from_u32(0), proc_exit: FuncId::from_u32(0), strings: HashMap::new(), class_new: FuncId::from_u32(0), class_defs: HashMap::new(), extern_funcs: HashMap::new(), extern_abis: HashMap::new(), extern_rets: HashMap::new(), globals: HashMap::new() }; c.print_i64 = c.import("nexa_print_i64", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.print_bool = c.import("nexa_print_bool", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.print_str = c.import("nexa_print_str", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_new = c.import("nexa_array_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_get = c.import("nexa_array_get", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_set = c.import("nexa_array_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.concat_str = c.import("nexa_concat_str", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_new = c.import("nexa_env_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_get = c.import("nexa_env_get", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_set = c.import("nexa_env_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_new = c.import("nexa_cell_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_get = c.import("nexa_cell_get", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_set = c.import("nexa_cell_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.closure_new = c.import("nexa_closure_new", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.closure_call = c.import("nexa_closure_call", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.stdin_line = c.import("nexa_stdin_line", vec![], vec![AbiParam::new(types::I64)])?; c.parse_number = c.import("nexa_std_parse_number", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.from_cstring = c.import("nexa_from_cstring", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.str_eq = c.import("nexa_str_eq", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.strlen = c.import("nexa_strlen", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.char_at = c.import("nexa_char_at", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.net_sockaddr_in = c.import("nexa_net_sockaddr_in", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.net_socket = c.import("nexa_net_socket", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.net_bind = c.import("nexa_net_bind", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.net_listen = c.import("nexa_net_listen", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.net_accept = c.import("nexa_net_accept", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.net_recv = c.import("nexa_net_recv", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.net_send = c.import("nexa_net_send", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.net_close = c.import("nexa_net_close", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.proc_fork = c.import("nexa_process_fork", vec![], vec![AbiParam::new(types::I64)])?; c.proc_exec1 = c.import("nexa_process_exec1", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.proc_exec2 = c.import("nexa_process_exec2", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.proc_pipe = c.import("nexa_process_pipe", vec![], vec![AbiParam::new(types::I64)])?; c.proc_pipe_read = c.import("nexa_process_pipe_read", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.proc_pipe_write = c.import("nexa_process_pipe_write", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.proc_wait = c.import("nexa_process_wait", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.proc_exit = c.import("nexa_process_exit", vec![AbiParam::new(types::I64)], vec![])?; c.class_new = c.import("nexa_class_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; Ok(c) }
    fn import(&mut self, n: &str, params: Vec<AbiParam>, returns: Vec<AbiParam>) -> Result<FuncId, String> { let mut s = Signature::new(self.m.isa().default_call_conv()); s.params = params; s.returns = returns; self.m.declare_function(n, Linkage::Import, &s).map_err(|e| e.to_string()) }
    /// Populate `class_defs` from the parsed class declarations. Called before
    /// `declare_externs` so struct (class) params/returns can be sized for the
    /// System V AMD64 by-value ABI; `compile` re-runs it (idempotent) so the
    /// maps are always consistent with what codegen emits.
    pub(crate) fn register_class_layouts(&mut self, classes: &[ClassDecl]) -> Result<(), String> {
        self.class_defs.clear();
        for c in classes {
            self.class_defs.insert(c.name.clone(), ClassDef {
                name: c.name.clone(),
                fields: c.fields.iter().map(|(n, t)| (n.clone(), *t)).collect(),
                constructor_name: c.constructor.name.clone(),
                method_names: c.methods.iter().map(|m| m.name.clone()).collect(),
            });
        }
        Ok(())
    }
    fn struct_field_count(&self, name: &str) -> Result<usize, String> {
        let cls = self.class_defs.get(name).ok_or_else(|| format!("unknown class/struct type `{name}` used across the extern ABI"))?;
        for (fname, fty) in &cls.fields {
            if !matches!(fty, ir::IrType::Number | ir::IrType::Boolean) {
                return Err(format!(
                    "extern-by-value struct {name} has non-integer field `{fname}` ({fty:?}); \
                     this version supports only number/boolean fields (each one full 8-byte slot) \
                     across the System V by-value ABI"
                ));
            }
        }
        if cls.fields.is_empty() {
            return Err(format!("extern-by-value struct {name} must declare at least one field"));
        }
        Ok(cls.fields.len())
    }
    pub(crate) fn declare_externs(&mut self, externs: &HashMap<String, ExternSig>) -> Result<(), String> {
        for (name, sig) in externs {
            let mut s = Signature::new(self.m.isa().default_call_conv());
            let mut abi = ExternAbi { params: Vec::new(), ret: ExternRetAbi::Void };
            let ret_ir;
            // System V register lanes used by the caller for this import. Starts
            // at 1 when a struct-return pointer (sret) occupies the first GPR.
            let mut next_gpr: usize;
            match sig.ret {
                Ty::Void => { ret_ir = ir::IrType::Void; next_gpr = 0; }
                Ty::Class(cname) => {
                    let n = self.struct_field_count(cname)?;
                    if n <= 2 {
                        s.returns = (0..n).map(|_| AbiParam::new(types::I64)).collect();
                        abi.ret = ExternRetAbi::StructRegs(cname, n);
                    } else {
                        // >16 bytes: MEMORY class, delivered via a hidden sret
                        // pointer passed as the first argument (RDI on System V).
                        s.params.push(AbiParam::special(types::I64, ArgumentPurpose::StructReturn));
                        abi.ret = ExternRetAbi::Sret(cname);
                    }
                    ret_ir = ir::IrType::Class(cname);
                    next_gpr = if n > 2 { 1 } else { 0 };
                }
                other => {
                    s.returns.push(AbiParam::new(types::I64));
                    abi.ret = ExternRetAbi::Scalar;
                    ret_ir = ir::ty_to_ir(other);
                    next_gpr = 0;
                }
            }
            for p in &sig.params {
                match p {
                    Ty::Class(cname) => {
                        let n = self.struct_field_count(cname)?;
                        if n <= 2 && next_gpr + n <= 6 {
                            // Small struct fits entirely in the remaining GPRs:
                            // one register per eightbyte.
                            for _ in 0..n {
                                s.params.push(AbiParam::new(types::I64));
                            }
                            next_gpr += n;
                            abi.params.push(ExternParamAbi::StructRegs(n));
                        } else {
                            // MEMORY class: the whole struct is copied onto the
                            // caller's stack (Cranelift StructArgument, sourced
                            // from the instance pointer); consumes no GPR.
                            s.params.push(AbiParam::special(types::I64, ArgumentPurpose::StructArgument((n * 8) as u32)));
                            abi.params.push(ExternParamAbi::StructStack);
                        }
                    }
                    Ty::Void => return Err(format!("extern function {name}: void is only valid as a return type")),
                    _ => {
                        s.params.push(AbiParam::new(types::I64));
                        if next_gpr < 6 { next_gpr += 1; }
                        abi.params.push(ExternParamAbi::Scalar);
                    }
                }
            }
            let id = self.m.declare_function(name, Linkage::Import, &s).map_err(|e| e.to_string())?;
            self.extern_funcs.insert(name.clone(), id);
            self.extern_abis.insert(name.clone(), abi);
            self.extern_rets.insert(name.clone(), ret_ir);
        }
        Ok(())
    }
    fn prepare_closures(&mut self, fs: &[Fun]) -> Result<(), String> { for f in fs { let mut outer = HashMap::new(); for (n, t) in f.params.iter().zip(&f.param_types) { outer.insert(n.clone(), *t); } let mut outer_mutated = HashSet::new(); for s in &f.body { collect_outer_mutations(s, &mut outer_mutated); if let Stmt::Let(n, annotation, e) = s { outer.insert(n.clone(), annotation.unwrap_or_else(|| inferred_ir_type(e))); } } let mut closure_bodies = Vec::new(); for s in &f.body { find_closure_stmt(s, &mut closure_bodies)?; } for body in closure_bodies { let mut refs = Vec::new(); let mut closure_mutated = HashSet::new(); for s in &body { collect_stmt_refs(s, &mut refs, &mut closure_mutated)?; }         let mut captures = Vec::new(); for name in refs { if self.globals.contains_key(&name) { continue; } let ty = *outer.get(&name).ok_or_else(|| format!("closure in {} references non-local `{name}`", f.name))?; if !matches!(ty, ir::IrType::Number | ir::IrType::Boolean) { return Err(format!("Nexa v1 closures only capture number/boolean values, `{name}` is {ty:?}")); } captures.push(Capture { name: name.clone(), ty, mutable: closure_mutated.contains(&name) || outer_mutated.contains(&name) }); } let name = format!("__nexa_closure_{}", self.closure_defs.values().map(|v| v.len()).sum::<usize>() + self.closure_defs.get(&f.name).map(|v| v.len()).unwrap_or(0)); self.closure_defs.entry(f.name.clone()).or_default().push(ClosureDef { name, parent: f.name.clone(), body, captures }); } } Ok(()) }
    pub(crate) fn compile(&mut self, classes: &[ClassDecl], fs: &[Fun], globals: &[GlobalDecl]) -> Result<(), String> {
        self.globals.clear();
        for g in globals {
            let id = self.m.declare_data(&format!("global_{}", g.name), Linkage::Local, true, false).map_err(|e| e.to_string())?;
            let mut d = DataDescription::new();
            d.define(vec![0u8; 8].into_boxed_slice());
            self.m.define_data(id, &d).map_err(|e| e.to_string())?;
            self.globals.insert(g.name.clone(), GlobalSlot { data_id: id, ty: g.ty });
        }
        self.prepare_closures(fs)?;
        self.register_class_layouts(classes)?;
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
        let global_init_id = if globals.is_empty() { None } else {
            let mut s = Signature::new(self.m.isa().default_call_conv());
            s.returns.push(AbiParam::new(types::I64));
            let id = self.m.declare_function(crate::GLOBAL_INIT_FN, Linkage::Local, &s).map_err(|e| e.to_string())?;
            self.funcs.insert(crate::GLOBAL_INIT_FN.to_string(), id);
            self.returns.insert(crate::GLOBAL_INIT_FN.to_string(), ir::IrType::Void);
            Some(id)
        };
        for c in classes {
            self.one(&c.constructor)?;
            for m in &c.methods {
                self.one(m)?;
            }
        }
        for f in fs { self.one(f)?; }
        if global_init_id.is_some() {
            let init_body: Vec<Stmt> = globals.iter().map(|g| Stmt::Assign(g.name.clone(), g.init.clone())).collect();
            let init_fun = Fun { name: crate::GLOBAL_INIT_FN.to_string(), params: vec![], param_types: vec![], return_type: ir::IrType::Void, body: init_body, type_param: None };
            self.one(&init_fun)?;
        }
        let all_closures: Vec<ClosureDef> = self.closure_defs.values().flat_map(|v| v.iter().cloned()).collect();
        for def in &all_closures { self.one_closure(def)?; }
        Ok(())
    }
    fn one_closure(&mut self, def: &ClosureDef) -> Result<(), String> { self.current_func = def.parent.clone(); let id = self.closures[&def.name]; let mut fun = Function::new(); let mut sig = Signature::new(self.m.isa().default_call_conv()); sig.params.push(AbiParam::new(types::I64)); sig.returns.push(AbiParam::new(types::I64)); fun.signature = sig; let mut cx = FunctionBuilderContext::new(); let mut b = FunctionBuilder::new(&mut fun, &mut cx); let entry = b.create_block(); b.append_block_params_for_function_params(entry); b.switch_to_block(entry); self.active_kinds.clear(); self.active_cells.clear(); self.cell_vars.clear(); let env = b.block_params(entry)[0]; let mut vars = HashMap::new(); for (slot, capture) in def.captures.iter().enumerate() { let v = b.declare_var(types::I64); let slot_value = b.ins().iconst(types::I64, slot as i64); let getter = self.m.declare_func_in_func(self.env_get, b.func); let call = b.ins().call(getter, &[env, slot_value]); let raw = b.func.dfg.inst_results(call)[0]; let value = if capture.mutable { let cell_var = b.declare_var(types::I64); b.def_var(cell_var, raw); self.cell_vars.insert(capture.name.clone(), cell_var); let cell_getter = self.m.declare_func_in_func(self.cell_get, b.func); let cell_call = b.ins().call(cell_getter, &[raw]); b.func.dfg.inst_results(cell_call)[0] } else { raw }; b.def_var(v, value); vars.insert(capture.name.clone(), v); self.active_kinds.insert(capture.name.clone(), capture.ty); if capture.mutable { self.active_cells.insert(capture.name.clone()); } } let terminated = self.stmts(&mut b, &def.body, &mut vars)?; if !terminated { let z = b.ins().iconst(types::I64, 0); b.ins().return_(&[z]); } b.seal_all_blocks(); b.finalize(); let mut ctx = cranelift_codegen::Context::for_function(fun); self.m.define_function(id, &mut ctx).map_err(|e| format!("{e:?}"))?; Ok(()) }
    fn one(&mut self, f: &Fun) -> Result<(), String> { self.current_func = f.name.clone(); let id = self.funcs[&f.name]; let mut fun = Function::new(); let mut sig = Signature::new(self.m.isa().default_call_conv()); sig.params = (0..f.params.len()).map(|_| AbiParam::new(types::I64)).collect(); sig.returns.push(AbiParam::new(types::I64)); fun.signature = sig; let mut cx = FunctionBuilderContext::new(); let mut b = FunctionBuilder::new(&mut fun, &mut cx); let entry = b.create_block(); b.append_block_params_for_function_params(entry); b.switch_to_block(entry); self.active_kinds.clear(); self.active_cells.clear(); self.cell_vars.clear(); let mut vars = HashMap::new(); for (i, n) in f.params.iter().enumerate() { let v = b.declare_var(types::I64); b.def_var(v, b.block_params(entry)[i]); vars.insert(n.clone(), v); self.active_kinds.insert(n.clone(), f.param_types.get(i).copied().unwrap_or(ir::IrType::Any)); } let terminated = self.stmts(&mut b, &f.body, &mut vars)?; if !terminated { let z = b.ins().iconst(types::I64, 0); b.ins().return_(&[z]); } b.seal_all_blocks(); b.finalize(); let mut ctx = cranelift_codegen::Context::for_function(fun); self.m.define_function(id, &mut ctx).map_err(|e| format!("{e:?}"))?; Ok(()) }
    fn stmts(&mut self, b: &mut FunctionBuilder, ss: &[Stmt], vars: &mut HashMap<String, Variable>) -> Result<bool, String> { for s in ss { if self.stmt(b, s, vars)? { return Ok(true); } } Ok(false) }
    fn stmt(&mut self, b: &mut FunctionBuilder, s: &Stmt, vars: &mut HashMap<String, Variable>) -> Result<bool, String> { match s {
        Stmt::Let(n, annotation, e) => { let v = b.declare_var(types::I64); let x = self.emit(b, e, vars)?; b.def_var(v, x); vars.insert(n.clone(), v); self.active_kinds.insert(n.clone(), annotation.unwrap_or_else(|| self.expr_kind(e))); Ok(false) }
        Stmt::Assign(n, e) => { let x = self.emit(b, e, vars)?; if let Some(slot) = self.globals.get(n) { let gv = self.m.declare_data_in_func(slot.data_id, b.func); let addr = b.ins().symbol_value(types::I64, gv); b.ins().store(MemFlags::new(), x, addr, 0); } else { let v = *vars.get(n).ok_or_else(|| format!("unknown variable {n}"))?; b.def_var(v, x); if let Some(&cell_var) = self.cell_vars.get(n) { let cell_ptr = b.use_var(cell_var); let callee = self.m.declare_func_in_func(self.cell_set, b.func); b.ins().call(callee, &[cell_ptr, x]); } } Ok(false) }
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
        Stmt::ForOf(iter, binder, body) => {
            // Desugar `for (const x of iterable) { body }` into the EXISTING
            // indexed C-style for(;;) loop, decided at compile time from the
            // statically-known type of the iterated expression:
            //   for (let __i = 0; __i < iterable.length; __i = __i + 1) {
            //       const x = iterable[__i];  body }
            // or
            //   for (let __i = 0; __i < std.strlen(iterable); __i = __i + 1) {
            //       const x = std.charAt(iterable, __i);  body }
            // Only number[] and string are iterable. The loop is then compiled
            // by delegating to the exact same Stmt::For path above, so this is
            // purely a compile-time syntactic lowering before Cranelift codegen.
            let i_var = "__i".to_string();
            let first = (*iter).clone();
            let i_ref = Expr::Var(i_var.clone());
            let step1 = Expr::Bin(Box::new(i_ref.clone()), "+".to_string(), Box::new(Expr::Num(1)));
            let init = Stmt::Let(i_var.clone(), Some(ir::IrType::Number), Expr::Num(0));
            let update = Stmt::Assign(i_var.clone(), step1);
            let kind = self.expr_kind(iter);
            let (cond, elem) = match kind {
                ir::IrType::NumberArray => {
                    let len = Expr::FieldAccess(Box::new(first.clone()), "length".to_string());
                    let cond = Expr::Bin(Box::new(i_ref.clone()), "<".to_string(), Box::new(len));
                    let elem = Expr::Index(Box::new(first), Box::new(i_ref));
                    (cond, elem)
                }
                ir::IrType::String => {
                    let len = Expr::Call("std.strlen".to_string(), vec![first.clone()]);
                    let cond = Expr::Bin(Box::new(i_ref.clone()), "<".to_string(), Box::new(len));
                    let elem = Expr::Call("std.charAt".to_string(), vec![first, i_ref]);
                    (cond, elem)
                }
                other => return Err(format!("cannot iterate over a value of type {other:?}; only number[] and string are iterable")),
            };
            let binder_ty = if kind == ir::IrType::NumberArray { Some(ir::IrType::Number) } else { Some(ir::IrType::String) };
            let mut wrapped = vec![Stmt::Let(binder.clone(), binder_ty, elem)];
            wrapped.extend(body.iter().cloned());
            let desugared = Stmt::For(Box::new(init), cond, Box::new(update), wrapped);
            self.stmt(b, &desugared, vars)
        }
    } }
    fn expr_kind(&self, e: &Expr) -> ir::IrType { match e { Expr::Num(_) => ir::IrType::Number, Expr::Bool(_) => ir::IrType::Boolean, Expr::Str(_) => ir::IrType::String, Expr::Array(_) => ir::IrType::NumberArray, Expr::Closure(_) => ir::IrType::ClosureNumber, Expr::Index(_, _) => ir::IrType::Number, Expr::New(name, _) => ir::IrType::Class(leak_str(name)), Expr::FieldAccess(obj, field) => {
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
        Expr::Var(n) => self.globals.get(n).map(|s| s.ty).unwrap_or_else(|| self.active_kinds.get(n).copied().unwrap_or(ir::IrType::Any)), Expr::Unary(op, _) => if *op == '!' { ir::IrType::Boolean } else { ir::IrType::Number }, Expr::Bin(a, op, c) => if op == "+" && self.expr_kind(a) == ir::IrType::String && self.expr_kind(c) == ir::IrType::String { ir::IrType::String } else if matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||") { ir::IrType::Boolean } else { ir::IrType::Number }, Expr::Call(n, _) | Expr::CallGeneric(n, _, _) => if let Some(op) = stdlib::StdOp::of(n) { op.ir_type() } else if self.active_kinds.get(n) == Some(&ir::IrType::ClosureNumber) { ir::IrType::Number } else if let Some(t) = self.extern_rets.get(n) { *t } else { self.returns.get(n).copied().unwrap_or(ir::IrType::Any) } } }
    /// Allocate a fresh, zeroed class instance for `class_name` (a calloc'd
    /// contiguous block of `field_count * 8` bytes): the runtime representation
    /// that doubles as the by-value struct storage at the extern boundary.
    fn alloc_instance(&mut self, b: &mut FunctionBuilder, class_name: &str) -> Result<Value, String> {
        let cls = self.class_defs.get(class_name).ok_or_else(|| format!("unknown class {class_name}"))?;
        let field_count = cls.fields.len() as i64;
        let size = b.ins().iconst(types::I64, field_count * 8);
        let callee = self.m.declare_func_in_func(self.class_new, b.func);
        let call = b.ins().call(callee, &[size]);
        Ok(b.func.dfg.inst_results(call)[0])
    }
    /// Emit a call to an extern "C" import, expanding every class-typed argument
    /// (and the return) according to the System V AMD64 by-value ABI recorded by
    /// `declare_externs`:
    ///   - small struct arg  (<=2 eightbytes, fits remaining GPRs): load each field
    ///     at slot offset and pass it as its own register value;
    ///   - large struct arg  (>2 eightbytes, or no room in the register window):
    ///     pass the instance pointer as a Cranelift StructArgument source, which
    ///     copies the struct bytes onto the caller's stack;
    ///   - small struct ret  (<=2 eightbytes): store the returned registers into a
    ///     fresh instance;
    ///   - large struct ret  (>2 eightbytes): allocate the instance up front and
    ///     pass it as the hidden sret pointer; the callee writes into it directly.
    fn emit_extern_call(&mut self, b: &mut FunctionBuilder, name: &str, fid: FuncId, args: &[Expr], vars: &HashMap<String, Variable>) -> Result<Value, String> {
        let abi = self.extern_abis.get(name).cloned().ok_or_else(|| format!("missing extern ABI descriptor for {name}"))?;
        let mut xs: Vec<Value> = Vec::new();
        if let ExternRetAbi::Sret(cname) = &abi.ret {
            xs.push(self.alloc_instance(b, cname)?);
        }
        for (i, e) in args.iter().enumerate() {
            match abi.params[i] {
                ExternParamAbi::Scalar => xs.push(self.emit(b, e, vars)?),
                ExternParamAbi::StructRegs(n) => {
                    let ptr = self.emit(b, e, vars)?;
                    for f in 0..n {
                        let off = b.ins().iconst(types::I64, (f * 8) as i64);
                        let addr = b.ins().iadd(ptr, off);
                        xs.push(b.ins().load(types::I64, MemFlags::new(), addr, 0));
                    }
                }
                ExternParamAbi::StructStack => xs.push(self.emit(b, e, vars)?),
            }
        }
        let callee = self.m.declare_func_in_func(fid, b.func);
        let call = b.ins().call(callee, &xs);
        match abi.ret {
            ExternRetAbi::Void => Ok(b.ins().iconst(types::I64, 0)),
            ExternRetAbi::Scalar => Ok(b.func.dfg.inst_results(call)[0]),
            ExternRetAbi::Sret(_) => Ok(xs[0]),
            ExternRetAbi::StructRegs(cname, n) => {
                let inst = self.alloc_instance(b, cname)?;
                for f in 0..n {
                    let v = b.func.dfg.inst_results(call)[f];
                    let off = b.ins().iconst(types::I64, (f * 8) as i64);
                    let addr = b.ins().iadd(inst, off);
                    b.ins().store(MemFlags::new(), v, addr, 0);
                }
                Ok(inst)
            }
        }
    }
    fn emit(&mut self, b: &mut FunctionBuilder, e: &Expr, vars: &HashMap<String, Variable>) -> Result<Value, String> { match e {
        Expr::Num(x) => Ok(b.ins().iconst(types::I64, *x)), Expr::Bool(x) => Ok(b.ins().iconst(types::I64, i64::from(*x))), Expr::Array(elems) => { let callee_new = self.m.declare_func_in_func(self.array_new, b.func); let n = b.ins().iconst(types::I64, elems.len() as i64); let call = b.ins().call(callee_new, &[n]); let arr = b.func.dfg.inst_results(call)[0]; let callee_set = self.m.declare_func_in_func(self.array_set, b.func); for (i, e) in elems.iter().enumerate() { let val = self.emit(b, e, vars)?; let idx = b.ins().iconst(types::I64, i as i64); b.ins().call(callee_set, &[arr, idx, val]); } Ok(arr) }, Expr::Index(a, i) => { let array = self.emit(b, a, vars)?; let index = self.emit(b, i, vars)?; let callee = self.m.declare_func_in_func(self.array_get, b.func); let call = b.ins().call(callee, &[array, index]); Ok(b.func.dfg.inst_results(call)[0]) }, Expr::Var(n) => { if let Some(slot) = self.globals.get(n) { let gv = self.m.declare_data_in_func(slot.data_id, b.func); let addr = b.ins().symbol_value(types::I64, gv); Ok(b.ins().load(types::I64, MemFlags::new(), addr, 0)) } else { Ok(b.use_var(*vars.get(n).ok_or_else(|| format!("unknown variable {n}"))?)) } },
        Expr::New(class_name, args) => {
            if class_name == "Array" {
                if args.len() != 1 { return Err("new Array<number>(n) requires exactly one size argument".into()); }
                let n = self.emit(b, &args[0], vars)?;
                let callee = self.m.declare_func_in_func(self.array_new, b.func);
                let call = b.ins().call(callee, &[n]);
                return Ok(b.func.dfg.inst_results(call)[0]);
            }
            let ptr = self.alloc_instance(b, class_name)?;
            let ctor_name = format!("{class_name}__constructor");
            let ctor_id = *self.funcs.get(&ctor_name).ok_or_else(|| format!("unknown constructor {ctor_name}"))?;
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
            let obj_kind = match obj.as_ref() {
                Expr::Var(n) => self.active_kinds.get(n).copied(),
                _ => None,
            };
            if field == "length" && (obj_kind == Some(ir::IrType::NumberArray) || obj_kind.is_none()) {
                /* arr.length: read the fixed length header at the single i64
                   immediately preceding the element buffer (array[-1]). */
                let minus = b.ins().iconst(types::I64, -8);
                let hdr_ptr = b.ins().iadd(obj_val, minus);
                return Ok(b.ins().load(types::I64, MemFlags::new(), hdr_ptr, 0));
            }
            let cls_name = obj_kind.and_then(|k| match k { ir::IrType::Class(c) => Some(c), _ => None }).ok_or_else(|| "field access on non-class object".to_string())?;
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
        Expr::Bin(a, op, c) => { let ta = self.expr_kind(a); let tc = self.expr_kind(c); let string_add = op == "+" && ta == ir::IrType::String && tc == ir::IrType::String; let string_cmp = (op == "==" || op == "!=") && ta == ir::IrType::String && tc == ir::IrType::String; let x = self.emit(b, a, vars)?; let y = self.emit(b, c, vars)?; if string_add { let callee = self.m.declare_func_in_func(self.concat_str, b.func); let call = b.ins().call(callee, &[x, y]); return Ok(b.func.dfg.inst_results(call)[0]); } if string_cmp { /* String == / != must compare CONTENT (length + bytes), not pointer identity. Two strings are equal when their bytes match even if they were built independently (a literal vs. a concat result live at different addresses). nexa_str_eq masks the tag bits, compares lengths, then bytes. */ let callee = self.m.declare_func_in_func(self.str_eq, b.func); let call = b.ins().call(callee, &[x, y]); let eq = b.func.dfg.inst_results(call)[0]; if op == "==" { return Ok(eq); } let nz = b.ins().icmp_imm(IntCC::Equal, eq, 0); return Ok(b.ins().uextend(types::I64, nz)); } let v = match op.as_str() { "+" => b.ins().iadd(x, y), "-" => b.ins().isub(x, y), "*" => b.ins().imul(x, y), "/" => b.ins().sdiv(x, y), "%" => b.ins().srem(x, y), "==" => b.ins().icmp(IntCC::Equal, x, y), "!=" => b.ins().icmp(IntCC::NotEqual, x, y), "<" => b.ins().icmp(IntCC::SignedLessThan, x, y), "<=" => b.ins().icmp(IntCC::SignedLessThanOrEqual, x, y), ">" => b.ins().icmp(IntCC::SignedGreaterThan, x, y), ">=" => b.ins().icmp(IntCC::SignedGreaterThanOrEqual, x, y), "&&" => b.ins().band(x, y), "||" => b.ins().bor(x, y), _ => return Err(format!("unknown operator {op}")) }; let v = if matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") { b.ins().uextend(types::I64, v) } else { v }; Ok(v) }
        Expr::Call(n, a) | Expr::CallGeneric(n, _, a) => { if let Some(op) = stdlib::StdOp::of(n) { stdlib::emit_std_call(self, b, op, a, vars) } else if self.active_kinds.get(n) == Some(&ir::IrType::ClosureNumber) { let closure_val = b.use_var(*vars.get(n).ok_or_else(|| format!("unknown closure {n}"))?); let callee = self.m.declare_func_in_func(self.closure_call, b.func); let call = b.ins().call(callee, &[closure_val]); Ok(b.func.dfg.inst_results(call)[0]) } else if let Some(&fid) = self.extern_funcs.get(n) { self.emit_extern_call(b, n, fid, a, vars) } else { let id = *self.funcs.get(n).ok_or_else(|| format!("unknown function {n}"))?; let mut xs = Vec::new(); for a in a { xs.push(self.emit(b, a, vars)?); } let callee = self.m.declare_func_in_func(id, b.func); let call = b.ins().call(callee, &xs); Ok(b.func.dfg.inst_results(call)[0]) } }
        Expr::Str(s) => { let id = if let Some(id) = self.strings.get(s) { *id } else { let id = self.m.declare_data(&format!("str{}", self.strings.len()), Linkage::Local, false, false).map_err(|e| e.to_string())?; let mut d = DataDescription::new(); let mut bytes = Vec::with_capacity(8 + s.len() + 1); bytes.extend_from_slice(&(s.len() as i64).to_ne_bytes()); bytes.extend_from_slice(s); bytes.push(0); d.define(bytes.into_boxed_slice()); self.m.define_data(id, &d).map_err(|e| e.to_string())?; let _ = self.strings.insert(s.clone(), id); id }; let gv = self.m.declare_data_in_func(id, b.func); let p = b.ins().symbol_value(types::I64, gv); let hdr = b.ins().iconst(types::I64, 8); let p = b.ins().iadd(p, hdr); let tag = b.ins().iconst(types::I64, i64::MIN); Ok(b.ins().bor(p, tag)) }
        Expr::Closure(_) => { let defs = self.closure_defs.get(&self.current_func).ok_or_else(|| format!("no closure definitions for {}", self.current_func))?; let idx = *self.closure_index.entry(self.current_func.clone()).or_insert(0); let def = defs.get(idx).ok_or_else(|| format!("closure index {} out of range for {}", idx, self.current_func))?; self.closure_index.insert(self.current_func.clone(), idx + 1); let env_len = b.ins().iconst(types::I64, def.captures.len() as i64); let callee = self.m.declare_func_in_func(self.env_new, b.func); let call = b.ins().call(callee, &[env_len]); let env = b.func.dfg.inst_results(call)[0]; for (slot, capture) in def.captures.iter().enumerate() { let slot_val = b.ins().iconst(types::I64, slot as i64); let value = b.use_var(*vars.get(&capture.name).ok_or_else(|| format!("unknown capture `{}`", capture.name))?); if capture.mutable { let cell_callee = self.m.declare_func_in_func(self.cell_new, b.func); let cell_call = b.ins().call(cell_callee, &[value]); let cell_ptr = b.func.dfg.inst_results(cell_call)[0]; let cell_var = b.declare_var(types::I64); b.def_var(cell_var, cell_ptr); self.cell_vars.insert(capture.name.clone(), cell_var); self.active_cells.insert(capture.name.clone()); let set_callee = self.m.declare_func_in_func(self.env_set, b.func); b.ins().call(set_callee, &[env, slot_val, cell_ptr]); } else { let set_callee = self.m.declare_func_in_func(self.env_set, b.func); b.ins().call(set_callee, &[env, slot_val, value]); } } let func_ref = self.m.declare_func_in_func(self.closures[&def.name], b.func); let code_ptr = b.ins().func_addr(types::I64, func_ref); let new_callee = self.m.declare_func_in_func(self.closure_new, b.func); let call = b.ins().call(new_callee, &[code_ptr, env]); Ok(b.func.dfg.inst_results(call)[0]) }
    } }
}


impl stdlib::StdEmitter for Compiler {
    fn emit_expr(&mut self, b: &mut FunctionBuilder, e: &Expr, vars: &HashMap<String, Variable>) -> Result<Value, String> {
        self.emit(b, e, vars)
    }
    fn expr_is_boolean(&self, e: &Expr) -> bool {
        self.expr_kind(e) == ir::IrType::Boolean
    }
    fn runtime_func(&self, f: stdlib::StdFunc) -> FuncId {
        match f {
            stdlib::StdFunc::PrintStr => self.print_str,
            stdlib::StdFunc::PrintI64 => self.print_i64,
            stdlib::StdFunc::PrintBool => self.print_bool,
            stdlib::StdFunc::StdInLine => self.stdin_line,
            stdlib::StdFunc::ParseNumber => self.parse_number,
            stdlib::StdFunc::FromCString => self.from_cstring,
            stdlib::StdFunc::StrLen => self.strlen,
            stdlib::StdFunc::CharAt => self.char_at,
            stdlib::StdFunc::NetSockaddrIn => self.net_sockaddr_in,
            stdlib::StdFunc::NetSocket => self.net_socket,
            stdlib::StdFunc::NetBind => self.net_bind,
            stdlib::StdFunc::NetListen => self.net_listen,
            stdlib::StdFunc::NetAccept => self.net_accept,
            stdlib::StdFunc::NetRecv => self.net_recv,
            stdlib::StdFunc::NetSend => self.net_send,
            stdlib::StdFunc::NetClose => self.net_close,
            stdlib::StdFunc::ProcFork => self.proc_fork,
            stdlib::StdFunc::ProcExec1 => self.proc_exec1,
            stdlib::StdFunc::ProcExec2 => self.proc_exec2,
            stdlib::StdFunc::ProcPipe => self.proc_pipe,
            stdlib::StdFunc::ProcPipeRead => self.proc_pipe_read,
            stdlib::StdFunc::ProcPipeWrite => self.proc_pipe_write,
            stdlib::StdFunc::ProcWait => self.proc_wait,
            stdlib::StdFunc::ProcExit => self.proc_exit,
        }
    }
    fn func_id(&self, name: &str) -> Option<FuncId> {
        self.funcs.get(name).copied()
    }
    fn intern_string(&mut self, s: &[u8], null_terminated: bool) -> Result<DataId, String> {
        if let Some(id) = self.strings.get(s) {
            return Ok(*id);
        }
        let id = self.m.declare_data(&format!("str{}", self.strings.len()), Linkage::Local, false, false).map_err(|e| e.to_string())?;
        let mut d = DataDescription::new();
        // Layout: [8-byte length header][bytes][NUL]. The length header is what
        // the runtime reads via ((int64_t*)str)[-1]; the caller advances the
        // data pointer by 8 so it points at char[0] (still NUL-terminated).
        let mut bytes = Vec::with_capacity(8 + s.len() + 1);
        bytes.extend_from_slice(&(s.len() as i64).to_ne_bytes());
        bytes.extend_from_slice(s);
        bytes.push(0);
        d.define(bytes.into_boxed_slice());
        self.m.define_data(id, &d).map_err(|e| e.to_string())?;
        self.strings.insert(s.to_vec(), id);
        Ok(id)
    }
    fn declare_data_in_func(&mut self, id: DataId, func: &mut Function) -> cranelift_codegen::ir::GlobalValue {
        self.m.declare_data_in_func(id, func)
    }
    fn declare_func_in_func(&mut self, id: FuncId, func: &mut Function) -> cranelift_codegen::ir::FuncRef {
        self.m.declare_func_in_func(id, func)
    }
}
