use cranelift_codegen::ir::{types, AbiParam, Function, InstBuilder, MemFlags, Signature, Value};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use swc_common::{sync::Lrc, FileName, SourceMap};
use swc_ecma_ast::{AssignOp, BinaryOp, Callee, ClassMember, Decl, EsVersion, Expr as SExpr, Lit, MemberProp, Module as SwcModule, ModuleItem, Pat, PropName, Stmt as SStmt, TsKeywordTypeKind, TsType};
use swc_ecma_parser::{lexer::Lexer, Parser as SwcParser, StringInput, Syntax, TsSyntax};
use std::{collections::{HashMap, HashSet}, env, fs, path::Path, process::Command};
mod ir;

#[derive(Clone, Copy, Debug, PartialEq, Eq)] enum Ty { Number, Boolean, String, NumberArray, Void, Any, Class(&'static str), ClosureNumber, Pointer }
#[derive(Clone, Debug)] struct FnSig { params: Vec<Ty>, ret: Ty }
#[derive(Clone, Copy, Debug)] enum GTy { Concrete(Ty), Param }
#[derive(Clone, Debug)] struct GenSig { tparam: String, params: Vec<GTy>, ret: GTy }
#[derive(Clone, Debug)] struct ClassDef { name: String, fields: Vec<(String, ir::IrType)>, constructor_name: String, method_names: Vec<String> }

fn ts_type(ty: &TsType) -> Result<Option<Ty>, String> {
    match ty {
        TsType::TsKeywordType(k) => Ok(Some(match k.kind { TsKeywordTypeKind::TsNumberKeyword => Ty::Number, TsKeywordTypeKind::TsBooleanKeyword => Ty::Boolean, TsKeywordTypeKind::TsStringKeyword => Ty::String, TsKeywordTypeKind::TsVoidKeyword => Ty::Void, TsKeywordTypeKind::TsAnyKeyword => return Err("Nexa does not compile any through the raw typed ABI; use a concrete type".into()), _ => return Err("Nexa supports only number, boolean, string, void, and number[] type annotations".into()) })),
        TsType::TsArrayType(a) => match &*a.elem_type { TsType::TsKeywordType(k) if k.kind == TsKeywordTypeKind::TsNumberKeyword => Ok(Some(Ty::NumberArray)), _ => Err("Nexa currently supports only number[] arrays".into()) },
        TsType::TsUnionOrIntersectionType(_) => Err("Nexa union/intersection type checking is not implemented yet".into()),
        TsType::TsParenthesizedType(p) => ts_type(&p.type_ann),
        TsType::TsTypeRef(r) => match (&r.type_name, r.type_params.as_deref()) {
            (swc_ecma_ast::TsEntityName::Ident(i), None) if &*i.sym == "Pointer" => Ok(Some(Ty::Pointer)),
            _ => Err("Nexa supports only the built-in Pointer type reference".into()),
        },
        TsType::TsFnOrConstructorType(swc_ecma_ast::TsFnOrConstructorType::TsFnType(f)) => {
            if !f.params.is_empty() { return Err("Nexa v1 closure types take no arguments".into()); }
            match &*f.type_ann.type_ann {
                TsType::TsKeywordType(k) if k.kind == TsKeywordTypeKind::TsNumberKeyword => Ok(Some(Ty::ClosureNumber)),
                _ => Err("Nexa v1 closures must return number".into()),
            }
        }
        _ => Err("Nexa type-level checker supports only scalar keyword types".into()),
    }
}

fn type_annotation(ann: Option<&swc_ecma_ast::TsTypeAnn>) -> Result<Option<Ty>, String> {
    let Some(ann) = ann else { return Ok(None); };
    ts_type(&ann.type_ann)
}

fn gty_of(t: &TsType, tparam: &str) -> Result<GTy, String> {
    if let TsType::TsTypeRef(r) = t {
        if let (swc_ecma_ast::TsEntityName::Ident(i), None) = (&r.type_name, r.type_params.as_deref()) {
            if *i.sym == *tparam { return Ok(GTy::Param); }
        }
    }
    match ts_type(t)? { Some(ty) => Ok(GTy::Concrete(ty)), None => Err("internal error: unresolved type annotation".into()) }
}

thread_local! { static ACTIVE_INST: std::cell::RefCell<Option<(String, Ty)>> = const { std::cell::RefCell::new(None) }; }

fn resolve_type_arg(t: &TsType) -> Result<Ty, String> {
    if let TsType::TsTypeRef(r) = t {
        if let (swc_ecma_ast::TsEntityName::Ident(i), None) = (&r.type_name, r.type_params.as_deref()) {
            let hit = ACTIVE_INST.with(|c| c.borrow().as_ref().and_then(|(name, ty)| (*i.sym == *name).then(|| *ty)));
            if let Some(ty) = hit { return Ok(ty); }
        }
    }
    ts_type(t)?.ok_or_else(|| "unsupported type argument".to_string())
}

fn compatible(expected: Ty, actual: Ty) -> bool { expected == actual }
fn required_type(ann: Option<&swc_ecma_ast::TsTypeAnn>, what: &str) -> Result<Ty, String> { type_annotation(ann)?.ok_or_else(|| format!("Nexa requires a concrete type for {what}; implicit any cannot enter native code")) }
fn leak_str(s: &str) -> &'static str { Box::leak(s.to_string().into_boxed_str()) }
fn ty_to_ir(ty: Ty) -> ir::IrType { match ty { Ty::Number => ir::IrType::Number, Ty::Boolean => ir::IrType::Boolean, Ty::String => ir::IrType::String, Ty::NumberArray => ir::IrType::NumberArray, Ty::ClosureNumber => ir::IrType::ClosureNumber, Ty::Class(name) => ir::IrType::Class(name), Ty::Void => ir::IrType::Void, Ty::Any => ir::IrType::Any, Ty::Pointer => ir::IrType::Pointer } }
fn ir_to_ty(ir_ty: ir::IrType) -> Ty { match ir_ty { ir::IrType::Number => Ty::Number, ir::IrType::Boolean => Ty::Boolean, ir::IrType::String => Ty::String, ir::IrType::NumberArray => Ty::NumberArray, ir::IrType::ClosureNumber => Ty::ClosureNumber, ir::IrType::Class(name) => Ty::Class(name), ir::IrType::Void => Ty::Void, ir::IrType::Any | ir::IrType::TParam => Ty::Any, ir::IrType::Pointer => Ty::Pointer } }

fn check_expr(e: &SExpr, env: &mut HashMap<String, Ty>, fns: &mut HashMap<String, FnSig>, classes: &mut HashMap<String, ClassDef>, generics: &HashMap<String, GenSig>, insts: &mut Vec<(String, Ty)>) -> Result<Ty, String> {
    match e {
        SExpr::Lit(Lit::Num(_)) => Ok(Ty::Number), SExpr::Lit(Lit::Bool(_)) => Ok(Ty::Boolean), SExpr::Lit(Lit::Str(_)) => Ok(Ty::String),
        SExpr::Lit(_) => Err("Nexa supports only number, boolean, and string literals".into()),
        SExpr::Ident(i) => env.get(i.sym.as_ref()).copied().ok_or_else(|| format!("unknown variable {}", i.sym)),
        SExpr::This(_) => env.get("this").copied().ok_or_else(|| "this used outside of class context".into()),
        SExpr::Paren(p) => check_expr(&p.expr, env, fns, classes, generics, insts), SExpr::TsAs(a) => check_expr(&a.expr, env, fns, classes, generics, insts), SExpr::TsNonNull(n) => check_expr(&n.expr, env, fns, classes, generics, insts),
        SExpr::Unary(u) => { let t = check_expr(&u.arg, env, fns, classes, generics, insts)?; match u.op { swc_ecma_ast::UnaryOp::Bang => { if t != Ty::Boolean && t != Ty::Any { return Err("! expects boolean".into()); } Ok(Ty::Boolean) }, swc_ecma_ast::UnaryOp::Minus | swc_ecma_ast::UnaryOp::Plus => { if t != Ty::Number && t != Ty::Any { return Err("numeric unary operator expects number".into()); } Ok(Ty::Number) }, _ => Err("unsupported unary operator in Nexa".into()) } }
        SExpr::Bin(b) => { let l = check_expr(&b.left, env, fns, classes, generics, insts)?; let r = check_expr(&b.right, env, fns, classes, generics, insts)?; match b.op { BinaryOp::Add => { if l == Ty::String && r == Ty::String { Ok(Ty::String) } else if compatible(Ty::Number, l) && compatible(Ty::Number, r) { Ok(Ty::Number) } else { Err("+ expects two numbers or two strings".into()) } }, BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => { if !compatible(Ty::Number, l) || !compatible(Ty::Number, r) { return Err("arithmetic operators expect numbers".into()); } Ok(Ty::Number) }, BinaryOp::LogicalAnd | BinaryOp::LogicalOr => { if !compatible(Ty::Boolean, l) || !compatible(Ty::Boolean, r) { return Err("logical operators expect booleans".into()); } Ok(Ty::Boolean) }, BinaryOp::EqEq | BinaryOp::NotEq | BinaryOp::EqEqEq | BinaryOp::NotEqEq | BinaryOp::Lt | BinaryOp::LtEq | BinaryOp::Gt | BinaryOp::GtEq => { if l != Ty::Any && r != Ty::Any && l != r { return Err("comparison operands must have compatible types".into()); } Ok(Ty::Boolean) }, _ => Err("unsupported binary operator in Nexa".into()) } }
        SExpr::Array(a) => { for x in a.elems.iter().flatten() { if check_expr(&x.expr, env, fns, classes, generics, insts)? != Ty::Number { return Err("Nexa arrays currently contain only numbers".into()); } } Ok(Ty::NumberArray) }
        SExpr::Member(m) => { let object = check_expr(&m.obj, env, fns, classes, generics, insts)?; match &m.prop { MemberProp::Computed(c) => { if object != Ty::NumberArray && object != Ty::Any { return Err("indexed access requires a number[]".into()); } if !compatible(Ty::Number, check_expr(&c.expr, env, fns, classes, generics, insts)?) { return Err("array index must be a number".into()); } Ok(Ty::Number) }, MemberProp::Ident(field_ident) => { if let Ty::Class(cls_name) = object { let cls = classes.get(cls_name).ok_or_else(|| format!("unknown class {cls_name}"))?; let field_name = field_ident.sym.to_string(); for (name, ty) in &cls.fields { if name == &field_name { return Ok(ir_to_ty(*ty)); } } return Err(format!("unknown field {field_name} on class {cls_name}")); } if object == Ty::Any { return Ok(Ty::Any); } Err("field access on non-class type".into()) }, _ => Err("unsupported member property".into()) } }
        SExpr::Assign(a) => { let new = check_expr(&a.right, env, fns, classes, generics, insts)?; match &a.left { swc_ecma_ast::AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Ident(i)) => { let name = i.id.sym.to_string(); let old = env.get(&name).copied().ok_or_else(|| format!("unknown variable {name}"))?; if a.op != AssignOp::Assign && old != Ty::Number { return Err("compound assignment requires number".into()); } if !compatible(old, new) { return Err(format!("cannot assign {new:?} to {old:?}")); } Ok(old) }, swc_ecma_ast::AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Member(m)) => { if a.op != AssignOp::Assign { return Err("compound array assignment is not implemented".into()); } let object = check_expr(&m.obj, env, fns, classes, generics, insts)?; match object { Ty::NumberArray | Ty::Any => { if let MemberProp::Computed(c) = &m.prop { if !compatible(Ty::Number, check_expr(&c.expr, env, fns, classes, generics, insts)?) { return Err("array index must be a number".into()); } } if !compatible(Ty::Number, new) { return Err("number[] elements must be numbers".into()); } Ok(Ty::Number) }, Ty::Class(cls_name) => { let cls = classes.get(cls_name).ok_or_else(|| format!("unknown class {cls_name}"))?; if let MemberProp::Ident(field_ident) = &m.prop { let field_name = field_ident.sym.to_string(); for (name, ty) in &cls.fields { if name == &field_name { if !compatible(ir_to_ty(*ty), new) { return Err(format!("cannot assign {new:?} to field {field_name} of type {:?}", ir_to_ty(*ty))); } return Ok(new); } } return Err(format!("unknown field {field_name} on class {cls_name}")); } Err("field assignment requires an identifier".into()) }, _ => Err("indexed assignment requires a number[]".into()) } }, _ => Err("Nexa assignments require a local identifier or array element".into()) } }
        SExpr::Call(c) => { let name = match &c.callee { Callee::Expr(x) => match &**x { SExpr::Ident(i) => i.sym.to_string(), SExpr::Member(m) if matches!(&m.obj.as_ref(), SExpr::Ident(i) if i.sym == "console") && matches!(&m.prop, MemberProp::Ident(i) if i.sym == "log") => "console.log".into(),                 SExpr::Member(m) if matches!(&m.obj.as_ref(), SExpr::Ident(i) if i.sym == "std") && matches!(&m.prop, MemberProp::Ident(i) if i.sym == "log" || i.sym == "in" || i.sym == "parseNumber" || i.sym == "toCString" || i.sym == "funcPtr") => { let MemberProp::Ident(pi) = &m.prop else { unreachable!() }; format!("std.{}", pi.sym) }, SExpr::Member(m) => { if let MemberProp::Ident(method_ident) = &m.prop { let method_name = method_ident.sym.to_string(); let obj_ty = check_expr(&m.obj, env, fns, classes, generics, insts)?; if let Ty::Class(cls_name) = obj_ty { let sig_name = format!("{}.{}", cls_name, method_name); let sig = fns.get(&sig_name).ok_or_else(|| format!("unknown method {}.{}", cls_name, method_name))?.clone(); if sig.params.len() - 1 != c.args.len() { return Err(format!("method {} expects {} arguments", sig_name, sig.params.len() - 1)); } for (p, a) in sig.params.iter().skip(1).zip(&c.args) { let t = check_expr(&a.expr, env, fns, classes, generics, insts)?; if !compatible(*p, t) { return Err(format!("argument type {t:?} does not match {p:?}")); } } return Ok(sig.ret); } } return Err("cannot call method on non-class type".into()); } _ => return Err("Nexa calls require a named function".into()) }, _ => return Err("unsupported call target".into()) }; let name = if name == "console.log" { "std.log".to_string() } else { name }; if name == "std.log" { if c.args.len() != 1 { return Err("std.log accepts one argument".into()); } let t = check_expr(&c.args[0].expr, env, fns, classes, generics, insts)?; if !matches!(t, Ty::Number | Ty::Boolean | Ty::String) { return Err(format!("std.log does not accept {t:?} values in the raw ABI")); } return Ok(Ty::Void); } if name == "std.in" { if !c.args.is_empty() { return Err("std.in accepts no arguments".into()); } return Ok(Ty::String); } if name == "std.parseNumber" { if c.args.len() != 1 { return Err("std.parseNumber accepts one argument".into()); } let t = check_expr(&c.args[0].expr, env, fns, classes, generics, insts)?; if t != Ty::String && t != Ty::Any { return Err(format!("std.parseNumber expects a string, got {t:?}")); } return Ok(Ty::Number); } // std.toCString: one-directional string→Pointer conversion. Masks the tag bit
// to produce a raw C char* pointer into the Nexa string's existing buffer.
// The returned pointer is only valid while the source string is alive — there is
// no cross-FFI ownership tracking yet, so this is a known lifetime hazard.
if name == "std.toCString" { if c.args.len() != 1 { return Err("std.toCString accepts one argument".into()); } let t = check_expr(&c.args[0].expr, env, fns, classes, generics, insts)?; if t != Ty::String && t != Ty::Any { return Err(format!("std.toCString expects a string, got {t:?}")); } return Ok(Ty::Pointer); } // std.funcPtr: compile-time resolution of a Nexa function's address as a C-compatible Pointer.
// Requires a string literal argument naming the target function.
// SAFETY: This emits a raw pointer to a Nexa-convention function.  On x86_64 Linux
// (System V AMD64 ABI) Nexa functions already use the default Cranelift calling
// convention which matches SystemV, so the pointer is directly callable from C.
// On platforms where default_call_conv() differs (Windows, Darwin), the pointer
// must NOT be passed to C without an adapter trampoline — revisiting this is
// required before v2 multi-platform support.
if name == "std.funcPtr" { if c.args.len() != 1 { return Err("std.funcPtr accepts one argument".into()); } let func_name = if let SExpr::Lit(Lit::Str(s)) = &*c.args[0].expr { s.value.as_str().unwrap_or("").to_string() } else { return Err("std.funcPtr requires a string literal naming the target function (e.g. std.funcPtr(\"main\"))".into()); }; if env.get(&func_name) == Some(&Ty::ClosureNumber) { return Err(format!("std.funcPtr cannot take the address of closure/capturing function \"{func_name}\"; closures are not representable as C function pointers")); } if !fns.contains_key(&func_name) { return Err(format!("std.funcPtr: unknown function \"{func_name}\"")); } return Ok(Ty::Pointer); } if c.type_args.is_some() && !generics.contains_key(&name) { return Err(format!("type arguments are only allowed when calling generic functions; {name} is not generic")); } if let Some(sig) = generics.get(&name) { let Some(targs) = c.type_args.as_deref().map(|t| t.params.as_slice()) else { return Err(format!("generic function {name} requires an explicit type instantiation at every call site, e.g. {name}<number>(...)")); }; if targs.len() != 1 { return Err("Nexa supports only a single type argument per generic call".into()); } let ty = resolve_type_arg(&targs[0])?; if matches!(ty, Ty::Void | Ty::Any) { return Err(format!("cannot instantiate {name} with void or any")); } let subst = |g: &GTy| match g { GTy::Concrete(t) => *t, GTy::Param => ty }; if sig.params.len() != c.args.len() { return Err(format!("function {name} expects {} arguments", sig.params.len())); } for (p, a) in sig.params.iter().zip(&c.args) { let expected = subst(p); let t = check_expr(&a.expr, env, fns, classes, generics, insts)?; if !compatible(expected, t) { return Err(format!("argument type {t:?} does not match {expected:?}")); } } insts.push((name.clone(), ty)); return Ok(subst(&sig.ret)); } if env.get(&name) == Some(&Ty::ClosureNumber) { if !c.args.is_empty() { return Err("Nexa v1 closures take no arguments".into()); } return Ok(Ty::Number); } let sig = fns.get(&name).ok_or_else(|| format!("unknown function {name}"))?.clone(); if sig.params.len() != c.args.len() { return Err(format!("function {name} expects {} arguments", sig.params.len())); } for (p, a) in sig.params.iter().zip(&c.args) { let t = check_expr(&a.expr, env, fns, classes, generics, insts)?; if !compatible(*p, t) { return Err(format!("argument type {t:?} does not match {p:?}")); } } Ok(sig.ret) }
        SExpr::New(n) => { if let SExpr::Ident(class_ident) = &*n.callee { let class_name = class_ident.sym.to_string(); let cls = classes.get(&class_name).ok_or_else(|| format!("unknown class {class_name}"))?; let ctor_name = &cls.constructor_name; let sig = fns.get(ctor_name).ok_or_else(|| format!("unknown constructor {ctor_name}"))?; if sig.params.len() != n.args.as_deref().unwrap_or(&[]).len() + 1 { return Err(format!("constructor {} expects {} arguments (including implicit this)", ctor_name, sig.params.len())); } Ok(Ty::Class(leak_str(&class_name))) } else { Err("new requires a class name".into()) } }
        SExpr::Arrow(a) => {
            if !a.params.is_empty() { return Err("Nexa v1 closures take no arguments".into()); }
            if a.type_params.is_some() { return Err("generic closures are not supported; use a generic function declaration".into()); }
            if let Some(rt) = &a.return_type { if ts_type(&rt.type_ann)? != Some(Ty::Number) { return Err("Nexa v1 closures must return number".into()); } }
            match &*a.body {
                swc_ecma_ast::ArrowFunctionBody::FunctionBody(b) => for s in &b.stmts { check_stmt(s, env, fns, classes, Ty::Number, generics, insts)?; },
                swc_ecma_ast::ArrowFunctionBody::Expr(_) => return Err("Nexa v1 closures require a block body".into()),
            }
            Ok(Ty::ClosureNumber)
        }
        _ => Err("unsupported expression in Nexa type checker".into()),
    }
}

fn check_stmt(s: &SStmt, env: &mut HashMap<String, Ty>, fns: &mut HashMap<String, FnSig>, classes: &mut HashMap<String, ClassDef>, ret: Ty, generics: &HashMap<String, GenSig>, insts: &mut Vec<(String, Ty)>) -> Result<(), String> {
    match s {
        SStmt::Decl(Decl::Var(v)) => for d in &v.decls { let Pat::Ident(i) = &d.name else { return Err("Nexa local declarations require identifiers".into()); }; let actual = d.init.as_ref().map(|x| check_expr(x, env, fns, classes, generics, insts)).transpose()?.unwrap_or(Ty::Any); if actual == Ty::Any { return Err(format!("Nexa requires an initializer or concrete annotation for {}", i.id.sym)); } let declared = type_annotation(i.type_ann.as_deref())?.unwrap_or(actual); if !compatible(declared, actual) { return Err(format!("initializer type {actual:?} does not match {declared:?}")); } env.insert(i.id.sym.to_string(), declared); },
        SStmt::Decl(Decl::Class(c)) => {
            let class_name = c.ident.sym.to_string();
            let mut fields = Vec::new();
            let constructor_name = format!("{class_name}__constructor");
            let mut method_names = Vec::new();
            for member in &c.class.body {
                match member {
                    ClassMember::ClassProp(prop) => {
                        let PropName::Ident(field_ident) = &prop.key else { return Err("class field must have identifier".into()); };
                        let field_ty = required_type(prop.type_ann.as_deref(), &format!("field {}.{}", class_name, field_ident.sym))?;
                        fields.push((field_ident.sym.to_string(), field_ty));
                    }
                    ClassMember::Constructor(ctor) => {
                        if let Some(body) = &ctor.body {
                            let mut ctor_env = HashMap::new();
                            ctor_env.insert("this".to_string(), Ty::Class(leak_str(&class_name)));
                            let mut ctor_param_tys = vec![Ty::Class(leak_str(&class_name))];
                            for p in &ctor.params {
                                let swc_ecma_ast::ParamOrTsParamProp::Param(param) = p else { return Err("constructor parameter must be identifier".into()); };
                                let Pat::Ident(param_ident) = &param.pat else { return Err("constructor parameter must be identifier".into()); };
                                let param_ty = required_type(param_ident.type_ann.as_deref(), &format!("constructor parameter {}.{}", class_name, param_ident.sym))?;
                                ctor_env.insert(param_ident.id.sym.to_string(), param_ty);
                                ctor_param_tys.push(param_ty);
                            }
                            fns.insert(constructor_name.clone(), FnSig { params: ctor_param_tys, ret: Ty::Void });
                            for s in &body.stmts {
                                check_stmt(s, &mut ctor_env, fns, classes, Ty::Void, generics, insts)?;
                            }
                        }
                    }
                    ClassMember::Method(method) => {
                        let PropName::Ident(method_ident) = &method.key else { return Err("method must have identifier".into()); };
                        let method_name = method_ident.sym.to_string();
                        let full_name = format!("{class_name}.{method_name}");
                        let mut method_env = HashMap::new();
                        method_env.insert("this".to_string(), Ty::Class(leak_str(&class_name)));
                        let mut param_tys = vec![Ty::Class(leak_str(&class_name))];
                        for p in &method.function.params {
                            let Pat::Ident(param_ident) = &p.pat else { return Err("method parameter must be identifier".into()); };
                            let param_ty = required_type(param_ident.type_ann.as_deref(), &format!("method parameter {}.{}", full_name, param_ident.sym))?;
                            method_env.insert(param_ident.id.sym.to_string(), param_ty);
                            param_tys.push(param_ty);
                        }
                        let ret_ty = required_type(method.function.return_type.as_deref(), &format!("method return type {}.{}", class_name, method_name))?;
                        fns.insert(full_name.clone(), FnSig { params: param_tys, ret: ret_ty });
                        method_names.push(full_name.clone());
                        if let Some(body) = &method.function.body {
                            for s in &body.stmts {
                                check_stmt(s, &mut method_env, fns, classes, ret_ty, generics, insts)?;
                            }
                        }
                    }
                    _ => return Err("unsupported class member in Nexa".into()),
                }
            }
            fns.insert(constructor_name.clone(), FnSig { params: vec![Ty::Class(leak_str(&class_name))], ret: Ty::Void });
            classes.insert(class_name.clone(), ClassDef { name: class_name, fields: fields.into_iter().map(|(n, t)| (n, ty_to_ir(t))).collect(), constructor_name, method_names });
        }
        SStmt::Expr(e) => { check_expr(&e.expr, env, fns, classes, generics, insts)?; },
        SStmt::Return(r) => { let actual = r.arg.as_ref().map(|x| check_expr(x, env, fns, classes, generics, insts)).transpose()?.unwrap_or(Ty::Void); if !compatible(ret, actual) { return Err(format!("return type {actual:?} does not match {ret:?}")); } },
        SStmt::Block(b) => for s in &b.stmts { check_stmt(s, env, fns, classes, ret, generics, insts)?; },
        SStmt::If(i) => { let t = check_expr(&i.test, env, fns, classes, generics, insts)?; if t != Ty::Boolean && t != Ty::Any { return Err("if condition must be boolean".into()); } check_stmt(&i.cons, env, fns, classes, ret, generics, insts)?; if let Some(a) = &i.alt { check_stmt(a, env, fns, classes, ret, generics, insts)?; } },
        SStmt::While(w) => { let t = check_expr(&w.test, env, fns, classes, generics, insts)?; if t != Ty::Boolean && t != Ty::Any { return Err("while condition must be boolean".into()); } check_stmt(&w.body, env, fns, classes, ret, generics, insts)?; },
        SStmt::For(f) => { if let Some(init) = &f.init { match init { swc_ecma_ast::VarDeclOrExpr::VarDecl(v) => for d in &v.decls { let Pat::Ident(i) = &d.name else { return Err("Nexa for declarations require identifiers".into()); }; let actual = d.init.as_ref().map(|x| check_expr(x, env, fns, classes, generics, insts)).transpose()?.unwrap_or(Ty::Any); let declared = type_annotation(i.type_ann.as_deref())?.unwrap_or(actual); if !compatible(declared, actual) { return Err(format!("initializer type {actual:?} does not match {declared:?}")); } env.insert(i.id.sym.to_string(), declared); }, swc_ecma_ast::VarDeclOrExpr::Expr(e) => { check_expr(e, env, fns, classes, generics, insts)?; } } } if let Some(test) = &f.test { let t = check_expr(test, env, fns, classes, generics, insts)?; if t != Ty::Boolean && t != Ty::Any { return Err("for condition must be boolean".into()); } } if let Some(update) = &f.update { check_expr(update, env, fns, classes, generics, insts)?; } check_stmt(&f.body, env, fns, classes, ret, generics, insts)?; },
        SStmt::Empty(_) => {},
        _ => return Err("unsupported statement in Nexa type checker".into()),
    } Ok(())
}

fn check_module(module: &SwcModule) -> Result<(), String> { check_module_with_externs(module, &HashMap::new()) }

fn check_module_with_externs(module: &SwcModule, externs: &HashMap<String, ExternSig>) -> Result<(), String> {
    let mut fns = HashMap::new();
    for (name, sig) in externs {
        fns.insert(name.clone(), FnSig { params: sig.params.clone(), ret: sig.ret });
    }
    let mut classes = HashMap::new();
    let mut generics: HashMap<String, GenSig> = HashMap::new();
    let mut generic_bodies: HashMap<String, &swc_ecma_ast::Function> = HashMap::new();
    let mut insts: Vec<(String, Ty)> = Vec::new();
    for item in &module.body {
        match item {
            ModuleItem::Stmt(SStmt::Decl(Decl::Fn(f))) => {
                let name = f.ident.sym.to_string();
                if let Some(tp_decl) = &f.function.type_params {
                    if tp_decl.params.len() != 1 { return Err("Nexa supports only a single type parameter per generic function".into()); }
                    let tp = &tp_decl.params[0];
                    if tp.constraint.is_some() { return Err(format!("type parameter bounds are not supported on generic function {name}")); }
                    if tp.default.is_some() { return Err(format!("type parameter defaults are not supported on generic function {name}")); }
                    if generics.contains_key(&name) || fns.contains_key(&name) { return Err(format!("duplicate function definition {name}")); }
                    let tparam = tp.name.sym.to_string();
                    let params = f.function.params.iter().map(|p| match &p.pat {
                        Pat::Ident(i) => i.type_ann.as_deref().map(|a| gty_of(&a.type_ann, &tparam)).transpose()?.ok_or_else(|| format!("Nexa requires a concrete type for parameter {} of {name}", i.id.sym)),
                        _ => Err("Nexa function parameters require identifiers".into()),
                    }).collect::<Result<Vec<_>, String>>()?;
                    let ret = f.function.return_type.as_deref().map(|a| gty_of(&a.type_ann, &tparam)).transpose()?.ok_or_else(|| format!("Nexa requires an explicit return type for generic function {name}"))?;
                    generics.insert(name.clone(), GenSig { tparam, params, ret });
                    generic_bodies.insert(name, &f.function);
                } else {
                    if generics.contains_key(&name) { return Err(format!("duplicate function definition {name}")); }
                    let params = f.function.params.iter().map(|p| match &p.pat { Pat::Ident(i) => required_type(i.type_ann.as_deref(), "function parameter"), _ => Err("Nexa function parameters require identifiers".into()) }).collect::<Result<Vec<_>, String>>()?;
                    let ret = required_type(f.function.return_type.as_deref(), "function return type")?;
                    fns.insert(name, FnSig { params, ret });
                }
            }
            ModuleItem::Stmt(SStmt::Decl(Decl::Class(c))) => {
                let class_name = c.ident.sym.to_string();
                let mut fields = Vec::new();
                let constructor_name = format!("{class_name}__constructor");
                let mut method_names = Vec::new();
                for member in &c.class.body {
                    match member {
                        ClassMember::ClassProp(prop) => {
                            let PropName::Ident(field_ident) = &prop.key else { return Err("class field must have identifier".into()); };
                            let field_ty = required_type(prop.type_ann.as_deref(), &format!("field {}.{}", class_name, field_ident.sym))?;
                            fields.push((field_ident.sym.to_string(), field_ty));
                        }
                        ClassMember::Method(method) => {
                            let PropName::Ident(method_ident) = &method.key else { return Err("method must have identifier".into()); };
                            if method.function.type_params.is_some() { return Err("generic methods are not supported; use a standalone generic function".into()); }
                            let method_name = method_ident.sym.to_string();
                            let full_name = format!("{class_name}.{method_name}");
                            let mut param_tys = vec![Ty::Class(leak_str(&class_name))];
                            for p in &method.function.params {
                                let Pat::Ident(param_ident) = &p.pat else { return Err("method parameter must be identifier".into()); };
                                let param_ty = required_type(param_ident.type_ann.as_deref(), &format!("method parameter {}.{}", full_name, param_ident.sym))?;
                                param_tys.push(param_ty);
                            }
                            let ret_ty = required_type(method.function.return_type.as_deref(), &format!("method return type {}.{}", class_name, method_name))?;
                            fns.insert(full_name.clone(), FnSig { params: param_tys, ret: ret_ty });
                            method_names.push(full_name);
                        }
                        ClassMember::Constructor(ctor) => {
                            let mut ctor_param_tys = vec![Ty::Class(leak_str(&class_name))];
                            for p in &ctor.params {
                                if let swc_ecma_ast::ParamOrTsParamProp::Param(param) = p {
                                    if let Pat::Ident(param_ident) = &param.pat {
                                        let param_ty = required_type(param_ident.type_ann.as_deref(), &format!("constructor parameter {}.{}", class_name, param_ident.sym))?;
                                        ctor_param_tys.push(param_ty);
                                    }
                                }
                            }
                            fns.insert(constructor_name.clone(), FnSig { params: ctor_param_tys, ret: Ty::Void });
                        }
                        _ => return Err("unsupported class member in Nexa".into()),
                    }
                }
            fns.entry(constructor_name.clone()).or_insert_with(|| FnSig { params: vec![Ty::Class(leak_str(&class_name))], ret: Ty::Void });
                classes.insert(class_name.clone(), ClassDef { name: class_name, fields: fields.into_iter().map(|(n, t)| (n, ty_to_ir(t))).collect(), constructor_name, method_names });
            }
            _ => {}
        }
    }
    for item in &module.body {
        match item {
            ModuleItem::Stmt(SStmt::Decl(Decl::Fn(f))) => {
                if f.function.type_params.is_some() { continue; }
                let mut env = HashMap::new();
                for p in &f.function.params {
                    let Pat::Ident(i) = &p.pat else { return Err("Nexa function parameters require identifiers".into()); };
                    env.insert(i.id.sym.to_string(), required_type(i.type_ann.as_deref(), "function parameter")?);
                }
                let ret = required_type(f.function.return_type.as_deref(), "function return type")?;
                if let Some(body) = &f.function.body {
                    for s in &body.stmts {
                        check_stmt(s, &mut env, &mut fns, &mut classes, ret, &generics, &mut insts)?;
                    }
                }
            }
            ModuleItem::Stmt(SStmt::Decl(Decl::Class(c))) => {
                let class_name = c.ident.sym.to_string();
                for member in &c.class.body {
                    if let ClassMember::Constructor(ctor) = member {
                        if let Some(body) = &ctor.body {
                            let mut ctor_env = HashMap::new();
                            ctor_env.insert("this".to_string(), Ty::Class(leak_str(&class_name)));
                            for p in &ctor.params {
                                if let swc_ecma_ast::ParamOrTsParamProp::Param(param) = p {
                                    if let Pat::Ident(param_ident) = &param.pat {
                                        let param_ty = required_type(param_ident.type_ann.as_deref(), &format!("constructor parameter {}.{}", class_name, param_ident.sym))?;
                                        ctor_env.insert(param_ident.id.sym.to_string(), param_ty);
                                    }
                                }
                            }
                            for s in &body.stmts {
                                check_stmt(s, &mut ctor_env, &mut fns, &mut classes, Ty::Void, &generics, &mut insts)?;
                            }
                        }
                    }
                    if let ClassMember::Method(method) = member {
                        if method.function.type_params.is_some() { return Err("generic methods are not supported; use a standalone generic function".into()); }
                        let PropName::Ident(method_ident) = &method.key else { return Err("method must have identifier".into()); };
                        let method_name = method_ident.sym.to_string();
                        let full_name = format!("{class_name}.{method_name}");
                        let mut method_env = HashMap::new();
                        method_env.insert("this".to_string(), Ty::Class(leak_str(&class_name)));
                        for p in &method.function.params {
                            let Pat::Ident(param_ident) = &p.pat else { return Err("method parameter must be identifier".into()); };
                            let param_ty = required_type(param_ident.type_ann.as_deref(), &format!("method parameter {}.{}", full_name, param_ident.sym))?;
                            method_env.insert(param_ident.id.sym.to_string(), param_ty);
                        }
                        let ret_ty = required_type(method.function.return_type.as_deref(), &format!("method return type {}.{}", class_name, method_name))?;
                        if let Some(body) = &method.function.body {
                            for s in &body.stmts {
                                check_stmt(s, &mut method_env, &mut fns, &mut classes, ret_ty, &generics, &mut insts)?;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    let mut idx = 0;
    while idx < insts.len() {
        let (gname, ty) = insts[idx].clone();
        idx += 1;
        let Some(sig) = generics.get(&gname).cloned() else { continue };
        let Some(function) = generic_bodies.get(&gname).copied() else { continue };
        let subst = |g: GTy| match g { GTy::Concrete(t) => t, GTy::Param => ty };
        let mut env = HashMap::new();
        for (p, param) in sig.params.iter().zip(&function.params) {
            let Pat::Ident(i) = &param.pat else { return Err("Nexa function parameters require identifiers".into()); };
            env.insert(i.id.sym.to_string(), subst(*p));
        }
        let ret = subst(sig.ret);
        ACTIVE_INST.with(|c| *c.borrow_mut() = Some((sig.tparam.clone(), ty)));
        let body_result = (|| -> Result<(), String> {
            if let Some(body) = &function.body {
                for s in &body.stmts {
                    check_stmt(s, &mut env, &mut fns, &mut classes, ret, &generics, &mut insts)?;
                }
            }
            Ok(())
        })();
        ACTIVE_INST.with(|c| *c.borrow_mut() = None);
        body_result?;
    }
    Ok(())
}

fn parse_swc_module(source: &str, filename: &str) -> Result<SwcModule, String> {
    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(FileName::Custom(filename.into()).into(), source.to_string());
    let lexer = Lexer::new(
        Syntax::Typescript(TsSyntax { tsx: false, decorators: true, ..Default::default() }),
        EsVersion::latest(),
        StringInput::from(&*fm),
        None,
    );
    let mut parser = SwcParser::new_from(lexer);
    let module = parser.parse_module().map_err(|e| format!("TypeScript parse error: {e:?}"))?;
    let errors = parser.take_errors();
    if let Some(error) = errors.into_iter().next() { return Err(format!("TypeScript parse error: {error:?}")); }
    Ok(module)
}

fn parse_typescript(source: &str, filename: &str) -> Result<(), String> {
    let (externs, clean) = extract_extern_blocks(source)?;
    let swc_src = blank_unsafe_markers(&clean)?;
    let module = parse_swc_module(&swc_src, filename)?;
    check_module_with_externs(&module, &externs)
}

#[derive(Clone, Debug)]
struct ExternSig { params: Vec<Ty>, ret: Ty }

fn is_ident_byte(c: u8) -> bool { c.is_ascii_alphanumeric() || c == b'_' }

fn skip_string(b: &[u8], mut i: usize) -> usize {
    let q = b[i];
    i += 1;
    while i < b.len() && b[i] != q { if b[i] == b'\\' { i += 1; } i += 1; }
    (i + 1).min(b.len())
}

fn find_word_from(s: &str, keyword: &str, from: usize) -> Option<usize> {
    let b = s.as_bytes();
    let kw = keyword.as_bytes();
    let mut i = from;
    while i < b.len() {
        if b[i] == b'"' || b[i] == b'\'' { i = skip_string(b, i); continue; }
        if i + 1 < b.len() && b[i] == b'/' && b[i + 1] == b'/' { while i < b.len() && b[i] != b'\n' { i += 1; } continue; }
        if i + 1 < b.len() && b[i] == b'/' && b[i + 1] == b'*' { i += 2; while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') { i += 1; } i += 2; continue; }
        if b[i] == kw[0] && (i == 0 || !is_ident_byte(b[i - 1])) && i + kw.len() <= b.len() && &b[i..i + kw.len()] == kw && (i + kw.len() == b.len() || !is_ident_byte(b[i + kw.len()])) {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn match_brace(s: &str, open: usize) -> Result<usize, String> {
    let b = s.as_bytes();
    let mut depth = 0usize;
    let mut i = open;
    while i < b.len() {
        if b[i] == b'"' || b[i] == b'\'' { i = skip_string(b, i); continue; }
        if i + 1 < b.len() && b[i] == b'/' && b[i + 1] == b'/' { while i < b.len() && b[i] != b'\n' { i += 1; } continue; }
        if i + 1 < b.len() && b[i] == b'/' && b[i + 1] == b'*' { i += 2; while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') { i += 1; } i += 2; continue; }
        if b[i] == b'{' { depth += 1; }
        if b[i] == b'}' { depth -= 1; if depth == 0 { return Ok(i); } }
        i += 1;
    }
    Err("unbalanced braces".into())
}

fn extern_scalar_ty(name: &str, ret: bool) -> Result<Ty, String> {
    match name {
        "number" => Ok(Ty::Number),
        "boolean" => Ok(Ty::Boolean),
        "Pointer" => Ok(Ty::Pointer),
        "void" if ret => Ok(Ty::Void),
        _ => Err(format!("type `{name}` is not allowed across the extern ABI; use number, boolean, Pointer{}", if ret { ", or void" } else { "" })),
    }
}

fn parse_extern_block(inner: &str) -> Result<Vec<(String, ExternSig)>, String> {
    let toks = lex(inner)?;
    let mut p = 0usize;
    let peek = |p: usize| -> Option<&Tok> { toks.get(p) };
    let mut out = Vec::new();
    while !matches!(peek(p), None | Some(Tok::Eof)) {
        if !matches!(peek(p), Some(Tok::Id(k)) if k == "function") { return Err("extern \"C\" blocks may contain only function signatures".into()); }
        p += 1;
        let name = match peek(p) { Some(Tok::Id(n)) => n.clone(), _ => return Err("expected function name in extern declaration".into()) };
        p += 1;
        if !matches!(peek(p), Some(Tok::LParen)) { return Err(format!("expected ( after extern function {name}")); }
        p += 1;
        let mut params = Vec::new();
        if !matches!(peek(p), Some(Tok::RParen)) {
            loop {
                if !matches!(peek(p), Some(Tok::Id(_))) { return Err(format!("expected parameter name in extern function {name}")); }
                p += 1;
                if !matches!(peek(p), Some(Tok::Colon)) { return Err(format!("extern parameters require type annotations in {name}")); }
                p += 1;
                let t = match peek(p) { Some(Tok::Id(t)) => t.clone(), _ => return Err(format!("extern parameters require type annotations in {name}")) };
                p += 1;
                params.push(extern_scalar_ty(&t, false)?);
                match peek(p) { Some(Tok::Comma) => p += 1, Some(Tok::RParen) => break, _ => return Err(format!("expected , or ) in extern function {name}")) }
            }
        }
        p += 1;
        if !matches!(peek(p), Some(Tok::Colon)) { return Err(format!("extern function {name} requires a return type annotation")); }
        p += 1;
        let r = match peek(p) { Some(Tok::Id(t)) => t.clone(), _ => return Err(format!("extern function {name} requires a return type annotation")) };
        p += 1;
        let ret = extern_scalar_ty(&r, true)?;
        if !matches!(peek(p), Some(Tok::Semi)) { return Err(format!("expected ; after extern declaration of {name}")); }
        p += 1;
        out.push((name, ExternSig { params, ret }));
    }
    Ok(out)
}

fn extract_extern_blocks(source: &str) -> Result<(HashMap<String, ExternSig>, String), String> {
    let mut out: Vec<u8> = source.as_bytes().to_vec();
    let mut externs: HashMap<String, ExternSig> = HashMap::new();
    let mut search_from = 0usize;
    while let Some(start) = find_word_from(source, "extern", search_from) {
        let b = source.as_bytes();
        let mut i = start + "extern".len();
        while i < b.len() && b[i].is_ascii_whitespace() { i += 1; }
        if i >= b.len() || b[i] != b'"' { return Err("expected an ABI string literal after extern".into()); }
        i += 1;
        let q = i;
        while i < b.len() && b[i] != b'"' { i += 1; }
        if i >= b.len() { return Err("unterminated ABI string after extern".into()); }
        let abi = &source[q..i];
        i += 1;
        if abi != "C" { return Err(format!("unsupported extern ABI \"{abi}\"; only \"C\" is supported")); }
        while i < b.len() && b[i].is_ascii_whitespace() { i += 1; }
        if i >= b.len() || b[i] != b'{' { return Err("expected { to open the extern \"C\" block".into()); }
        let close = match_brace(source, i).map_err(|_| "unterminated extern \"C\" block".to_string())?;
        for (name, sig) in parse_extern_block(&source[i + 1..close])? {
            if externs.insert(name.clone(), sig).is_some() { return Err(format!("duplicate extern declaration of {name}")); }
        }
        for slot in out.iter_mut().take(close + 1).skip(start) { *slot = b' '; }
        search_from = close + 1;
    }
    Ok((externs, String::from_utf8(out).map_err(|e| e.to_string())?))
}

fn blank_unsafe_markers(source: &str) -> Result<String, String> {
    let mut out: Vec<u8> = source.as_bytes().to_vec();
    let mut search_from = 0usize;
    while let Some(start) = find_word_from(source, "unsafe", search_from) {
        let b = source.as_bytes();
        let mut i = start + "unsafe".len();
        while i < b.len() && b[i].is_ascii_whitespace() { i += 1; }
        if i >= b.len() || b[i] != b'{' { return Err("`unsafe` must be followed by a { ... } block".into()); }
        let close = match_brace(source, i).map_err(|_| "unterminated unsafe block".to_string())?;
        for slot in out.iter_mut().take(start + "unsafe".len()).skip(start) { *slot = b' '; }
        out[i] = b' ';
        out[close] = b' ';
        search_from = i + 1;
    }
    Ok(String::from_utf8(out).map_err(|e| e.to_string())?)
}

#[derive(Clone, Debug)]
enum Tok { Id(String), Num(i64), Str(String), True, False, Plus, Minus, Star, Slash, Percent, Eq, EqEq, NotEq, Lt, Le, Gt, Ge, Bang, And, Or, Colon, Dot, Arrow, LParen, RParen, LBrace, RBrace, LBracket, RBracket, Comma, Semi, Eof }

fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let mut out = Vec::new(); let b = s.as_bytes(); let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_whitespace() { i += 1; continue; }
        if i + 1 < b.len() && b[i] == b'/' && b[i + 1] == b'/' { while i < b.len() && b[i] != b'\n' { i += 1; } continue; }
        if i + 1 < b.len() {
            if i + 3 <= b.len() && &s[i..i + 3] == "===" { out.push(Tok::EqEq); i += 3; continue; }
            if &s[i..i + 2] == "=>" { out.push(Tok::Arrow); i += 2; continue; }
            let two = &s[i..i + 2];
            let t = match two { "==" => Some(Tok::EqEq), "!=" => Some(Tok::NotEq), "<=" => Some(Tok::Le), ">=" => Some(Tok::Ge), "&&" => Some(Tok::And), "||" => Some(Tok::Or), _ => None };
            if let Some(t) = t { out.push(t); i += 2; continue; }
        }
        match b[i] {
            b'0'..=b'9' => { let j = i; while i < b.len() && b[i].is_ascii_digit() { i += 1; } out.push(Tok::Num(s[j..i].parse().unwrap())); }
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => { let j = i; while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') { i += 1; } out.push(match &s[j..i] { "true" => Tok::True, "false" => Tok::False, x => Tok::Id(x.into()) }); }
            b'"' => { i += 1; let j = i; while i < b.len() && b[i] != b'"' { i += 1; } if i == b.len() { return Err("unterminated string".into()); } out.push(Tok::Str(s[j..i].into())); i += 1; }
            b'+' => { out.push(Tok::Plus); i += 1; } b'-' => { out.push(Tok::Minus); i += 1; } b'*' => { out.push(Tok::Star); i += 1; } b'/' => { out.push(Tok::Slash); i += 1; } b'%' => { out.push(Tok::Percent); i += 1; }
            b'=' => { out.push(Tok::Eq); i += 1; } b'!' => { out.push(Tok::Bang); i += 1; } b'<' => { out.push(Tok::Lt); i += 1; } b'>' => { out.push(Tok::Gt); i += 1; }
            b':' => { out.push(Tok::Colon); i += 1; } b'.' => { out.push(Tok::Dot); i += 1; } b'(' => { out.push(Tok::LParen); i += 1; } b')' => { out.push(Tok::RParen); i += 1; }
            b'{' => { out.push(Tok::LBrace); i += 1; } b'}' => { out.push(Tok::RBrace); i += 1; } b'[' => { out.push(Tok::LBracket); i += 1; } b']' => { out.push(Tok::RBracket); i += 1; } b',' => { out.push(Tok::Comma); i += 1; } b';' => { out.push(Tok::Semi); i += 1; }
            _ => return Err(format!("unexpected character: {}", b[i] as char)),
        }
    }
    out.push(Tok::Eof); Ok(out)
}

#[derive(Clone, Debug)]
pub(crate) enum Expr {
    Num(i64), Bool(bool), Str(String), Array,
    Index(Box<Expr>, Box<Expr>),
    Var(String),
    FieldAccess(Box<Expr>, String),
    MethodCall(Box<Expr>, String, Vec<Expr>),
    New(String, Vec<Expr>),
    Unary(char, Box<Expr>),
    Bin(Box<Expr>, String, Box<Expr>),
    Call(String, Vec<Expr>),
    CallGeneric(String, ir::IrType, Vec<Expr>),
    Closure(Vec<Stmt>),
}
#[derive(Clone, Debug)]
pub(crate) enum Stmt {
    Let(String, Option<ir::IrType>, Expr),
    Assign(String, Expr),
    FieldAssign(Box<Expr>, String, Expr),
    IndexAssign(Expr, Expr, Expr),
    Return(Expr),
    Expr(Expr),
    If(Expr, Vec<Stmt>, Vec<Stmt>),
    While(Expr, Vec<Stmt>),
    For(Box<Stmt>, Expr, Box<Stmt>, Vec<Stmt>),
    Block(Vec<Stmt>),
}
#[derive(Clone, Debug)]
pub(crate) struct Fun {
    pub(crate) name: String,
    pub(crate) params: Vec<String>,
    pub(crate) param_types: Vec<ir::IrType>,
    pub(crate) return_type: ir::IrType,
    pub(crate) body: Vec<Stmt>,
    pub(crate) type_param: Option<String>,
}
#[derive(Clone, Debug)]
pub(crate) struct ClassDecl {
    pub(crate) name: String,
    pub(crate) fields: Vec<(String, ir::IrType)>,
    pub(crate) constructor: Fun,
    pub(crate) methods: Vec<Fun>,
}

fn inferred_ir_type(e: &Expr) -> ir::IrType { match e { Expr::Num(_) => ir::IrType::Number, Expr::Bool(_) => ir::IrType::Boolean, Expr::Closure(_) => ir::IrType::ClosureNumber, Expr::New(name, _) => ir::IrType::Class(leak_str(name)), Expr::FieldAccess(_, _) => ir::IrType::Number, _ => ir::IrType::Any } }

fn resolve_ty_name(name: &str) -> Result<ir::IrType, String> { match name { "number" => Ok(ir::IrType::Number), "string" => Ok(ir::IrType::String), "boolean" => Ok(ir::IrType::Boolean), "Pointer" => Ok(ir::IrType::Pointer), other => Err(format!("unsupported generic type argument: {other}")) } }

fn ty_tag(ty: ir::IrType) -> String { match ty { ir::IrType::Number => "number".into(), ir::IrType::Boolean => "boolean".into(), ir::IrType::String => "string".into(), ir::IrType::Pointer => "Pointer".into(), ir::IrType::NumberArray => "numberArray".into(), ir::IrType::ClosureNumber => "closureNumber".into(), ir::IrType::Void => "void".into(), ir::IrType::Any => "any".into(), ir::IrType::TParam => "TParam".into(), ir::IrType::Class(name) => format!("class.{name}") } }
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

struct Parser { t: Vec<Tok>, p: usize, unsafe_depth: usize, extern_names: HashSet<String>, scope_type_param: Option<String> }
impl Parser {
    fn peek(&self) -> &Tok { &self.t[self.p] }
    fn eat(&mut self) -> Tok { let x = self.t[self.p].clone(); self.p += 1; x }
    fn id(&mut self) -> Result<String, String> { match self.eat() { Tok::Id(x) => Ok(x), x => Err(format!("expected identifier, got {x:?}")) } }
    fn expect(&mut self, f: fn(&Tok) -> bool, msg: &str) -> Result<(), String> { if f(self.peek()) { self.eat(); Ok(()) } else { Err(msg.into()) } }
    fn annotation(&mut self, type_param: Option<&str>) -> Result<Option<ir::IrType>, String> { if matches!(self.peek(), Tok::Colon) { self.eat(); if matches!(self.peek(), Tok::LParen) { self.eat(); if matches!(self.peek(), Tok::RParen) { self.eat(); self.expect(|x| matches!(x, Tok::Arrow), "expected => in closure type")?; let ret = self.id()?; if ret != "number" { return Err("Nexa v1 closures must return number".into()); } return Ok(Some(ir::IrType::ClosureNumber)); } else if matches!(self.peek(), Tok::LParen) { self.eat(); self.expect(|x| matches!(x, Tok::RParen), "Nexa v1 closure types take no arguments")?; self.expect(|x| matches!(x, Tok::Arrow), "expected => in closure type")?; let ret = self.id()?; if ret != "number" { return Err("Nexa v1 closures must return number".into()); } self.expect(|x| matches!(x, Tok::RParen), "expected ) in closure type")?; return Ok(Some(ir::IrType::ClosureNumber)); } else { return Err("Nexa v1 closure types take no arguments".into()); } } let ty = self.id()?; if Some(ty.as_str()) == type_param { return Ok(Some(ir::IrType::TParam)); } let array = if matches!(self.peek(), Tok::LBracket) { self.eat(); self.expect(|x| matches!(x, Tok::RBracket), "expected ] in type annotation")?; true } else { false }; return Ok(Some(if array { if ty != "number" { return Err("Nexa currently supports only number[] arrays".into()); } ir::IrType::NumberArray } else { match ty.as_str() { "number" => ir::IrType::Number, "string" => ir::IrType::String, "boolean" => ir::IrType::Boolean, "void" => ir::IrType::Void, "any" => ir::IrType::Any, "Pointer" => ir::IrType::Pointer, _ => return Err(format!("unsupported type annotation: {ty}")) } })); } Ok(None) }
    fn expr(&mut self) -> Result<Expr, String> { self.or() }
    fn or(&mut self) -> Result<Expr, String> { self.bin(Self::and, &["||"]) }
    fn and(&mut self) -> Result<Expr, String> { self.bin(Self::compare, &["&&"]) }
    fn compare(&mut self) -> Result<Expr, String> { self.bin(Self::add, &["==", "!=", "<", "<=", ">", ">="]) }
    fn add(&mut self) -> Result<Expr, String> { self.bin(Self::mul, &["+", "-"]) }
    fn mul(&mut self) -> Result<Expr, String> { self.bin(Self::unary, &["*", "/", "%"]) }
    fn bin(&mut self, next: fn(&mut Self) -> Result<Expr, String>, ops: &[&str]) -> Result<Expr, String> {
        let mut x = next(self)?;
        loop { let op = match self.peek() { Tok::Or if ops.contains(&"||") => "||", Tok::And if ops.contains(&"&&") => "&&", Tok::EqEq if ops.contains(&"==") => "==", Tok::NotEq if ops.contains(&"!=") => "!=", Tok::Lt if ops.contains(&"<") => "<", Tok::Le if ops.contains(&"<=") => "<=", Tok::Gt if ops.contains(&">") => ">", Tok::Ge if ops.contains(&">=") => ">=", Tok::Plus if ops.contains(&"+") => "+", Tok::Minus if ops.contains(&"-") => "-", Tok::Star if ops.contains(&"*") => "*", Tok::Slash if ops.contains(&"/") => "/", Tok::Percent if ops.contains(&"%") => "%", _ => break }; self.eat(); x = Expr::Bin(Box::new(x), op.into(), Box::new(next(self)?)); }
        Ok(x)
    }
    fn unary(&mut self) -> Result<Expr, String> { match self.peek() { Tok::Bang => { self.eat(); Ok(Expr::Unary('!', Box::new(self.unary()?))) }, Tok::Minus => { self.eat(); Ok(Expr::Unary('-', Box::new(self.unary()?))) }, _ => self.atom() } }
    fn member_chain(&mut self) -> Result<Expr, String> {
        let mut x = match self.eat() {
            Tok::Id(name) if name == "unsafe" => {
                self.expect(|x| matches!(x, Tok::LBrace), "`unsafe` must be followed by a { ... } block")?;
                self.unsafe_depth += 1;
                let e = self.expr()?;
                self.unsafe_depth -= 1;
                self.expect(|x| matches!(x, Tok::RBrace), "expected } to close unsafe block")?;
                e
            }
            Tok::Id(name) => Expr::Var(name),
            Tok::Num(x) => Expr::Num(x),
            Tok::True => Expr::Bool(true),
            Tok::False => Expr::Bool(false),
            Tok::Str(x) => Expr::Str(x),
            Tok::LBracket => {
                self.expect(|x| matches!(x, Tok::RBracket), "Nexa currently supports only empty array literals")?;
                Expr::Array
            }
            Tok::LParen => {
                if matches!(self.peek(), Tok::RParen) && (matches!(self.t.get(self.p + 1), Some(Tok::Arrow)) || matches!(self.t.get(self.p + 1), Some(Tok::Colon))) {
                    self.eat();
                    if matches!(self.peek(), Tok::Colon) { self.eat(); self.eat(); }
                    self.eat();
                    Expr::Closure(self.block()?)
                } else {
                    let x = self.expr()?;
                    self.expect(|x| matches!(x, Tok::RParen), "expected )")?;
                    x
                }
            }
            x => return Err(format!("expected expression, got {x:?}")),
        };
        while matches!(self.peek(), Tok::Dot) {
            self.eat();
            let field = self.id()?;
            if matches!(self.peek(), Tok::LParen) {
                self.eat();
                let mut args = Vec::new();
                if !matches!(self.peek(), Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; }
                    }
                }
                self.expect(|x| matches!(x, Tok::RParen), "expected )")?;
                if let Expr::Var(ref obj_name) = x {
                    if obj_name == "console" && field == "log" {
                        x = Expr::Call("std.log".into(), args);
                    } else if obj_name == "std" && (field == "log" || field == "in" || field == "parseNumber" || field == "toCString" || field == "funcPtr") {
                        x = Expr::Call(format!("std.{field}"), args);
                    } else {
                        x = Expr::MethodCall(Box::new(x), field, args);
                    }
                } else {
                    x = Expr::MethodCall(Box::new(x), field, args);
                }
            } else {
                x = Expr::FieldAccess(Box::new(x), field);
            }
        }
        while matches!(self.peek(), Tok::LBracket) {
            self.eat();
            let index = self.expr()?;
            self.expect(|x| matches!(x, Tok::RBracket), "expected ]")?;
            x = Expr::Index(Box::new(x), Box::new(index));
        }
        if matches!(self.peek(), Tok::Lt)
            && matches!(self.t.get(self.p + 1), Some(Tok::Id(_)))
            && matches!(self.t.get(self.p + 2), Some(Tok::Gt))
            && matches!(self.t.get(self.p + 3), Some(Tok::LParen)) {
            if let Expr::Var(name) = x {
                self.eat();
                let ty_name = self.id()?;
                let ty = if Some(ty_name.as_str()) == self.scope_type_param.as_deref() { ir::IrType::TParam } else { resolve_ty_name(&ty_name)? };
                self.eat();
                self.eat();
                let mut args = Vec::new();
                if !matches!(self.peek(), Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; }
                    }
                }
                self.expect(|x| matches!(x, Tok::RParen), "expected )")?;
                x = Expr::CallGeneric(name, ty, args);
            }
        } else if matches!(self.peek(), Tok::LParen) {
            if let Expr::Var(ref name) = x {
                let name = name.clone();
                self.eat();
                let mut args = Vec::new();
                if !matches!(self.peek(), Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; }
                    }
                }
                self.expect(|x| matches!(x, Tok::RParen), "expected )")?;
                if self.extern_names.contains(&name) && self.unsafe_depth == 0 {
                    return Err(format!("call to extern function `{name}` must be made inside an unsafe block"));
                }
                x = Expr::Call(name, args);
            }
        }
        Ok(x)
    }
    fn atom(&mut self) -> Result<Expr, String> {
        match self.peek() {
            Tok::Id(name) if name == "new" => {
                self.eat();
                let class_name = self.id()?;
                self.expect(|x| matches!(x, Tok::LParen), "expected (")?;
                let mut args = Vec::new();
                if !matches!(self.peek(), Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; }
                    }
                }
                self.expect(|x| matches!(x, Tok::RParen), "expected )")?;
                Ok(Expr::New(class_name, args))
            }
            Tok::Id(name) if name == "this" => {
                self.eat();
                let mut x = Expr::Var("this".to_string());
                while matches!(self.peek(), Tok::Dot) {
                    self.eat();
                    let field = self.id()?;
                    if matches!(self.peek(), Tok::LParen) {
                        self.eat();
                        let mut args = Vec::new();
                        if !matches!(self.peek(), Tok::RParen) {
                            loop {
                                args.push(self.expr()?);
                                if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; }
                            }
                        }
                        self.expect(|x| matches!(x, Tok::RParen), "expected )")?;
                        x = Expr::MethodCall(Box::new(x), field, args);
                    } else {
                        x = Expr::FieldAccess(Box::new(x), field);
                    }
                }
                while matches!(self.peek(), Tok::LBracket) {
                    self.eat();
                    let index = self.expr()?;
                    self.expect(|x| matches!(x, Tok::RBracket), "expected ]")?;
                    x = Expr::Index(Box::new(x), Box::new(index));
                }
                Ok(x)
            }
            _ => self.member_chain()
        }
    }
    fn block(&mut self) -> Result<Vec<Stmt>, String> { self.expect(|x| matches!(x, Tok::LBrace), "expected {")?; let mut b = Vec::new(); while !matches!(self.peek(), Tok::RBrace | Tok::Eof) { b.push(self.stmt()?); } self.expect(|x| matches!(x, Tok::RBrace), "expected }")?; Ok(b) }
    fn stmt(&mut self) -> Result<Stmt, String> { match self.peek() {
        Tok::Id(k) if k == "let" || k == "const" => { self.eat(); let n = self.id()?; let tp = self.scope_type_param.clone(); let annotation = self.annotation(tp.as_deref())?; self.expect(|x| matches!(x, Tok::Eq), "expected =")?; let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Let(n, annotation, e)) }
        Tok::Id(k) if k == "return" => { self.eat(); let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Return(e)) }
        Tok::Id(k) if k == "if" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let c = self.expr()?; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; let yes = self.block()?; let no = if matches!(self.peek(), Tok::Id(x) if x == "else") { self.eat(); if matches!(self.peek(), Tok::Id(x) if x == "if") { vec![self.stmt()?] } else { self.block()? } } else { Vec::new() }; Ok(Stmt::If(c, yes, no)) }
        Tok::Id(k) if k == "while" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let c = self.expr()?; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; Ok(Stmt::While(c, self.block()?)) }
        Tok::Id(k) if k == "for" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let init = if matches!(self.peek(), Tok::Id(k) if k == "let" || k == "const") { self.stmt()? } else { let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Stmt::Expr(e) }; let cond = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; let update = { let n = self.id()?; self.expect(|x| matches!(x, Tok::Eq), "expected =")?; let e = self.expr()?; Stmt::Assign(n, e) }; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; Ok(Stmt::For(Box::new(init), cond, Box::new(update), self.block()?)) }
        Tok::Id(k) if k == "unsafe" => { self.eat(); self.expect(|x| matches!(x, Tok::LBrace), "`unsafe` must be followed by a { ... } block")?; self.unsafe_depth += 1; let mut body = Vec::new(); while !matches!(self.peek(), Tok::RBrace | Tok::Eof) { body.push(self.stmt()?); } self.unsafe_depth -= 1; self.expect(|x| matches!(x, Tok::RBrace), "expected } to close unsafe block")?; Ok(Stmt::Block(body)) }
        Tok::Id(_) => {
            let left = self.member_chain()?;
            if matches!(self.peek(), Tok::Eq) {
                self.eat();
                let value = self.expr()?;
                self.expect(|x| matches!(x, Tok::Semi), "expected ;")?;
                match left {
                    Expr::FieldAccess(obj, field) => Ok(Stmt::FieldAssign(obj, field, value)),
                    Expr::Var(name) => Ok(Stmt::Assign(name, value)),
                    Expr::Index(a, i) => Ok(Stmt::IndexAssign(*a, *i, value)),
                    _ => Err("invalid assignment target".into()),
                }
            } else {
                self.expect(|x| matches!(x, Tok::Semi), "expected ;")?;
                Ok(Stmt::Expr(left))
            }
        }
        _ => { let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Expr(e)) }
    } }
    fn class_decl(&mut self) -> Result<Fun, String> {
        Err("class declarations are handled at top level by parse_nexa".into())
    }
    fn fun(&mut self) -> Result<Fun, String> { if self.id()? != "function" { return Err("expected function".into()); } let name = self.id()?; let type_param = if matches!(self.peek(), Tok::Lt) { self.eat(); let tp = self.id()?; self.expect(|x| matches!(x, Tok::Gt), "expected > after type parameter")?; Some(tp) } else { None }; self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let mut params = Vec::new(); let mut param_types = Vec::new(); if !matches!(self.peek(), Tok::RParen) { loop { let p = self.id()?; let ty = self.annotation(type_param.as_deref())?.unwrap_or(ir::IrType::Any); params.push(p); param_types.push(ty); if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; } } } self.expect(|x| matches!(x, Tok::RParen), "expected )")?; let return_type = self.annotation(type_param.as_deref())?.unwrap_or(ir::IrType::Any); let saved = self.scope_type_param.clone(); self.scope_type_param = type_param.clone(); let body = self.block()?; self.scope_type_param = saved; Ok(Fun { name, params, param_types, return_type, body, type_param }) }
    fn program(&mut self) -> Result<Vec<Fun>, String> { let mut f = Vec::new(); while !matches!(self.peek(), Tok::Eof) { f.push(self.fun()?); } Ok(f) }
}

struct Compiler {
    m: ObjectModule, funcs: HashMap<String, FuncId>, returns: HashMap<String, ir::IrType>,
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
    fn new() -> Result<Self, String> { let isa = cranelift_codegen::isa::lookup(target_lexicon::HOST).map_err(|e| e.to_string())?.finish(settings::Flags::new(settings::builder())).map_err(|e| e.to_string())?; let b = ObjectBuilder::new(isa, "nexa", cranelift_module::default_libcall_names()).map_err(|e| e.to_string())?; let m = ObjectModule::new(b); let mut c = Self { m, funcs: HashMap::new(), returns: HashMap::new(), closures: HashMap::new(), closure_defs: HashMap::new(), active_kinds: HashMap::new(), active_cells: HashSet::new(), cell_vars: HashMap::new(), current_func: String::new(), closure_index: HashMap::new(), print_i64: FuncId::from_u32(0), print_bool: FuncId::from_u32(0), print_str: FuncId::from_u32(0), array_new: FuncId::from_u32(0), array_get: FuncId::from_u32(0), array_set: FuncId::from_u32(0), concat_str: FuncId::from_u32(0), env_new: FuncId::from_u32(0), env_get: FuncId::from_u32(0), env_set: FuncId::from_u32(0), cell_new: FuncId::from_u32(0), cell_get: FuncId::from_u32(0), cell_set: FuncId::from_u32(0), closure_new: FuncId::from_u32(0), closure_call: FuncId::from_u32(0), stdin_line: FuncId::from_u32(0), parse_number: FuncId::from_u32(0), strings: HashMap::new(), class_new: FuncId::from_u32(0), class_defs: HashMap::new(), extern_funcs: HashMap::new(), extern_voids: HashSet::new() }; c.print_i64 = c.import("nexa_print_i64", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.print_bool = c.import("nexa_print_bool", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.print_str = c.import("nexa_print_str", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_new = c.import("nexa_array_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_get = c.import("nexa_array_get", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_set = c.import("nexa_array_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.concat_str = c.import("nexa_concat_str", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_new = c.import("nexa_env_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_get = c.import("nexa_env_get", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.env_set = c.import("nexa_env_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_new = c.import("nexa_cell_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_get = c.import("nexa_cell_get", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.cell_set = c.import("nexa_cell_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.closure_new = c.import("nexa_closure_new", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.closure_call = c.import("nexa_closure_call", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.stdin_line = c.import("nexa_stdin_line", vec![], vec![AbiParam::new(types::I64)])?; c.parse_number = c.import("nexa_std_parse_number", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.class_new = c.import("nexa_class_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; Ok(c) }
    fn import(&mut self, n: &str, params: Vec<AbiParam>, returns: Vec<AbiParam>) -> Result<FuncId, String> { let mut s = Signature::new(self.m.isa().default_call_conv()); s.params = params; s.returns = returns; self.m.declare_function(n, Linkage::Import, &s).map_err(|e| e.to_string()) }
    fn declare_externs(&mut self, externs: &HashMap<String, ExternSig>) -> Result<(), String> {
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
    fn compile(&mut self, classes: &[ClassDecl], fs: &[Fun]) -> Result<(), String> {
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

fn main() { if let Err(e) = run() { eprintln!("nexa: {e}"); std::process::exit(1); } }
fn strip_top_level_entry_call(source: &str) -> String { source.lines().filter(|line| line.trim() != "main();").collect::<Vec<_>>().join("\n") }

fn parse_nexa(source: &str) -> Result<(Vec<ClassDecl>, Vec<Fun>), String> {
    let (externs, clean) = extract_extern_blocks(source)?;
    parse_nexa_with_externs(&clean, &externs)
}

fn parse_nexa_with_externs(source: &str, externs: &HashMap<String, ExternSig>) -> Result<(Vec<ClassDecl>, Vec<Fun>), String> {
    let lowered_src = strip_top_level_entry_call(source);
    let mut p = Parser { t: lex(&lowered_src)?, p: 0, unsafe_depth: 0, extern_names: externs.keys().cloned().collect(), scope_type_param: None };
    let mut classes = Vec::new();
    let mut functions = Vec::new();
    while !matches!(p.peek(), Tok::Eof) {
        if matches!(p.peek(), Tok::Id(k) if k == "class") {
            p.eat();
            let name = p.id()?;
            p.expect(|x| matches!(x, Tok::LBrace), "expected {")?;
            let mut fields = Vec::new();
            let mut constructor_body = None;
            let mut constructor_param_names = Vec::new();
            let mut constructor_param_tys = Vec::new();
            let mut methods = Vec::new();
            while !matches!(p.peek(), Tok::RBrace | Tok::Eof) {
                if matches!(p.peek(), Tok::Id(k) if k == "constructor") {
                    p.eat();
                    p.expect(|x| matches!(x, Tok::LParen), "expected (")?;
                    if !matches!(p.peek(), Tok::RParen) {
                        loop {
                            let param_name = p.id()?;
                            let ty = p.annotation(None)?.unwrap_or(ir::IrType::Any);
                            constructor_param_names.push(param_name);
                            constructor_param_tys.push(ty);
                            if matches!(p.peek(), Tok::Comma) { p.eat(); } else { break; }
                        }
                    }
                    p.expect(|x| matches!(x, Tok::RParen), "expected )")?;
                    constructor_body = Some(p.block()?);
                } else if matches!(p.peek(), Tok::Id(k) if k == "let" || k == "const") {
                    p.eat();
                    let field_name = p.id()?;
                    let annotation = p.annotation(None)?;
                    let ty = annotation.unwrap_or(ir::IrType::Number);
                    fields.push((field_name, ty));
                    p.expect(|x| matches!(x, Tok::Semi), "expected ;")?;
                } else if matches!(p.peek(), Tok::Id(_)) && matches!(p.t.get(p.p + 1), Some(Tok::Colon)) {
                    let field_name = p.id()?;
                    let annotation = p.annotation(None)?;
                    let ty = annotation.unwrap_or(ir::IrType::Number);
                    fields.push((field_name, ty));
                    p.expect(|x| matches!(x, Tok::Semi), "expected ;")?;
                } else {
                    let method_name = p.id()?;
                    p.expect(|x| matches!(x, Tok::LParen), "expected (")?;
                    let mut params = Vec::new();
                    let mut param_types = Vec::new();
                    if !matches!(p.peek(), Tok::RParen) {
                        loop {
                            let param_name = p.id()?;
                            let ty = p.annotation(None)?.unwrap_or(ir::IrType::Any);
                            params.push(param_name);
                            param_types.push(ty);
                            if matches!(p.peek(), Tok::Comma) { p.eat(); } else { break; }
                        }
                    }
                    p.expect(|x| matches!(x, Tok::RParen), "expected )")?;
                    let return_type = p.annotation(None)?.unwrap_or(ir::IrType::Any);
                    let body = p.block()?;
                    let full_name = format!("{name}.{method_name}");
                    let mut all_params = vec!["this".to_string()];
                    all_params.extend(params);
                    let mut all_param_types = vec![ir::IrType::Class(leak_str(&name))];
                    all_param_types.extend(param_types);
                    methods.push(Fun { name: full_name, params: all_params, param_types: all_param_types, return_type, body, type_param: None });
                }
            }
            p.expect(|x| matches!(x, Tok::RBrace), "expected }")?;
            let mut ctor_params = vec!["this".to_string()];
            let mut ctor_param_types = vec![ir::IrType::Class(leak_str(&name))];
            ctor_params.extend(constructor_param_names);
            ctor_param_types.extend(constructor_param_tys);
            let ctor_name = format!("{name}__constructor");
            let constructor = Fun { name: ctor_name, params: ctor_params, param_types: ctor_param_types, return_type: ir::IrType::Void, body: constructor_body.unwrap_or_default(), type_param: None };
            classes.push(ClassDecl { name, fields, constructor, methods });
        } else {
            functions.push(p.fun()?);
        }
    }
    Ok((classes, functions))
}

fn monomorphize(functions: Vec<Fun>) -> Result<Vec<Fun>, String> {
    let mut generics: HashMap<String, Fun> = HashMap::new();
    let mut program: Vec<Fun> = Vec::new();
    for f in functions {
        match f.type_param {
            Some(_) => { if generics.insert(f.name.clone(), f).is_some() { return Err(format!("duplicate definition of generic function {}", generics.keys().last().unwrap_or(&String::new()))); } }
            None => program.push(f),
        }
    }
    if generics.is_empty() { return Ok(program); }
    let mut pending: Vec<(String, ir::IrType)> = Vec::new();
    for f in program.iter_mut() {
        rewrite_generic_calls(&mut f.body, &mut pending, None)?;
    }
    let mut instances: HashMap<String, Fun> = HashMap::new();
    while !pending.is_empty() {
        let (gname, ty) = pending.remove(0);
        let generic = generics.get(&gname).ok_or_else(|| format!("call to unknown generic function {gname}"))?.clone();
        let mangled = format!("{}.{}", gname, ty_tag(ty));
        if instances.contains_key(&mangled) { continue; }
        let mut inst = generic;
        inst.name = mangled.clone();
        inst.type_param = None;
        subst_fun(&mut inst, ty);
        rewrite_generic_calls(&mut inst.body, &mut pending, Some(ty))?;
        instances.insert(mangled, inst);
    }
    for (_, inst) in instances {
        program.push(inst);
    }
    Ok(program)
}

fn rewrite_generic_calls(stmts: &mut [Stmt], pending: &mut Vec<(String, ir::IrType)>, subst: Option<ir::IrType>) -> Result<(), String> {
    for s in stmts {
        match s {
            Stmt::Let(_, _, e) | Stmt::Assign(_, e) | Stmt::Return(e) | Stmt::Expr(e) => rewrite_generic_calls_expr(e, pending, subst)?,
            Stmt::FieldAssign(obj, _, e) => { rewrite_generic_calls_expr(obj, pending, subst)?; rewrite_generic_calls_expr(e, pending, subst)?; }
            Stmt::IndexAssign(a, i, e) => { rewrite_generic_calls_expr(a, pending, subst)?; rewrite_generic_calls_expr(i, pending, subst)?; rewrite_generic_calls_expr(e, pending, subst)?; }
            Stmt::If(c, y, n) => { rewrite_generic_calls_expr(c, pending, subst)?; rewrite_generic_calls(y, pending, subst)?; rewrite_generic_calls(n, pending, subst)?; }
            Stmt::While(c, b) => { rewrite_generic_calls_expr(c, pending, subst)?; rewrite_generic_calls(b, pending, subst)?; }
            Stmt::For(init, c, u, b) => {
                if let Stmt::Let(_, _, e) | Stmt::Expr(e) = &mut **init { rewrite_generic_calls_expr(e, pending, subst)?; }
                rewrite_generic_calls_expr(c, pending, subst)?;
                if let Stmt::Expr(e) = &mut **u { rewrite_generic_calls_expr(e, pending, subst)?; }
                else if let Stmt::Let(_, _, e) = &mut **u { rewrite_generic_calls_expr(e, pending, subst)?; }
                rewrite_generic_calls(b, pending, subst)?;
            }
            Stmt::Block(b) => rewrite_generic_calls(b, pending, subst)?,
        }
    }
    Ok(())
}

fn rewrite_generic_calls_expr(e: &mut Expr, pending: &mut Vec<(String, ir::IrType)>, subst: Option<ir::IrType>) -> Result<(), String> {
    match e {
        Expr::CallGeneric(name, ty, args) => {
            for a in args.iter_mut() { rewrite_generic_calls_expr(a, pending, subst)?; }
            let effective = if *ty == ir::IrType::TParam {
                subst.ok_or_else(|| format!("TParam type argument in call to {name} outside a generic function body"))?
            } else { *ty };
            pending.push((name.clone(), effective));
            let mangled = format!("{}.{}", name, ty_tag(effective));
            *e = Expr::Call(mangled, std::mem::take(args));
        }
        Expr::Bin(a, _, b) => { rewrite_generic_calls_expr(a, pending, subst)?; rewrite_generic_calls_expr(b, pending, subst)?; }
        Expr::Unary(_, x) => rewrite_generic_calls_expr(x, pending, subst)?,
        Expr::Index(a, i) => { rewrite_generic_calls_expr(a, pending, subst)?; rewrite_generic_calls_expr(i, pending, subst)?; }
        Expr::FieldAccess(o, _) => rewrite_generic_calls_expr(o, pending, subst)?,
        Expr::MethodCall(o, _, args) => { rewrite_generic_calls_expr(o, pending, subst)?; for a in args.iter_mut() { rewrite_generic_calls_expr(a, pending, subst)?; } }
        Expr::Call(_, args) | Expr::New(_, args) => for a in args.iter_mut() { rewrite_generic_calls_expr(a, pending, subst)?; },
        Expr::Closure(body) => rewrite_generic_calls(body, pending, subst)?,
        Expr::Num(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Array | Expr::Var(_) => {}
    }
    Ok(())
}

fn subst_fun(f: &mut Fun, ty: ir::IrType) {
    for p in f.param_types.iter_mut() { if *p == ir::IrType::TParam { *p = ty; } }
    if f.return_type == ir::IrType::TParam { f.return_type = ty; }
    subst_stmts(&mut f.body, ty);
}

fn subst_stmts(stmts: &mut [Stmt], ty: ir::IrType) {
    for s in stmts {
        match s {
            Stmt::Let(_, ann, e) => { if *ann == Some(ir::IrType::TParam) { *ann = Some(ty); } subst_expr(e, ty); }
            Stmt::Assign(_, e) | Stmt::Expr(e) | Stmt::Return(e) => subst_expr(e, ty),
            Stmt::FieldAssign(o, _, e) => { subst_expr(o, ty); subst_expr(e, ty); }
            Stmt::IndexAssign(a, i, e) => { subst_expr(a, ty); subst_expr(i, ty); subst_expr(e, ty); }
            Stmt::If(c, y, n) => { subst_expr(c, ty); subst_stmts(y, ty); subst_stmts(n, ty); }
            Stmt::While(c, b) => { subst_expr(c, ty); subst_stmts(b, ty); }
            Stmt::For(init, c, u, b) => {
                subst_stmts(std::slice::from_mut(&mut **init), ty);
                subst_expr(c, ty);
                subst_stmts(std::slice::from_mut(&mut **u), ty);
                subst_stmts(b, ty);
            }
            Stmt::Block(b) => subst_stmts(b, ty),
        }
    }
}

fn subst_expr(e: &mut Expr, ty: ir::IrType) {
    match e {
        Expr::Bin(a, _, b) => { subst_expr(a, ty); subst_expr(b, ty); }
        Expr::Unary(_, x) => subst_expr(x, ty),
        Expr::Index(a, i) => { subst_expr(a, ty); subst_expr(i, ty); }
        Expr::FieldAccess(o, _) => subst_expr(o, ty),
        Expr::MethodCall(o, _, args) => { subst_expr(o, ty); for a in args.iter_mut() { subst_expr(a, ty); } }
        Expr::Call(_, args) | Expr::New(_, args) => for a in args.iter_mut() { subst_expr(a, ty); },
        Expr::Closure(body) => subst_stmts(body, ty),
        Expr::Num(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Array | Expr::Var(_) | Expr::CallGeneric(_, _, _) => {}
    }
}

fn run() -> Result<(), String> { let a: Vec<String> = env::args().collect(); if a.len() < 2 { return Err("usage: nexa <source.ts> [-o executable]".into()); } let src = fs::read_to_string(&a[1]).map_err(|e| e.to_string())?; let (externs, clean) = extract_extern_blocks(&src)?; let swc_src = blank_unsafe_markers(&clean)?; let module = parse_swc_module(&swc_src, &a[1])?; check_module_with_externs(&module, &externs)?; let (classes, functions) = parse_nexa_with_externs(&clean, &externs)?; let functions = monomorphize(functions)?; let ir = ir::lower_program(&functions); if env::var_os("NEXA_DUMP_IR").is_some() { eprintln!("{ir}"); } let mut c = Compiler::new()?; c.declare_externs(&externs)?; c.compile(&classes, &functions)?; let obj = c.m.finish(); let objpath = "/tmp/nexa.o"; fs::write(objpath, obj.emit().map_err(|e| e.to_string())?).map_err(|e| e.to_string())?; let out = a.iter().position(|x| x == "-o").and_then(|i| a.get(i + 1)).cloned().unwrap_or_else(|| "a.out".into()); if !Path::new("runtime.c").exists() { return Err("runtime.c is missing".into()); } let status = Command::new("gcc").args([objpath, "runtime.c", "-o", &out]).status().map_err(|e| e.to_string())?; if !status.success() { return Err("link failed".into()); } println!("built {out}"); Ok(()) }

#[cfg(test)]
mod safety_tests {
    use super::*;

    #[test]
    fn swc_accepts_optional_chaining_but_checker_rejects_it_before_lowering() {
        let source = r#"
            function main(): number {
                const value: string = "nexa";
                console.log(value?.length);
                return 0;
            }
            main();
        "#;
        let module = parse_swc_module(source, "optional-chaining.ts")
            .expect("SWC should accept optional chaining syntax");
        let error = check_module(&module)
            .expect_err("the checker must reject an unsupported optional-chain AST");
        assert!(error.contains("unsupported expression"), "unexpected checker error: {error}");
        assert!(parse_typescript(source, "optional-chaining.ts").is_err());
    }

    #[test]
    fn array_types_do_not_decay_to_any_before_lowering() {
        let source = r#"
            function take(xs: number[]): number {
                return xs[0];
            }
            function main(): number {
                const xs: number[] = [];
                return take(xs);
            }
            main();
        "#;
        let module = parse_swc_module(source, "array-any.ts").expect("SWC parse");
        check_module(&module).expect("number[] should pass the checker");

        let (_, functions) = parse_nexa(source).expect("parse nexa");
        assert_eq!(functions[0].param_types, vec![ir::IrType::NumberArray]);
        assert!(matches!(
            functions[1].body.first(),
            Some(Stmt::Let(_, Some(ir::IrType::NumberArray), Expr::Array))
        ));
        assert!(!functions.iter().any(|f| {
            f.param_types.iter().any(|t| *t == ir::IrType::Any)
                || f.return_type == ir::IrType::Any
        }));
    }

    #[test]
    fn class_counter_compiles_and_runs() {
        let source = r#"
            class Counter {
                count: number;
                constructor() {
                    this.count = 0;
                }
                increment(): number {
                    this.count = this.count + 1;
                    return this.count;
                }
            }
            function main(): number {
                let a = new Counter();
                let b = new Counter();
                console.log(a.increment());
                console.log(a.increment());
                console.log(b.increment());
                console.log(a.increment());
                return 0;
            }
            main();
        "#;
        parse_typescript(source, "class-counter.ts").expect("type checker should accept classes");
        let (classes, functions) = parse_nexa(source).expect("parser should handle classes");
        assert_eq!(classes.len(), 1, "should parse one class");
        assert_eq!(classes[0].name, "Counter");
        assert_eq!(classes[0].fields.len(), 1);
        assert_eq!(classes[0].fields[0].0, "count");
        assert!(!functions.is_empty(), "should have main function");

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions).expect("compile classes and methods");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_class.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_class"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let output = Command::new("/tmp/nexa_test_class").output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["1", "2", "1", "3"],
            "instances a and b must have independent storage");
    }

    #[test]
    fn extern_malloc_free_acceptance_compiles_and_runs() {
        let source = r#"
            extern "C" {
              function malloc(size: number): Pointer;
              function free(ptr: Pointer): void;
            }

            function main(): number {
              let p: Pointer = unsafe { malloc(64) };
              unsafe { free(p); }
              console.log(1);
              return 0;
            }
        "#;
        parse_typescript(source, "extern-acceptance.ts")
            .expect("type checker should accept extern declarations and unsafe blocks");
        let (classes, functions) = parse_nexa(source).expect("parser should handle extern/unsafe");
        assert!(classes.is_empty());
        let (externs, _) = extract_extern_blocks(source).expect("extract extern signatures");
        assert_eq!(externs.len(), 2);
        assert_eq!(externs["malloc"].params, vec![Ty::Number]);
        assert_eq!(externs["malloc"].ret, Ty::Pointer);
        assert_eq!(externs["free"].ret, Ty::Void);

        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&externs).expect("declare extern imports");
        c.compile(&classes, &functions).expect("compile extern program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_extern.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_extern"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed: malloc/free must resolve against libc");
        let output = Command::new("/tmp/nexa_test_extern").output().unwrap();
        assert!(output.status.success(), "program must exit cleanly after malloc/free");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["1"], "expected the acceptance program to print 1");
    }

    #[test]
    fn extern_call_outside_unsafe_is_compile_time_error() {
        let source = r#"
            extern "C" {
              function malloc(size: number): Pointer;
            }

            function main(): number {
              let p: Pointer = malloc(64);
              return 0;
            }
            main();
        "#;
        parse_typescript(source, "extern-negative.ts")
            .expect("the SWC-level checker accepts the plain call shape; unsafe enforcement happens at lowering");
        let err = parse_nexa(source)
            .expect_err("calling an extern function outside unsafe must fail compilation");
        assert!(err.contains("malloc"), "error should name the extern function: {err}");
        assert!(err.contains("unsafe"), "error should mention the unsafe requirement: {err}");
    }

    #[test]
    fn std_log_and_std_in_compiles_and_runs() {
        use std::io::Write as _;
        use std::process::Stdio;
        let source = r#"
            function main(): number {
              std.log("enter your name:");
              let name: string = std.in();
              std.log("hello, " + name);
              return 0;
            }
        "#;
        parse_typescript(source, "std-hello.ts")
            .expect("type checker should accept std.log/std.in without unsafe");
        let (classes, functions) = parse_nexa(source).expect("parser should handle the std namespace");
        assert!(matches!(
            functions[0].body.first(),
            Some(Stmt::Expr(Expr::Call(n, _))) if n == "std.log"
        ));
        assert!(functions[0].body.iter().any(|s| matches!(
            s,
            Stmt::Let(_, Some(ir::IrType::String), Expr::Call(n, args)) if n == "std.in" && args.is_empty()
        )));

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions).expect("compile std program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_std.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_std"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let mut child = Command::new("/tmp/nexa_test_std")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(b"nexa\n").unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success());
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["enter your name:", "hello, nexa"],
            "std.in must return the line without its trailing newline");
    }

    #[test]
    fn generic_functions_monomorphize_compile_and_run() {
        let source = r#"
            function identity<T>(x: T): T {
              return x;
            }
            function main(): number {
              std.log(identity<number>(5));
              std.log(identity<string>("hello"));
              std.log(identity<boolean>(true));
              return 0;
            }
        "#;
        parse_typescript(source, "generic.ts").expect("type checker should accept generic functions with explicit instantiation");
        let (classes, functions) = parse_nexa(source).expect("parser should handle generic declarations and call sites");
        assert_eq!(functions[0].type_param.as_deref(), Some("T"));
        assert!(matches!(
            functions[0].param_types.as_slice(),
            [ir::IrType::TParam]
        ));
        assert!(matches!(
            functions[1].body.first(),
            Some(Stmt::Expr(Expr::Call(log, args))) if log == "std.log"
            && matches!(args.first(), Some(Expr::CallGeneric(n, ir::IrType::Number, _)) if n == "identity")
        ));
        let mono = monomorphize(functions).expect("monomorphize should instantiate all used generics");
        assert!(mono.iter().all(|f| f.type_param.is_none()), "no generic declarations may survive monomorphization");
        assert!(mono.iter().all(|f| !f.param_types.iter().any(|t| *t == ir::IrType::TParam) && f.return_type != ir::IrType::TParam),
            "every TParam slot must be substituted before codegen");
        for mangled in ["identity.number", "identity.string", "identity.boolean"] {
            assert!(mono.iter().any(|f| f.name == mangled), "expected instance {mangled}");
        }
        assert_eq!(mono.len(), 4, "one main plus three distinct instantiations, deduplicated");

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &mono).expect("compile monomorphized program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_generic.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_generic"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let output = Command::new("/tmp/nexa_test_generic").output().unwrap();
        assert!(output.status.success());
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["5", "hello", "true"],
            "each monomorphized instance must preserve value and tag through identity<T>");
    }

    #[test]
    fn generic_call_requires_explicit_instantiation() {
        let source = r#"
            function identity<T>(x: T): T {
              return x;
            }
            function main(): number {
              std.log(identity(5));
              return 0;
            }
        "#;
        let err = parse_typescript(source, "generic-bad.ts")
            .err()
            .expect("calling a generic function without type arguments must be a compile-time error");
        assert!(err.contains("requires an explicit type instantiation"), "unexpected error: {err}");
    }

    #[test]
    fn std_parse_number_reads_piped_line_and_adds_one() {
        use std::io::Write as _;
        use std::process::Stdio;
        let source = r#"
            function main(): number {
              std.log("enter a number:");
              let raw: string = std.in();
              let n: number = std.parseNumber(raw);
              std.log(n + 1);
              return 0;
            }
        "#;
        parse_typescript(source, "parse-number.ts").expect("type checker should accept std.parseNumber");
        let (classes, functions) = parse_nexa(source).expect("parser should handle std.parseNumber");
        assert!(functions[0].body.iter().any(|s| matches!(
            s,
            Stmt::Let(_, Some(ir::IrType::Number), Expr::Call(n, args)) if n == "std.parseNumber" && args.len() == 1
        )));

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions).expect("compile parseNumber program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_parsenum.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_parsenum"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let mut child = Command::new("/tmp/nexa_test_parsenum")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(b"41\n").unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success());
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["enter a number:", "42"],
            "echo \"41\" | ./a.out must print 42");
    }

    #[test]
    fn std_parse_number_aborts_on_invalid_input() {
        use std::io::Write as _;
        use std::process::Stdio;
        let source = r#"
            function main(): number {
              std.log("enter a number:");
              let raw: string = std.in();
              let n: number = std.parseNumber(raw);
              std.log(n + 1);
              return 0;
            }
        "#;
        let (classes, functions) = parse_nexa(source).expect("parser should handle std.parseNumber");
        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions).expect("compile parseNumber program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_parsenum_bad.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_parsenum_bad"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let mut child = Command::new("/tmp/nexa_test_parsenum_bad")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(b"not a number\n").unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(!output.status.success(),
            "invalid input must fail-fast abort, not return silently");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("parseNumber"), "expected a clear parseNumber error on stderr, got: {stderr}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(!stdout.lines().any(|l| l == "1"),
            "must not fall back to 0 (which would print 0 + 1)");
    }

    #[test]
    fn class_string_field_compiles_and_runs() {
        let source = r#"
            class Person {
                name: string;

                constructor(n: string) {
                    this.name = n;
                }

                greet(): string {
                    return "hello, " + this.name;
                }
            }

            function main(): number {
                let p = new Person("nexa");
                let q = new Person("codex");
                console.log(p.greet());
                console.log(q.greet());
                console.log(p.name);
                return 0;
            }
            main();
        "#;
        parse_typescript(source, "class-string-field.ts").expect("type checker should accept string fields");
        let (classes, functions) = parse_nexa(source).expect("parser should handle string fields");
        assert_eq!(classes.len(), 1, "should parse one class");
        assert_eq!(classes[0].name, "Person");
        assert_eq!(classes[0].fields.len(), 1);
        assert_eq!(classes[0].fields[0].0, "name");
        assert_eq!(classes[0].fields[0].1, ir::IrType::String);

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions).expect("compile classes and methods");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_string_field.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_string_field"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let output = Command::new("/tmp/nexa_test_string_field").output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["hello, nexa", "hello, codex", "nexa"],
            "p and q must hold independent, non-aliased string field values");
    }

    #[test]
    fn pointer_field_and_to_cstring_acceptance_compiles_and_runs() {
        let source = r#"
            class Widget {
              handle: Pointer;
              constructor(h: Pointer) {
                this.handle = h;
              }
            }

            extern "C" {
              function malloc(size: number): Pointer;
              function free(ptr: Pointer): void;
              function puts(s: Pointer): number;
            }

            function main(): number {
              let p: Pointer = unsafe { malloc(64) };
              let w = new Widget(p);
              unsafe { free(w.handle); }

              let msg: string = "hello from nexa";
              unsafe { puts(std.toCString(msg)); }

              std.log(1);
              return 0;
            }
        "#;
        let (classes, functions) = parse_nexa(source).expect("parser should handle Pointer fields and std.toCString");
        assert_eq!(classes.len(), 1, "should parse Widget class");
        assert_eq!(classes[0].name, "Widget");
        assert_eq!(classes[0].fields.len(), 1);
        assert_eq!(classes[0].fields[0].0, "handle");
        assert_eq!(classes[0].fields[0].1, ir::IrType::Pointer);

        let (externs, _) = extract_extern_blocks(source).expect("extract extern signatures");
        assert_eq!(externs.len(), 3);
        assert_eq!(externs["malloc"].params, vec![Ty::Number]);
        assert_eq!(externs["malloc"].ret, Ty::Pointer);
        assert_eq!(externs["free"].params, vec![Ty::Pointer]);
        assert_eq!(externs["free"].ret, Ty::Void);
        assert_eq!(externs["puts"].params, vec![Ty::Pointer]);
        assert_eq!(externs["puts"].ret, Ty::Number);

        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&externs).expect("declare extern imports");
        c.compile(&classes, &functions).expect("compile pointer field + toCString program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_pointer_field.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_pointer_field"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed: puts/malloc/free must resolve against libc");
        let output = Command::new("/tmp/nexa_test_pointer_field").output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["hello from nexa", "1"],
            "puts must print the C string, and std.log must print 1");
    }

    #[test]
    fn funcptr_valid_acceptance_compiles_and_runs() {
        let source = r#"
            extern "C" {
              function puts(s: Pointer): number;
            }

            function greet(): number {
              return 42;
            }

            function main(): number {
              let ptr = std.funcPtr("greet");
              std.log(1);
              return 0;
            }
        "#;
        let (externs, clean) = extract_extern_blocks(source).expect("extract extern");
        let (classes, functions) = parse_nexa_with_externs(&clean, &externs).expect("parse funcPtr program");
        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&externs).expect("declare externs");
        c.compile(&classes, &functions).expect("compile funcPtr program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_funcptr.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_funcptr"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let output = Command::new("/tmp/nexa_test_funcptr").output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(stdout.trim(), "1", "must print 1");
    }

    #[test]
    fn funcptr_rejects_closure_at_compile_time() {
        let source = r#"
            function main(): number {
              let counter = 0;
              let f = () => { counter = counter + 1; return 0; };
              let ptr = std.funcPtr("f");
              return 0;
            }
        "#;
        let (externs, clean) = extract_extern_blocks(source).expect("extract extern");
        let err = compile_with_externs(&clean, &externs).unwrap_err();
        assert!(
            err.contains("closure") || err.contains("std.funcPtr"),
            "should reject closure, got: {err}"
        );
    }

    #[test]
    fn funcptr_rejects_unknown_function_at_compile_time() {
        let source = r#"
            function main(): number {
              let ptr = std.funcPtr("does_not_exist");
              return 0;
            }
        "#;
        let (externs, clean) = extract_extern_blocks(source).expect("extract extern");
        let err = compile_with_externs(&clean, &externs).unwrap_err();
        assert!(
            err.contains("unknown function"),
            "should reject unknown function, got: {err}"
        );
    }

    #[test]
    fn funcptr_rejects_non_literal_argument_at_compile_time() {
        let source = r#"
            function main(): number {
              let name = "main";
              let ptr = std.funcPtr(name);
              return 0;
            }
        "#;
        let (externs, clean) = extract_extern_blocks(source).expect("extract extern");
        let err = compile_with_externs(&clean, &externs).unwrap_err();
        assert!(
            err.contains("string literal"),
            "should reject non-literal argument, got: {err}"
        );
    }
}

fn compile_with_externs(source: &str, externs: &HashMap<String, ExternSig>) -> Result<(), String> {
    let (classes, functions) = parse_nexa_with_externs(source, externs)?;
    let mut c = Compiler::new().map_err(|e| e.to_string())?;
    c.declare_externs(externs)?;
    c.compile(&classes, &functions)?;
    Ok(())
}
