use std::collections::{HashMap, HashSet};

use swc_ecma_ast::{AssignOp, BinaryOp, Callee, ClassMember, Decl, Expr as SExpr, KeyValueProp, Lit, MemberProp, Module as SwcModule, ModuleItem, ObjectLit, Pat, Prop, PropName, PropOrSpread, Stmt as SStmt, TsExprWithTypeArgs, TsKeywordTypeKind, TsType, TsTypeElement};

use crate::ir;
use crate::ir::{ty_to_ir, ir_to_ty, Ty};
use crate::stdlib;
use crate::{leak_str, ExternSig};

#[derive(Clone, Debug)] pub(crate) struct FnSig { params: Vec<Ty>, ret: Ty }
#[derive(Clone, Copy, Debug)] enum GTy { Concrete(Ty), Param }
#[derive(Clone, Debug)] struct GenSig { tparam: String, params: Vec<GTy>, ret: GTy }
#[derive(Clone, Debug)] pub(crate) struct ClassDef { pub(crate) name: String, pub(crate) fields: Vec<(String, ir::IrType)>, pub(crate) constructor_name: String, pub(crate) method_names: Vec<String> }
fn ts_type(ty: &TsType) -> Result<Option<Ty>, String> {
    match ty {
        TsType::TsKeywordType(k) => Ok(Some(match k.kind { TsKeywordTypeKind::TsNumberKeyword => Ty::Number, TsKeywordTypeKind::TsBooleanKeyword => Ty::Boolean, TsKeywordTypeKind::TsStringKeyword => Ty::String, TsKeywordTypeKind::TsVoidKeyword => Ty::Void, TsKeywordTypeKind::TsAnyKeyword => return Err("Nexa does not compile any through the raw typed ABI; use a concrete type".into()), _ => return Err("Nexa supports only number, boolean, string, void, and number[] type annotations".into()) })),
        TsType::TsArrayType(a) => match &*a.elem_type { TsType::TsKeywordType(k) if k.kind == TsKeywordTypeKind::TsNumberKeyword => Ok(Some(Ty::NumberArray)), TsType::TsTypeRef(r) => match (&r.type_name, r.type_params.as_deref()) { (swc_ecma_ast::TsEntityName::Ident(i), None) if &*i.sym == "f32" => Ok(Some(Ty::Float32Array)), (swc_ecma_ast::TsEntityName::Ident(i), None) if &*i.sym == "f64" => Ok(Some(Ty::Float64Array)), _ => Err("Nexa array element types are number, f32, or f64".into()) }, _ => Err("Nexa array element types are number, f32, or f64".into()) },
        TsType::TsUnionOrIntersectionType(_) => Err("Nexa union/intersection type checking is not implemented yet".into()),
        TsType::TsParenthesizedType(p) => ts_type(&p.type_ann),
        TsType::TsTypeRef(r) => match (&r.type_name, r.type_params.as_deref()) {
            (swc_ecma_ast::TsEntityName::Ident(i), None) if &*i.sym == "Pointer" => Ok(Some(Ty::Pointer)),
            (swc_ecma_ast::TsEntityName::Ident(i), None) if &*i.sym == "f32" => Ok(Some(Ty::F32)),
            (swc_ecma_ast::TsEntityName::Ident(i), None) if &*i.sym == "f64" => Ok(Some(Ty::F64)),
            // Any other bare identifier is a fixed-layout class/struct type: a
            // class declared in the same program whose fields define the C
            // layout. This is what lets `class Point { ... }` flow through type
            // annotations and extern "C" signatures as a by-value struct type.
            // A name registered as a structural interface resolves to the
            // interface type instead (same layout convention, statically
            // checked for field-shape compatibility at every use).
            (swc_ecma_ast::TsEntityName::Ident(i), None) => {
                let name = leak_str(&i.sym);
                Ok(Some(if ACTIVE_INTERFACES.with(|c| c.borrow().contains_key(name)) { Ty::Interface(name) } else { Ty::Class(name) }))
            }
            _ => Err("Nexa supports only a bare class/struct name or the built-in Pointer type reference".into()),
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
// Structural interfaces (field-shape type checking). Populated during the
// first pass over the module, consulted whenever `ts_type` resolves a bare
// identifier annotation (to distinguish `interface Point` from a class) and
// whenever a class value is checked against an interface expectation. Kept in
// a thread_local so concurrent test compilations cannot clobber each other.
thread_local! { static ACTIVE_INTERFACES: std::cell::RefCell<HashMap<String, Vec<(String, Ty)>>> = std::cell::RefCell::new(HashMap::new()); }

// `import * as ns` bindings for the module currently being checked: alias ->
// exported member names. Populated ahead of the body pass (alongside
// ACTIVE_INTERFACES) so `ns.member(...)` calls, `new ns.Class()`, and
// `ns.global` reads resolve against the flat top-level names.
thread_local! { static ACTIVE_NAMESPACES: std::cell::RefCell<HashMap<String, HashSet<String>>> = std::cell::RefCell::new(HashMap::new()); }

// If `prop` is a member of the active namespace `ns`, return its flat name.
fn ns_member_name(ns: &str, prop: &MemberProp) -> Option<String> {
    let MemberProp::Ident(pi) = prop else { return None; };
    let field = pi.sym.to_string();
    ACTIVE_NAMESPACES.with(|s| s.borrow().get(ns).map_or(false, |m| m.contains(&field))).then_some(field)
}

// If `obj` is a namespace alias whose `prop` is exported, return its flat name.
fn ns_callee(obj: &SExpr, prop: &MemberProp) -> Option<String> {
    if let SExpr::Ident(i) = obj {
        ns_member_name(&*i.sym, prop)
    } else {
        None
    }
}
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
fn is_float(ty: Ty) -> bool { matches!(ty, Ty::F32 | Ty::F64) }
fn numeric(ty: Ty) -> bool { ty == Ty::Number || is_float(ty) }
// Any value flows into a float destination with an explicit float annotation
// (let, assignment, argument, return, global init): int->float widens
// implicitly, and f32/f64 convert freely in both directions at the annotated
// destination (a value that lands in an f32 slot is demoted, mirroring how a
// literal like 2.5 compiles to the declared type). Float->int is the only
// conversion callers must spell out, via std.toInt.
//
// A class satisfies an interface structurally (real TypeScript shape typing):
// every interface field must exist on the class with the same type. Because a
// class instance is a native pointer and interface field access is compiled
// against the interface's OWN layout, a satisfying class must also declare the
// shared fields at the same index/offset -- i.e. a superset of the interface
// with the interface's fields in the same order. Additional class fields are
// fine. Mismatches produce a precise diagnostic instead of a bare `false`, so
// callers surface them verbatim.
fn assignable(expected: Ty, actual: Ty, classes: &HashMap<String, ClassDef>) -> Result<bool, String> {
    if expected == actual { return Ok(true); }
    if is_float(expected) && matches!(actual, Ty::Number | Ty::F32 | Ty::F64) { return Ok(true); }
    if let (Ty::Interface(iname), Ty::Class(cname)) = (expected, actual) {
        let shapes = ACTIVE_INTERFACES.with(|c| c.borrow().get(iname).cloned()).unwrap_or_default();
        let cls = classes.get(cname).ok_or_else(|| format!("unknown class {cname}"))?;
        for (i, (fname, fty)) in shapes.iter().enumerate() {
            let Some((cname2, cty)) = cls.fields.get(i) else {
                return Err(format!(
                    "class {cname} does not satisfy interface {iname}: missing required field `{fname}` \
                     (a satisfying class must declare the interface's fields at the same positions/offsets)"
                ));
            };
            if cname2 != fname {
                return Err(format!(
                    "class {cname} does not satisfy interface {iname}: field at index {i} is `{cname2}` \
                     but the interface requires `{fname}` (shared fields must be declared in the same order)"
                ));
            }
            if ir_to_ty(*cty) != *fty {
                return Err(format!(
                    "class {cname} does not satisfy interface {iname}: field `{fname}` has type {cty:?} \
                     but the interface requires {fty:?}"
                ));
            }
        }
        return Ok(true);
    }
    Ok(false)
}
/// Validity of an swc object literal at a position whose expected type is the
/// named interface `expected`. Applies the same positional shape-matching rule
/// as class-to-interface assignability: the literal's fields (names + types,
/// in declaration order) must line up exactly with the interface's required
/// fields — this is what makes the interface's known offsets correct for the
/// synthesized struct the literal compiles to. Inferred shape = field count +
/// each field's checked type; any mismatch, spread, or non-field prop, or a
/// non-interface expected type, is rejected.
fn check_object_literal(obj: &ObjectLit, expected: Ty, env: &mut HashMap<String, Ty>, fns: &mut HashMap<String, FnSig>, classes: &mut HashMap<String, ClassDef>, generics: &HashMap<String, GenSig>, insts: &mut Vec<(String, Ty)>) -> Result<Ty, String> {
    let Ty::Interface(iname) = expected else {
        return Err("object literals are supported only where a named interface type is expected (as a function argument or an explicitly-typed `let`); `{ ... }` cannot be an anonymous type in this version".into());
    };
    let shapes = ACTIVE_INTERFACES.with(|c| c.borrow().get(iname).cloned()).unwrap_or_default();
    if obj.props.len() != shapes.len() {
        let expected_names: Vec<String> = shapes.iter().map(|(n, _)| n.clone()).collect();
        return Err(format!(
            "object literal does not match interface {iname}: expected {} field(s) ({}) but found {}",
            shapes.len(),
            expected_names.join(", "),
            obj.props.len()
        ));
    }
    for (i, (fname, fty)) in shapes.iter().enumerate() {
        match obj.props.get(i) {
            Some(PropOrSpread::Spread(_)) => return Err("object literal spread syntax is not supported in this version".into()),
            Some(PropOrSpread::Prop(p)) => match &**p {
                Prop::KeyValue(KeyValueProp { key, value }) => {
                    let PropName::Ident(field_ident) = key else { return Err("object literal fields must be simple identifiers".into()); };
                    if field_ident.sym != *fname {
                        return Err(format!(
                            "object literal does not match interface {iname}: field at index {i} is `{}` but the interface requires `{fname}` (fields must be declared in the same order)",
                            field_ident.sym
                        ));
                    }
                    if matches!(&**value, SExpr::Object(_)) {
                        return Err(format!("object literal field `{fname}` cannot be a nested object literal in this version"));
                    }
                    let field_ty = check_expr(value, env, fns, classes, generics, insts)?;
                    if field_ty != *fty {
                        return Err(format!("object literal does not match interface {iname}: field `{fname}` has type {field_ty:?} but the interface requires {fty:?}"));
                    }
                }
                _ => return Err("object literal supports key-value fields only in this version (no shorthand, method, getter, or setter properties)".into()),
            },
            None => return Err("internal error: object literal field out of range".into()),
        }
    }
    Ok(Ty::Interface(iname))
}
fn float_result(a: Ty, b: Ty) -> Ty { if matches!(a, Ty::F32 | Ty::F64) || matches!(b, Ty::F32 | Ty::F64) { Ty::F64 } else if a == Ty::F32 && b == Ty::F32 { Ty::F32 } else { Ty::Number } }
fn required_type(ann: Option<&swc_ecma_ast::TsTypeAnn>, what: &str) -> Result<Ty, String> { type_annotation(ann)?.ok_or_else(|| format!("Nexa requires a concrete type for {what}; implicit any cannot enter native code")) }

static GLOBAL_ENV: std::sync::LazyLock<std::sync::Mutex<HashMap<String, Ty>>> = std::sync::LazyLock::new(Default::default);

fn walk_idents(e: &SExpr, out: &mut Vec<String>) {
    match e {
        SExpr::Ident(i) => out.push(i.sym.to_string()),
        SExpr::Paren(p) => walk_idents(&p.expr, out),
        SExpr::TsAs(a) => walk_idents(&a.expr, out),
        SExpr::TsNonNull(n) => walk_idents(&n.expr, out),
        SExpr::TsTypeAssertion(ta) => walk_idents(&ta.expr, out),
        SExpr::Unary(u) => walk_idents(&u.arg, out),
        SExpr::Bin(b) => { walk_idents(&b.left, out); walk_idents(&b.right, out); }
        SExpr::Array(a) => { for el in a.elems.iter().flatten() { walk_idents(&el.expr, out); } }
        SExpr::Member(m) => { walk_idents(&m.obj, out); if let MemberProp::Computed(c) = &m.prop { walk_idents(&c.expr, out); } },
        SExpr::Assign(a) => { if let swc_ecma_ast::AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Ident(i)) = &a.left { out.push(i.id.sym.to_string()); } walk_idents(&a.right, out); }
        SExpr::Call(c) => { if let Callee::Expr(x) = &c.callee { walk_idents(x, out); } for a in &c.args { walk_idents(&a.expr, out); } }
        SExpr::New(n) => { if let Some(args) = &n.args { for a in args { walk_idents(&a.expr, out); } } }
        SExpr::Object(o) => for prop in &o.props { if let PropOrSpread::Prop(p) = prop { if let Prop::KeyValue(kv) = &**p { walk_idents(&kv.value, out); } } }
        _ => {}
    }
}
fn check_expr(e: &SExpr, env: &mut HashMap<String, Ty>, fns: &mut HashMap<String, FnSig>, classes: &mut HashMap<String, ClassDef>, generics: &HashMap<String, GenSig>, insts: &mut Vec<(String, Ty)>) -> Result<Ty, String> {
    match e {
        SExpr::Lit(Lit::Num(n)) => Ok(if (n.raw.as_deref().map_or(false, |r| r.contains('.') || r.contains('e') || r.contains('E'))) || n.value.fract() != 0.0 { Ty::F64 } else { Ty::Number }), SExpr::Lit(Lit::Bool(_)) => Ok(Ty::Boolean), SExpr::Lit(Lit::Str(_)) => Ok(Ty::String),
        SExpr::Lit(_) => Err("Nexa supports only number, boolean, and string literals".into()),
        SExpr::Ident(i) => env.get(i.sym.as_ref()).copied().or_else(|| GLOBAL_ENV.lock().ok().and_then(|c| c.get(i.sym.as_ref()).copied())).ok_or_else(|| format!("unknown variable {}", i.sym)),
        SExpr::This(_) => env.get("this").copied().ok_or_else(|| "this used outside of class context".into()),
        SExpr::Paren(p) => check_expr(&p.expr, env, fns, classes, generics, insts), SExpr::TsAs(a) => check_expr(&a.expr, env, fns, classes, generics, insts), SExpr::TsNonNull(n) => check_expr(&n.expr, env, fns, classes, generics, insts),
        SExpr::Unary(u) => { let t = check_expr(&u.arg, env, fns, classes, generics, insts)?; match u.op { swc_ecma_ast::UnaryOp::Bang => { if t != Ty::Boolean && t != Ty::Any { return Err("! expects boolean".into()); } Ok(Ty::Boolean) }, swc_ecma_ast::UnaryOp::Minus | swc_ecma_ast::UnaryOp::Plus => { if !(numeric(t) || t == Ty::Any) { return Err("numeric unary operator expects number, f32, or f64".into()); } Ok(t) }, _ => Err("unsupported unary operator in Nexa".into()) } }
        SExpr::Bin(b) => { let l = check_expr(&b.left, env, fns, classes, generics, insts)?; let r = check_expr(&b.right, env, fns, classes, generics, insts)?; match b.op { BinaryOp::Add => { if l == Ty::String && r == Ty::String { Ok(Ty::String) } else if numeric(l) && numeric(r) { Ok(float_result(l, r)) } else { Err("+ expects two numbers, two strings, or two floats".into()) } }, BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => { if !numeric(l) || !numeric(r) { return Err("arithmetic operators expect number, f32, or f64 operands".into()); } Ok(float_result(l, r)) }, BinaryOp::Mod => { if !numeric(l) || !numeric(r) { return Err("modulo expects number operands".into()); } if is_float(l) || is_float(r) { return Err("modulo (%) is not supported on float operands".into()); } Ok(Ty::Number) }, BinaryOp::LogicalAnd | BinaryOp::LogicalOr => { if !compatible(Ty::Boolean, l) || !compatible(Ty::Boolean, r) { return Err("logical operators expect booleans".into()); } Ok(Ty::Boolean) }, BinaryOp::EqEq | BinaryOp::NotEq | BinaryOp::EqEqEq | BinaryOp::NotEqEq | BinaryOp::Lt | BinaryOp::LtEq | BinaryOp::Gt | BinaryOp::GtEq => { if l != Ty::Any && r != Ty::Any && l != r && !(numeric(l) && numeric(r)) { return Err("comparison operands must have compatible types".into()); } Ok(Ty::Boolean) }, _ => Err("unsupported binary operator in Nexa".into()) } }
        SExpr::Array(a) => { if a.elems.is_empty() { return Err("unsized array literal `[]` is a compile error in this version; use `new Array<number>(n)` to allocate an explicit size".into()); } for el in &a.elems { let Some(e) = el else { return Err("array literals may not contain holes or spread elements".into()); }; if e.spread.is_some() { return Err("spread (...) is not supported in array literals".into()); } let t = check_expr(&e.expr, env, fns, classes, generics, insts)?; if !compatible(Ty::Number, t) { return Err("number[] literal elements must all be numbers".into()); } } Ok(Ty::NumberArray) }
        SExpr::Member(m) => { if let SExpr::Ident(ns_ident) = &*m.obj { if let Some(field) = ns_member_name(&*ns_ident.sym, &m.prop) { return GLOBAL_ENV.lock().ok().and_then(|c| c.get(&field).copied()).ok_or_else(|| format!("namespace `{}` has no exported global `{field}`", ns_ident.sym)); } } let object = check_expr(&m.obj, env, fns, classes, generics, insts)?; match &m.prop { MemberProp::Computed(c) => { let elem = match object { Ty::Float32Array => Ty::F32, Ty::Float64Array => Ty::F64, _ => Ty::Number }; if object != Ty::NumberArray && object != Ty::Float32Array && object != Ty::Float64Array && object != Ty::Any { return Err("indexed access requires a number[], f32[], or f64[] array".into()); } let idx = check_expr(&c.expr, env, fns, classes, generics, insts)?; if !(compatible(Ty::Number, idx) || idx == Ty::Any) { return Err("array index must be a number".into()); } Ok(elem) },         MemberProp::Ident(field_ident) => { let field_name = field_ident.sym.to_string(); if matches!(object, Ty::NumberArray | Ty::Float32Array | Ty::Float64Array) { if field_name == "length" { return Ok(Ty::Number); } return Err(format!("arrays have only a `length` property, not `{field_name}`")); } if let Ty::Class(cls_name) = object { let cls = classes.get(cls_name).ok_or_else(|| format!("unknown class {cls_name}"))?; for (name, ty) in &cls.fields { if name == &field_name { return Ok(ir_to_ty(*ty)); } } return Err(format!("unknown field {field_name} on class {cls_name}")); } if let Ty::Interface(iname) = object { let fields = ACTIVE_INTERFACES.with(|c| c.borrow().get(iname).cloned()).unwrap_or_default(); for (name, ty) in &fields { if name == &field_name { return Ok(*ty); } } return Err(format!("unknown field {field_name} on interface {iname}")); } if object == Ty::Any { return Ok(Ty::Any); } Err("field access on non-class type".into()) }, _ => Err("unsupported member property".into()) } }
        SExpr::Assign(a) => { let new = check_expr(&a.right, env, fns, classes, generics, insts)?; match &a.left { swc_ecma_ast::AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Ident(i)) => { let name = i.id.sym.to_string(); let old = env.get(&name).copied().or_else(|| GLOBAL_ENV.lock().ok().and_then(|c| c.get(&name).copied())).ok_or_else(|| format!("unknown variable {name}"))?; if a.op != AssignOp::Assign && old != Ty::Number { return Err("compound assignment requires number".into()); } if !assignable(old, new, classes)? { return Err(format!("cannot assign {new:?} to {old:?}")); } Ok(old) }, swc_ecma_ast::AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Member(m)) => { if a.op != AssignOp::Assign { return Err("compound array assignment is not implemented".into()); } let object = check_expr(&m.obj, env, fns, classes, generics, insts)?; match object { Ty::NumberArray | Ty::Float32Array | Ty::Float64Array | Ty::Any => { let elem = match object { Ty::Float32Array => Ty::F32, Ty::Float64Array => Ty::F64, _ => Ty::Number }; if let MemberProp::Computed(c) = &m.prop { if !compatible(Ty::Number, check_expr(&c.expr, env, fns, classes, generics, insts)?) { return Err("array index must be a number".into()); } } if !assignable(elem, new, classes)? { return Err(format!("cannot assign {new:?} to an array of {elem:?}")); } Ok(new) }, Ty::Class(cls_name) => { let cls = classes.get(cls_name).ok_or_else(|| format!("unknown class {cls_name}"))?; if let MemberProp::Ident(field_ident) = &m.prop { let field_name = field_ident.sym.to_string(); for (name, ty) in &cls.fields { if name == &field_name { if !assignable(ir_to_ty(*ty), new, classes)? { return Err(format!("cannot assign {new:?} to field {field_name} of type {:?}", ir_to_ty(*ty))); } return Ok(new); } } return Err(format!("unknown field {field_name} on class {cls_name}")); } Err("field assignment requires an identifier".into()) }, Ty::Interface(iname) => { let fields = ACTIVE_INTERFACES.with(|c| c.borrow().get(iname).cloned()).unwrap_or_default(); if let MemberProp::Ident(field_ident) = &m.prop { let field_name = field_ident.sym.to_string(); for (name, ty) in &fields { if name == &field_name { if !assignable(*ty, new, classes)? { return Err(format!("cannot assign {new:?} to field {field_name} of type {ty:?}")); } return Ok(new); } } return Err(format!("unknown field {field_name} on interface {iname}")); } Err("field assignment requires an identifier".into()) }, _ => Err("indexed assignment requires an array (number[], f32[], or f64[])".into()) } }, _ => Err("Nexa assignments require a local identifier or array element".into()) } }
        SExpr::Call(c) => { let name = match &c.callee { Callee::Expr(x) => match &**x { SExpr::Ident(i) => i.sym.to_string(), SExpr::Member(m) if matches!(&m.obj.as_ref(), SExpr::Ident(i) if i.sym == "console") && matches!(&m.prop, MemberProp::Ident(i) if i.sym == "log") => "console.log".into(),                 SExpr::Member(m) if matches!(&m.obj.as_ref(), SExpr::Ident(i) if i.sym == "std") && matches!(&m.prop, MemberProp::Ident(i) if i.sym == "log" || i.sym == "in" || i.sym == "parseNumber" || i.sym == "toCString" || i.sym == "fromCString" || i.sym == "funcPtr" || i.sym == "strlen" || i.sym == "charAt" || i.sym == "toF64" || i.sym == "toF32" || i.sym == "toInt") => { let MemberProp::Ident(pi) = &m.prop else { unreachable!() }; format!("std.{}", pi.sym) }, SExpr::Member(m) if matches!(&m.obj.as_ref(), SExpr::Member(inner) if matches!(&inner.obj.as_ref(), SExpr::Ident(i) if i.sym == "std") && matches!(&inner.prop, MemberProp::Ident(i) if i.sym == "process")) && matches!(&m.prop, MemberProp::Ident(i) if i.sym == "exec1" || i.sym == "exec2" || i.sym == "pipe" || i.sym == "pipeReadFd" || i.sym == "pipeWriteFd") => { let MemberProp::Ident(pi) = &m.prop else { unreachable!() }; format!("std.process.{}", pi.sym) }, SExpr::Member(m) if ns_callee(&m.obj, &m.prop).is_some() => ns_callee(&m.obj, &m.prop).unwrap(), SExpr::Member(m) => { if let MemberProp::Ident(method_ident) = &m.prop { let method_name = method_ident.sym.to_string(); let obj_ty = check_expr(&m.obj, env, fns, classes, generics, insts)?; if let Ty::Class(cls_name) = obj_ty { let sig_name = format!("{}.{}", cls_name, method_name); let sig = fns.get(&sig_name).ok_or_else(|| format!("unknown method {}.{}", cls_name, method_name))?.clone(); if sig.params.len() - 1 != c.args.len() { return Err(format!("method {} expects {} arguments", sig_name, sig.params.len() - 1)); } for (p, a) in sig.params.iter().skip(1).zip(&c.args) { let t = if let SExpr::Object(obj) = &*a.expr { check_object_literal(obj, *p, env, fns, classes, generics, insts)? } else { check_expr(&a.expr, env, fns, classes, generics, insts)? }; if !assignable(*p, t, classes)? { return Err(format!("argument type {t:?} does not match {p:?}")); } } return Ok(sig.ret); } } return Err("cannot call method on non-class type".into()); } _ => return Err("Nexa calls require a named function".into()) }, _ => return Err("unsupported call target".into()) }; let name = if name == "console.log" { "std.log".to_string() } else { name };
        if let Some(op) = stdlib::StdOp::of(&name) {
            let arg_types;
            let func_ptr_literal;
            if stdlib::checks_argument_types(op) {
                arg_types = c.args.iter().map(|a| check_expr(&a.expr, env, fns, classes, generics, insts)).collect::<Result<Vec<_>, _>>()?;
                func_ptr_literal = None;
            } else {
                arg_types = Vec::new();
                func_ptr_literal = c.args.first().and_then(|a| match &*a.expr {
                    SExpr::Lit(Lit::Str(s)) => Some(s.value.as_str().unwrap_or("").to_string()),
                    _ => None,
                });
            }
            return stdlib::check_call(op, c.args.len(), &arg_types, func_ptr_literal.as_deref(), env, fns);
        } if c.type_args.is_some() && !generics.contains_key(&name) { return Err(format!("type arguments are only allowed when calling generic functions; {name} is not generic")); } if let Some(sig) = generics.get(&name) { let Some(targs) = c.type_args.as_deref().map(|t| t.params.as_slice()) else { return Err(format!("generic function {name} requires an explicit type instantiation at every call site, e.g. {name}<number>(...)")); }; if targs.len() != 1 { return Err("Nexa supports only a single type argument per generic call".into()); } let ty = resolve_type_arg(&targs[0])?; if matches!(ty, Ty::Void | Ty::Any) { return Err(format!("cannot instantiate {name} with void or any")); } let subst = |g: &GTy| match g { GTy::Concrete(t) => *t, GTy::Param => ty }; if sig.params.len() != c.args.len() { return Err(format!("function {name} expects {} arguments", sig.params.len())); } for (p, a) in sig.params.iter().zip(&c.args) { let expected = subst(p); let t = if let SExpr::Object(obj) = &*a.expr { check_object_literal(obj, expected, env, fns, classes, generics, insts)? } else { check_expr(&a.expr, env, fns, classes, generics, insts)? }; if !assignable(expected, t, classes)? { return Err(format!("argument type {t:?} does not match {expected:?}")); } } insts.push((name.clone(), ty)); return Ok(subst(&sig.ret)); } if env.get(&name) == Some(&Ty::ClosureNumber) { if !c.args.is_empty() { return Err("Nexa v1 closures take no arguments".into()); } return Ok(Ty::Number); } let sig = fns.get(&name).ok_or_else(|| format!("unknown function {name}"))?.clone(); if sig.params.len() != c.args.len() { return Err(format!("function {name} expects {} arguments", sig.params.len())); } for (p, a) in sig.params.iter().zip(&c.args) { let t = if let SExpr::Object(obj) = &*a.expr { check_object_literal(obj, *p, env, fns, classes, generics, insts)? } else { check_expr(&a.expr, env, fns, classes, generics, insts)? }; if !assignable(*p, t, classes)? { return Err(format!("argument type {t:?} does not match {p:?}")); } } Ok(sig.ret) }
        SExpr::New(n) => { let class_name = match &*n.callee { SExpr::Ident(i) => Some(i.sym.to_string()), SExpr::Member(m) => ns_callee(&m.obj, &m.prop), _ => None }; if let Some(class_name) = class_name { if class_name == "Array" { if n.args.as_deref().map_or(true, |a| a.is_empty()) || n.args.as_deref().unwrap().len() != 1 { return Err("new Array<T>(n) requires exactly one size argument".into()); } if !compatible(Ty::Number, check_expr(&n.args.as_deref().unwrap()[0].expr, env, fns, classes, generics, insts)?) { return Err("array size must be a number".into()); } let elem = n.type_args.as_deref().and_then(|t| t.params.first()).map(|t| resolve_type_arg(t)).transpose()?.unwrap_or(Ty::Number); if !matches!(elem, Ty::Number | Ty::F32 | Ty::F64) { return Err("new Array requires a number, f32, or f64 element type".into()); } return Ok(match elem { Ty::F32 => Ty::Float32Array, Ty::F64 => Ty::Float64Array, _ => Ty::NumberArray }); } let cls = classes.get(&class_name).ok_or_else(|| format!("unknown class {class_name}"))?; let ctor_name = &cls.constructor_name; let sig = fns.get(ctor_name).ok_or_else(|| format!("unknown constructor {ctor_name}"))?; if sig.params.len() != n.args.as_deref().unwrap_or(&[]).len() + 1 { return Err(format!("constructor {} expects {} arguments (including implicit this)", ctor_name, sig.params.len())); } Ok(Ty::Class(leak_str(&class_name))) } else { Err("new requires a class name".into()) } }
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
        SExpr::Object(_) => Err("object literals are supported only where a named interface type is expected in this version (as a function argument or the initializer of an explicitly-typed `let`)".into()),
        _ => Err("unsupported expression in Nexa type checker".into()),
    }
}
fn check_stmt(s: &SStmt, env: &mut HashMap<String, Ty>, fns: &mut HashMap<String, FnSig>, classes: &mut HashMap<String, ClassDef>, ret: Ty, generics: &HashMap<String, GenSig>, insts: &mut Vec<(String, Ty)>) -> Result<(), String> {
    match s {
        SStmt::Decl(Decl::Var(v)) => for d in &v.decls { let Pat::Ident(i) = &d.name else { return Err("Nexa local declarations require identifiers".into()); }; let actual = match d.init.as_ref() { Some(init) => { let declared_ann = type_annotation(i.type_ann.as_deref())?; if let SExpr::Object(obj) = &**init { let expected = declared_ann.ok_or_else(|| format!("object literal initializer for `{}` requires an explicit named interface annotation", i.id.sym))?; check_object_literal(obj, expected, env, fns, classes, generics, insts)? } else { check_expr(init, env, fns, classes, generics, insts)? } } None => Ty::Any }; if actual == Ty::Any { return Err(format!("Nexa requires an initializer or concrete annotation for {}", i.id.sym)); } let declared = type_annotation(i.type_ann.as_deref())?.unwrap_or(actual); if !assignable(declared, actual, classes)? { return Err(format!("initializer type {actual:?} does not match {declared:?}")); } env.insert(i.id.sym.to_string(), declared); },
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
        SStmt::Return(r) => { let actual = r.arg.as_ref().map(|x| check_expr(x, env, fns, classes, generics, insts)).transpose()?.unwrap_or(Ty::Void); if !assignable(ret, actual, classes)? { return Err(format!("return type {actual:?} does not match {ret:?}")); } },
        SStmt::Block(b) => for s in &b.stmts { check_stmt(s, env, fns, classes, ret, generics, insts)?; },
        SStmt::If(i) => { let t = check_expr(&i.test, env, fns, classes, generics, insts)?; if t != Ty::Boolean && t != Ty::Any { return Err("if condition must be boolean".into()); } check_stmt(&i.cons, env, fns, classes, ret, generics, insts)?; if let Some(a) = &i.alt { check_stmt(a, env, fns, classes, ret, generics, insts)?; } },
        SStmt::While(w) => { let t = check_expr(&w.test, env, fns, classes, generics, insts)?; if t != Ty::Boolean && t != Ty::Any { return Err("while condition must be boolean".into()); } check_stmt(&w.body, env, fns, classes, ret, generics, insts)?; },
        SStmt::For(f) => { if let Some(init) = &f.init { match init { swc_ecma_ast::VarDeclOrExpr::VarDecl(v) => for d in &v.decls { let Pat::Ident(i) = &d.name else { return Err("Nexa for declarations require identifiers".into()); }; let actual = match d.init.as_ref() { Some(init) => { let declared_ann = type_annotation(i.type_ann.as_deref())?; if let SExpr::Object(obj) = &**init { let expected = declared_ann.ok_or_else(|| format!("object literal initializer for `{}` requires an explicit named interface annotation", i.id.sym))?; check_object_literal(obj, expected, env, fns, classes, generics, insts)? } else { check_expr(init, env, fns, classes, generics, insts)? } } None => Ty::Any }; let declared = type_annotation(i.type_ann.as_deref())?.unwrap_or(actual); if !assignable(declared, actual, classes)? { return Err(format!("initializer type {actual:?} does not match {declared:?}")); } env.insert(i.id.sym.to_string(), declared); }, swc_ecma_ast::VarDeclOrExpr::Expr(e) => { check_expr(e, env, fns, classes, generics, insts)?; } } } if let Some(test) = &f.test { let t = check_expr(test, env, fns, classes, generics, insts)?; if t != Ty::Boolean && t != Ty::Any { return Err("for condition must be boolean".into()); } } if let Some(update) = &f.update { check_expr(update, env, fns, classes, generics, insts)?; } check_stmt(&f.body, env, fns, classes, ret, generics, insts)?; },
        SStmt::ForOf(f) => { let iter_ty = check_expr(&f.right, env, fns, classes, generics, insts)?; let elem_ty = match iter_ty { Ty::NumberArray => Ty::Number, Ty::String => Ty::String, _ => return Err(format!("cannot iterate over {iter_ty:?}; only number[] and string are iterable")) }; let bname = match &f.left { swc_ecma_ast::ForHead::VarDecl(v) if v.kind == swc_ecma_ast::VarDeclKind::Const => { if v.decls.len() != 1 { return Err("Nexa for...of requires a single identifier binder".into()); } match &v.decls[0].name { Pat::Ident(b) => b.id.sym.to_string(), _ => return Err("Nexa for...of requires a single identifier binder".into()) } }, _ => return Err("Nexa v1 for...of supports only a `const x of ...` declaration".into()) }; env.insert(bname, elem_ty); check_stmt(&f.body, env, fns, classes, ret, generics, insts)?; },
        SStmt::Empty(_) => {},
        _ => return Err("unsupported statement in Nexa type checker".into()),
    } Ok(())
}
pub(crate) fn check_module(module: &SwcModule) -> Result<(), String> { check_module_with_externs(module, &HashMap::new(), &HashMap::new()) }

pub(crate) fn check_module_with_externs(module: &SwcModule, externs: &HashMap<String, ExternSig>, namespaces: &HashMap<String, HashSet<String>>) -> Result<(), String> {
    let mut fns = HashMap::new();
    for (name, sig) in externs {
        fns.insert(name.clone(), FnSig { params: sig.params.clone(), ret: sig.ret });
    }
    let mut classes = HashMap::new();
    let mut generics: HashMap<String, GenSig> = HashMap::new();
    let mut generic_bodies: HashMap<String, &swc_ecma_ast::Function> = HashMap::new();
    let mut insts: Vec<(String, Ty)> = Vec::new();
    let mut globals: HashMap<String, Ty> = HashMap::new();
    let mut global_decls: Vec<(String, Ty, swc_ecma_ast::Expr)> = Vec::new();
    let mut global_index: HashMap<String, usize> = HashMap::new();
    ACTIVE_INTERFACES.with(|s| *s.borrow_mut() = HashMap::new());
    ACTIVE_NAMESPACES.with(|s| *s.borrow_mut() = namespaces.clone());
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
                if ACTIVE_INTERFACES.with(|s| s.borrow().contains_key(&class_name)) {
                    return Err(format!("duplicate top-level declaration `{class_name}` (an interface of the same name already exists)"));
                }
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
                for impl_ in &c.class.implements {
                    let TsExprWithTypeArgs { expr, type_args, .. } = impl_;
                    let SExpr::Ident(iname) = &**expr else { return Err("`implements` must name a single interface".into()); };
                    if type_args.is_some() { return Err("generic `implements` clauses are not supported".into()); }
                    let iname = iname.sym.to_string();
                    let ifields = ACTIVE_INTERFACES.with(|s| s.borrow().get(&iname).cloned()).ok_or_else(|| format!("unknown interface `{iname}` in implements clause of class `{class_name}` (interfaces must be declared before the classes that implement them)"))?;
                    for (i, (if_name, if_ty)) in ifields.iter().enumerate() {
                        let mismatch = match fields.get(i) {
                            Some((fname, fty)) => fname != if_name || fty != if_ty,
                            None => true,
                        };
                        if mismatch {
                            return Err(format!("class {class_name} does not satisfy interface {iname}: interface field `{if_name}` must be declared at the same index ({i}) with the same type ({if_ty:?})"));
                        }
                    }
                }
                classes.insert(class_name.clone(), ClassDef { name: class_name, fields: fields.into_iter().map(|(n, t)| (n, ty_to_ir(t))).collect(), constructor_name, method_names });
            }
            ModuleItem::Stmt(SStmt::Decl(Decl::TsInterface(i))) => {
                // Structural interfaces: field-shape types only. Collected in
                // this first pass so that annotations (params, lets, returns,
                // call sites) can resolve the name to an interface type.
                let name = i.id.sym.to_string();
                if fns.contains_key(&name) || classes.contains_key(&name) || ACTIVE_INTERFACES.with(|s| s.borrow().contains_key(&name)) {
                    return Err(format!("duplicate top-level declaration `{name}`"));
                }
                if i.type_params.is_some() { return Err("generic interfaces are not supported in this version".into()); }
                if !i.extends.is_empty() { return Err("interface-to-interface extension (`interface A extends B`) is not supported in this version".into()); }
                let mut fields = Vec::new();
                for elem in &i.body.body {
                    match elem {
                        TsTypeElement::TsPropertySignature(psig) => {
                            if psig.computed { return Err(format!("interface `{name}`: computed property names are not supported")); }
                            if psig.optional { return Err(format!("interface `{name}`: optional fields are not supported; every interface field is required")); }
                            let SExpr::Ident(fn_ident) = psig.key.as_ref() else { return Err(format!("interface `{name}`: fields must be simple identifiers")); };
                            let field_name = fn_ident.sym.to_string();
                            let field_ty = required_type(psig.type_ann.as_deref(), &format!("interface {name}.{field_name}"))?;
                            if !matches!(field_ty, Ty::Number | Ty::Boolean | Ty::String | Ty::Pointer) {
                                return Err(format!("interface `{name}` field `{field_name}` must be number, boolean, string, or Pointer; got {field_ty:?}"));
                            }
                            fields.push((field_name.clone(), field_ty));
                        }
                        _ => return Err(format!("interface `{name}` supports fields only in this version (no method, index, getter, setter, or call signatures)")),
                    }
                }
                ACTIVE_INTERFACES.with(|s| { s.borrow_mut().insert(name, fields); });
            }
            ModuleItem::Stmt(SStmt::Decl(Decl::Var(v))) => {
                if v.decls.len() != 1 { return Err("Nexa supports only single-declarator top-level global declarations".into()); }
                let swc_ecma_ast::Pat::Ident(p) = &v.decls[0].name else { return Err("top-level global declarations require an identifier".into()); };
                let name = p.id.sym.to_string();
                if globals.contains_key(&name) || fns.contains_key(&name) || classes.contains_key(&name) { return Err(format!("duplicate top-level declaration `{name}`")); }
                let ty = required_type(p.type_ann.as_deref(), "module next to global")?;
                if !matches!(ty, Ty::Number | Ty::Boolean | Ty::String | Ty::F32 | Ty::F64) { return Err(format!("top-level global `{name}` must be number, boolean, string, f32, or f64; got {ty:?}")); }
                let init = v.decls[0].init.as_deref().ok_or_else(|| format!("top-level global `{name}` requires an initializer"))?.clone();
                global_index.insert(name.clone(), global_decls.len());
                global_decls.push((name.clone(), ty, init));
                globals.insert(name, ty);
            }
            _ => {}
        }
    }
    let mut declared: HashMap<String, Ty> = HashMap::new();
    for (i, (name, ty, init)) in global_decls.iter().enumerate() {
        let mut refs = Vec::new();
        walk_idents(init, &mut refs);
        for r in refs {
            if let Some(&idx) = global_index.get(&r) {
                if idx > i {
                    return Err(format!("top-level global `{name}` forward-references global `{r}` declared later; globals must initialize in declaration order"));
                }
            }
        }
        GLOBAL_ENV.lock().unwrap().clone_from(&declared);
        let init_ty = check_expr(init, &mut HashMap::new(), &mut fns, &mut classes, &generics, &mut insts)?;
        if !assignable(*ty, init_ty, &classes)? { return Err(format!("initializer type {init_ty:?} for global `{name}` does not match declared type {ty:?}")); }
        declared.insert(name.clone(), *ty);
    }
    GLOBAL_ENV.lock().unwrap().clone_from(&globals);
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
    GLOBAL_ENV.lock().unwrap().clear();
    ACTIVE_INTERFACES.with(|s| *s.borrow_mut() = HashMap::new());
    ACTIVE_NAMESPACES.with(|s| *s.borrow_mut() = HashMap::new());
    Ok(())
}
