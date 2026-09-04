use swc_common::{sync::Lrc, FileName, SourceMap};
use swc_ecma_ast::{EsVersion, Module as SwcModule};
use swc_ecma_parser::{lexer::Lexer, Parser as SwcParser, StringInput, Syntax, TsSyntax};
use std::{collections::HashMap, env, fs, path::Path, process::Command};
mod ir;
mod modules;
mod parser;
mod stdlib;
mod codegen;

use parser::{lex, Parser, Tok};

mod checker;
use checker::check_module_with_externs;
use codegen::Compiler;
use ir::Ty;
fn leak_str(s: &str) -> &'static str { Box::leak(s.to_string().into_boxed_str()) }

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
        // Any other bare identifier is a fixed-layout class/struct type. A class
        // used in an extern "C" signature is passed/returned BY VALUE under the
        // System V AMD64 ABI: its fields (each stored in an 8-byte slot on the
        // current class layout) become INTEGER eightbytes, register-passed for
        // small structs and stack-passed for larger ones.
        name if name != "void" => Ok(Ty::Class(leak_str(name))),
        _ => Err("void is only valid as an extern return type".into()),
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
pub(crate) enum Expr {
    Num(i64), Bool(bool), Str(Vec<u8>), Array(Vec<Expr>),
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
    ForOf(Expr, String, Vec<Stmt>),
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
#[derive(Clone, Debug)]
pub(crate) struct GlobalDecl {
    pub(crate) name: String,
    pub(crate) ty: ir::IrType,
    pub(crate) init: Expr,
}

pub(crate) const GLOBAL_INIT_FN: &str = "__nexa_globals_init";

fn inject_global_init(functions: &mut Vec<Fun>, globals: &[GlobalDecl]) {
    if globals.is_empty() { return; }
    let call = Stmt::Expr(Expr::Call(GLOBAL_INIT_FN.to_string(), vec![]));
    for f in functions.iter_mut() {
        if f.name == "main" {
            f.body.insert(0, call);
            break;
        }
    }
}

fn ty_tag(ty: ir::IrType) -> String { match ty { ir::IrType::Number => "number".into(), ir::IrType::Boolean => "boolean".into(), ir::IrType::String => "string".into(), ir::IrType::Pointer => "Pointer".into(), ir::IrType::NumberArray => "numberArray".into(), ir::IrType::ClosureNumber => "closureNumber".into(), ir::IrType::Void => "void".into(), ir::IrType::Any => "any".into(), ir::IrType::TParam => "TParam".into(), ir::IrType::Class(name) => format!("class.{name}") } }

fn main() { if let Err(e) = run() { eprintln!("nexa: {e}"); std::process::exit(1); } }
fn strip_top_level_entry_call(source: &str) -> String { source.lines().filter(|line| line.trim() != "main();").collect::<Vec<_>>().join("\n") }

fn parse_nexa(source: &str) -> Result<(Vec<ClassDecl>, Vec<Fun>, Vec<GlobalDecl>), String> {
    let (externs, clean) = extract_extern_blocks(source)?;
    parse_nexa_with_externs(&clean, &externs)
}

fn parse_nexa_with_externs(source: &str, externs: &HashMap<String, ExternSig>) -> Result<(Vec<ClassDecl>, Vec<Fun>, Vec<GlobalDecl>), String> {
    let lowered_src = strip_top_level_entry_call(source);
    let mut p = Parser { t: lex(&lowered_src)?, p: 0, unsafe_depth: 0, extern_names: externs.keys().cloned().collect(), scope_type_param: None };
    let mut classes = Vec::new();
    let mut functions = Vec::new();
    let mut globals = Vec::new();
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
        } else if matches!(p.peek(), Tok::Id(k) if k == "let" || k == "const") {
            if let Stmt::Let(n, annotation, e) = p.stmt()? {
                let ty = annotation.filter(|t| matches!(t, ir::IrType::Number | ir::IrType::Boolean | ir::IrType::String)).ok_or_else(|| format!("top-level global `{n}` requires an explicit number, boolean, or string type annotation"))?;
                globals.push(GlobalDecl { name: n, ty, init: e });
            } else {
                return Err("internal: expected a let/const declaration at top level".into());
            }
        } else {
            functions.push(p.fun()?);
        }
    }
    Ok((classes, functions, globals))
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
            Stmt::ForOf(iter, _, b) => { rewrite_generic_calls_expr(iter, pending, subst)?; rewrite_generic_calls(b, pending, subst)?; }
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
        Expr::Array(elems) => for a in elems.iter_mut() { rewrite_generic_calls_expr(a, pending, subst)?; },
        Expr::Closure(body) => rewrite_generic_calls(body, pending, subst)?,
        Expr::Num(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Var(_) => {}
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
            Stmt::ForOf(iter, _, b) => { subst_expr(iter, ty); subst_stmts(b, ty); }
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
        Expr::Array(elems) => for a in elems.iter_mut() { subst_expr(a, ty); },
        Expr::Closure(body) => subst_stmts(body, ty),
        Expr::Num(_) | Expr::Bool(_) | Expr::Str(_) | Expr::Var(_) | Expr::CallGeneric(_, _, _) => {}
    }
}

fn run() -> Result<(), String> { let a: Vec<String> = env::args().collect(); if a.len() < 2 { return Err("usage: nexa <source.ts> [-o executable]".into()); } let flat = modules::resolve_and_flatten(Path::new(&a[1]))?; let (externs, clean) = extract_extern_blocks(&flat)?; let swc_src = blank_unsafe_markers(&clean)?; let module = parse_swc_module(&swc_src, &a[1])?; check_module_with_externs(&module, &externs)?; let (classes, functions, globals) = parse_nexa_with_externs(&clean, &externs)?; let mut functions = monomorphize(functions)?; inject_global_init(&mut functions, &globals); let ir = ir::lower_program(&functions); if env::var_os("NEXA_DUMP_IR").is_some() { eprintln!("{ir}"); } let mut c = Compiler::new()?; c.register_class_layouts(&classes)?; c.declare_externs(&externs)?; c.compile(&classes, &functions, &globals)?; let obj = c.m.finish(); let objpath = "/tmp/nexa.o"; fs::write(objpath, obj.emit().map_err(|e| e.to_string())?).map_err(|e| e.to_string())?; let out = a.iter().position(|x| x == "-o").and_then(|i| a.get(i + 1)).cloned().unwrap_or_else(|| "a.out".into()); if !Path::new("runtime.c").exists() { return Err("runtime.c is missing".into()); } let status = Command::new("gcc").args([objpath, "runtime.c", "-o", &out]).status().map_err(|e| e.to_string())?; if !status.success() { return Err("link failed".into()); } println!("built {out}"); Ok(()) }

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
        let error = checker::check_module(&module)
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
                const xs: number[] = new Array<number>(1);
                return take(xs);
            }
            main();
        "#;
        let module = parse_swc_module(source, "array-any.ts").expect("SWC parse");
        checker::check_module(&module).expect("number[] should pass the checker");
        let (_, functions, _globals) = parse_nexa(source).expect("parse nexa");
        assert_eq!(functions[0].param_types, vec![ir::IrType::NumberArray]);
        assert!(matches!(
            functions[1].body.first(),
            Some(Stmt::Let(_, Some(ir::IrType::NumberArray), Expr::New(name, args)))
                if name == "Array" && args.len() == 1
        ));
        assert!(!functions.iter().any(|f| {
            f.param_types.iter().any(|t| *t == ir::IrType::Any)
                || f.return_type == ir::IrType::Any
        }));
    }

    #[test]
    fn array_length_tracks_exact_size_and_indexing_still_works() {
        // The acceptance contract for real length tracking: `new Array<number>(n)`
        // allocates exactly n zero-initialized elements and writes n into a length
        // header at array[-1]; `arr.length` reads that header; and the existing
        // arr[i] read/write path is completely unaffected (still indexes into the
        // same element buffer, at the same pointer).
        let source = r#"
            function main(): number {
              let arr: number[] = new Array<number>(3);
              arr[0] = 10;
              arr[1] = 20;
              arr[2] = 30;
              std.log(arr.length);
              std.log(arr[0]);
              std.log(arr[2]);
              return 0;
            }
            main();
        "#;
        let (classes, functions, _globals) = parse_nexa(source).expect("should parse sized array construction");
        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&HashMap::new()).expect("no externs");
        c.compile(&classes, &functions, &[]).expect("compile array program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_array_length.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_array_length"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let output = Command::new("/tmp/nexa_test_array_length").output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["3", "10", "30"],
            "length must report the exact allocation size (3) and indexing must be unchanged (10, 30)");
    }

    #[test]
    fn unsized_array_literal_is_a_compile_error() {
        // The version precludes growable arrays, so an unsized `[]` must be
        // rejected at compile time rather than silently using a placeholder
        // capacity. Sized construction via `new Array<number>(n)` is required.
        let source = r#"
            function main(): number {
              let arr: number[] = [];
              arr[0] = 5;
              return 0;
            }
            main();
        "#;
        let (externs, clean) = extract_extern_blocks(source).expect("extract extern");
        let err = compile_with_externs(&clean, &externs).expect_err("unsized [] must be rejected");
        assert!(
            err.contains("unsized array literal") || err.contains("Array"),
            "should reject unsized [] with a helpful message, got: {err}"
        );
    }

    fn build_and_run_prog(source: &str, tag: &str) -> String {
        let (classes, functions, _globals) = parse_nexa(source).expect("parse nexa program");
        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&HashMap::new()).expect("no externs");
        c.compile(&classes, &functions, &[]).expect("compile program");
        let obj = c.m.finish();
        let objpath = format!("/tmp/nexa_test_{tag}.o");
        fs::write(&objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([&objpath, "runtime.c", "-o", &format!("/tmp/nexa_test_{tag}")])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let output = Command::new(format!("/tmp/nexa_test_{tag}")).output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        String::from_utf8_lossy(&output.stdout).to_string()
    }

    fn build_and_run_prog_with_c(source: &str, c_source: &str, tag: &str) -> String {
        let (externs, clean) = extract_extern_blocks(source).expect("extract extern");
        let swc_src = blank_unsafe_markers(&clean).expect("blank unsafe markers");
        let module = parse_swc_module(&swc_src, &format!("{tag}.ts")).expect("swc parse");
        check_module_with_externs(&module, &externs).expect("type check");
        let (classes, functions, _globals) = parse_nexa_with_externs(&clean, &externs).expect("parse nexa program with externs");
        let mut c = Compiler::new().expect("compiler init");
        c.register_class_layouts(&classes).expect("register class layouts");
        c.declare_externs(&externs).expect("declare extern imports");
        c.compile(&classes, &functions, &[]).expect("compile program");
        let obj = c.m.finish();
        let objpath = format!("/tmp/nexa_test_{tag}.o");
        fs::write(&objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let cpath = format!("/tmp/nexa_test_{tag}_helpers.c");
        fs::write(&cpath, c_source).unwrap();
        let status = Command::new("gcc")
            .args([&objpath, "runtime.c", &cpath, "-o", &format!("/tmp/nexa_test_{tag}")])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed (check C helper ABI/names)");
        let output = Command::new(format!("/tmp/nexa_test_{tag}")).output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        String::from_utf8_lossy(&output.stdout).to_string()
    }

    #[test]
    fn extern_struct_point_passed_and_returned_by_value_in_registers() {
        // Point is two i64 fields = 16 bytes, so both directions travel in the
        // System V integer registers: args a/b consume RDI..RCX, the result comes
        // back in RAX:RDX. scale() spreads a 1-eightbyte struct + a scalar.
        let source = r#"
            extern "C" {
              function nexa_abi_point_add(a: Point, b: Point): Point;
              function nexa_abi_point_scale(a: Point, s: number): Point;
            }

            class Point {
              x: number;
              y: number;
              constructor(x: number, y: number) {
                this.x = x;
                this.y = y;
              }
              sum(): number {
                return this.x + this.y;
              }
            }

            function main(): number {
              let a: Point = new Point(1, 2);
              let b: Point = new Point(3, 4);
              let r: Point = unsafe { nexa_abi_point_add(a, b) };
              std.log(r.x);
              std.log(r.y);
              let s: Point = unsafe { nexa_abi_point_scale(new Point(2, 3), 10) };
              std.log(s.x);
              std.log(s.y);
              std.log(s.sum());
              return 0;
            }
            main();
        "#;
        let c_helpers = r#"
            #include <stdint.h>
            typedef struct { int64_t x, y; } Point;
            Point nexa_abi_point_add(Point a, Point b) {
                Point r = { a.x + b.x, a.y + b.y };
                return r;
            }
            Point nexa_abi_point_scale(Point a, int64_t s) {
                Point r = { a.x * s, a.y * s };
                return r;
            }
        "#;
        let out = build_and_run_prog_with_c(source, c_helpers, "abi_point");
        assert_eq!(out.lines().collect::<Vec<_>>(), vec!["4", "6", "20", "30", "50"],
            "16-byte structs must be passed/returned via registers with correct field order");
    }

    #[test]
    fn extern_struct_larger_than_16_bytes_uses_stack_arg_and_sret_return() {
        // Big3 is three i64 fields = 24 bytes > 16: the arg is a MEMORY-class
        // stack copy (Cranelift StructArgument) and the result is delivered into
        // a hidden caller-allocated sret buffer (first GPR).
        let source = r#"
            extern "C" {
              function nexa_abi_big_sum(a: Big3): Big3;
            }

            class Big3 {
              a: number;
              b: number;
              c: number;
              constructor(a: number, b: number, c: number) {
                this.a = a;
                this.b = b;
                this.c = c;
              }
            }

            function main(): number {
              let r: Big3 = unsafe { nexa_abi_big_sum(new Big3(1, 2, 3)) };
              std.log(r.a);
              std.log(r.b);
              std.log(r.c);
              return 0;
            }
            main();
        "#;
        let c_helpers = r#"
            #include <stdint.h>
            typedef struct { int64_t a, b, c; } Big3;
            Big3 nexa_abi_big_sum(Big3 v) {
                Big3 r = { v.a + 100, v.b + 200, v.c + 300 };
                return r;
            }
        "#;
        let out = build_and_run_prog_with_c(source, c_helpers, "abi_big");
        assert_eq!(out.lines().collect::<Vec<_>>(), vec!["101", "202", "303"],
            "24-byte structs must round-trip through the stack arg and sret return");
    }

    #[test]
    fn extern_struct_promoted_to_stack_when_register_window_is_exhausted() {
        // Six scalars consume all six System V GPRs (RDI..R9); the following
        // Point now has no register window left, so the whole struct must be
        // promoted to the stack (MEMORY class), then the trailing scalar too.
        let source = r#"
            extern "C" {
              function nexa_abi_gpr_exhaustion(a: number, b: number, c: number, d: number, e: number, f: number, p: Point, s: number): Point;
            }

            class Point {
              x: number;
              y: number;
              constructor(x: number, y: number) {
                this.x = x;
                this.y = y;
              }
            }

            function main(): number {
              let r: Point = unsafe { nexa_abi_gpr_exhaustion(1, 2, 3, 4, 5, 6, new Point(7, 8), 9) };
              std.log(r.x);
              std.log(r.y);
              return 0;
            }
            main();
        "#;
        let c_helpers = r#"
            #include <stdint.h>
            typedef struct { int64_t x, y; } Point;
            Point nexa_abi_gpr_exhaustion(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, Point p, int64_t s) {
                Point r = { a + b, p.x + p.y + s };
                return r;
            }
        "#;
        let out = build_and_run_prog_with_c(source, c_helpers, "abi_exh");
        assert_eq!(out.lines().collect::<Vec<_>>(), vec!["3", "24"],
            "struct must be stack-promoted once the 6 GPR registers are taken");
    }

    #[test]
    fn extern_struct_sret_consumes_first_gpr_and_pushes_later_args_to_stack() {
        // The 32-byte Quad return goes through a hidden sret buffer that sits in
        // the FIRST GPR (RDI). That hands the regular args only five GPRs, so
        // a..e get RSI/RDX/RCX/R8/R9 and f, the 16-byte Pair, and the trailing
        // scalar all spill to the stack. Every offset is exercised by values.
        let source = r#"
            extern "C" {
              function nexa_abi_sret_shifts(a: number, b: number, c: number, d: number, e: number, f: number, p: Pair, t: number): Quad;
            }

            class Pair {
              x: number;
              y: number;
              constructor(x: number, y: number) {
                this.x = x;
                this.y = y;
              }
            }

            class Quad {
              a: number;
              b: number;
              c: number;
              d: number;
              constructor(a: number, b: number, c: number, d: number) {
                this.a = a;
                this.b = b;
                this.c = c;
                this.d = d;
              }
            }

            function main(): number {
              let r: Quad = unsafe { nexa_abi_sret_shifts(1, 2, 3, 4, 5, 6, new Pair(7, 8), 9) };
              std.log(r.a);
              std.log(r.b);
              std.log(r.c);
              std.log(r.d);
              return 0;
            }
            main();
        "#;
        let c_helpers = r#"
            #include <stdint.h>
            typedef struct { int64_t x, y; } Pair;
            typedef struct { int64_t a, b, c, d; } Quad;
            Quad nexa_abi_sret_shifts(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, Pair p, int64_t t) {
                Quad r = { a + b + c + d + e + f, p.x, p.y, t };
                return r;
            }
        "#;
        let out = build_and_run_prog_with_c(source, c_helpers, "abi_sret_shift");
        assert_eq!(out.lines().collect::<Vec<_>>(), vec!["21", "7", "8", "9"],
            "sret must own RDI, leaving 5 GPRs so f, the struct, and t all go on the stack");
    }

    #[test]
    fn extern_struct_mixed_register_stack_and_trailing_scalar_after_large_struct() {
        // Quad return via sret (RDI); Pair is 16 bytes and takes RSI/RCX; the
        // 32-byte Quad arg is stack-passed in the middle; the trailing scalar
        // must still resume the register stream at RDX instead of wrongly being
        // glued onto the stack after the Quad.
        let source = r#"
            extern "C" {
              function nexa_abi_quad_sum(p: Pair, q: Quad, t: number): Quad;
            }

            class Pair {
              x: number;
              y: number;
              constructor(x: number, y: number) {
                this.x = x;
                this.y = y;
              }
            }

            class Quad {
              a: number;
              b: number;
              c: number;
              d: number;
              constructor(a: number, b: number, c: number, d: number) {
                this.a = a;
                this.b = b;
                this.c = c;
                this.d = d;
              }
            }

            function main(): number {
              let r: Quad = unsafe { nexa_abi_quad_sum(new Pair(1, 2), new Quad(10, 20, 30, 40), 5) };
              std.log(r.a);
              std.log(r.b);
              std.log(r.c);
              std.log(r.d);
              return 0;
            }
            main();
        "#;
        let c_helpers = r#"
            #include <stdint.h>
            typedef struct { int64_t x, y; } Pair;
            typedef struct { int64_t a, b, c, d; } Quad;
            Quad nexa_abi_quad_sum(Pair p, Quad q, int64_t t) {
                Quad r = { p.x + t, p.y + q.b, q.c, q.d };
                return r;
            }
        "#;
        let out = build_and_run_prog_with_c(source, c_helpers, "abi_mixed");
        assert_eq!(out.lines().collect::<Vec<_>>(), vec!["6", "22", "30", "40"],
            "large struct arg goes to the stack while adjacent scalars still use registers");
    }

    #[test]
    fn extern_struct_two_consecutive_large_struct_args_do_not_overlap_on_stack() {
        // Two 32-byte structs passed back-to-back are both MEMORY-class and must
        // land in distinct consecutive stack slots (offsets 0 and 32). Overlaps
        // or a wrong order swap the summed fields and change the result.
        let source = r#"
            extern "C" {
              function nexa_abi_two_quads(a: Quad, b: Quad): Quad;
            }

            class Quad {
              a: number;
              b: number;
              c: number;
              d: number;
              constructor(a: number, b: number, c: number, d: number) {
                this.a = a;
                this.b = b;
                this.c = c;
                this.d = d;
              }
            }

            function main(): number {
              let r: Quad = unsafe { nexa_abi_two_quads(new Quad(1, 2, 3, 4), new Quad(10, 20, 30, 40)) };
              std.log(r.a);
              std.log(r.b);
              std.log(r.c);
              std.log(r.d);
              return 0;
            }
            main();
        "#;
        let c_helpers = r#"
            #include <stdint.h>
            typedef struct { int64_t a, b, c, d; } Quad;
            Quad nexa_abi_two_quads(Quad a, Quad b) {
                Quad r = { a.a + b.a, a.b + b.b, a.c + b.c, a.d + b.d };
                return r;
            }
        "#;
        let out = build_and_run_prog_with_c(source, c_helpers, "abi_two_quads");
        assert_eq!(out.lines().collect::<Vec<_>>(), vec!["11", "22", "33", "44"],
            "consecutive large struct args must occupy distinct stack slots in order");
    }

    #[test]
    fn for_of_array_desugars_to_indexed_loop() {
        // for (const x of arr) must reduce to the existing indexed for(;;): it
        // reads arr.length for the bound and arr[__i] for each element. Values
        // are summed, so wrong length/iteration yields a wrong total.
        let source = r#"
            function main(): number {
              let arr: number[] = new Array<number>(4);
              arr[0] = 10; arr[1] = 20; arr[2] = 30; arr[3] = 40;
              let total: number = 0;
              for (const x of arr) {
                total = total + x;
              }
              std.log(total);
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "forof_arr");
        assert_eq!(out.trim(), "100", "sum of 10+20+30+40 via for...of must be 100");
    }

    #[test]
    fn for_of_copies_array_in_order_and_tracks_length() {
        // for...of yanked into a fresh array must preserve element order and the
        // destination must report the same .length as the source. The bound read
        // (arr.length) and per-element index (arr[__i]) are shared with the
        // desugared for(;;); wrong ordering or a stale length changes the result.
        let source = r#"
            function main(): number {
              let src: number[] = new Array<number>(5);
              src[0] = 7; src[1] = 14; src[2] = 21; src[3] = 28; src[4] = 35;
              let dst: number[] = new Array<number>(5);
              let i: number = 0;
              for (const x of src) {
                dst[i] = x;
                i = i + 1;
              }
              std.log(dst.length);                        // 5
              std.log(dst[0]);                            // 7
              std.log(dst[1]);                            // 14
              std.log(dst[4]);                            // 35
              let sum: number = 0;
              for (const x of dst) {
                sum = sum + x;
              }
              std.log(sum);                               // 7+14+21+28+35 = 105
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "forof_copy");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["5", "7", "14", "35", "105"],
            "copy via for...of must preserve length, order, and sum 105");
    }

    #[test]
    fn array_literal_with_inline_elements() {
        // [e0, ..., en] must lower to the same fixed-size-header allocation as
        // new Array<number>(n): a length header (read via arr.length) at array[-1]
        // and each element stored in order via indexed stores. Reading the stored
        // elements shows correct element order and values; iterating with for...of
        // (which reads the same length header + elements) behaves identically.
        let source = r#"
            function main(): number {
              let arr: number[] = [10, 20, 30];
              std.log(arr.length); // 3
              std.log(arr[0]);     // 10
              std.log(arr[1]);     // 20
              std.log(arr[2]);     // 30

              let x: number = 5;
              let computed: number[] = [x, x + 1, x * 2];
              std.log(computed[0]); // 5
              std.log(computed[1]); // 6
              std.log(computed[2]); // 10

              let total: number = 0;
              for (const v of [1, 2, 3]) {
                total = total + v;
              }
              std.log(total);       // 6
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "arrlit");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["3", "10", "20", "30", "5", "6", "10", "6"],
            "inline array literals must store elements in order with a correct length header");
    }

    #[test]
    fn for_of_string_desugars_to_strlen_charat_loop() {
        // for (const ch of s) must reduce to std.strlen(s) for the bound and
        // std.charAt(s, __i) for each element. Counting the chars of a string
        // exercises the strlen bound; extracting chars exercises charAt.
        let source = r#"
            function main(): number {
              let count: number = 0;
              for (const ch of "hello") {
                count = count + 1;
              }
              std.log(count);
              let chsum: string = "";
              for (const ch of "ab") {
                chsum = chsum + ch;
              }
              std.log(chsum);
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "forof_str");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["5", "ab"],
            "for...of over a string must count 5 chars and rebuild \"ab\" from charAt");
    }

    #[test]
    fn std_strlen_reports_byte_length() {
        let source = r#"
            function main(): number {
              std.log(std.strlen(""));
              std.log(std.strlen("hello"));
              std.log(std.strlen("a\x00b"));
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "strlen");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["0", "5", "3"],
            "strlen must read the stored length header (byte-accurate, not NUL-truncated): 0, 5, and 3 for \"a\\x00b\"");
    }

    #[test]
    fn concat_str_counts_embedded_nuls_in_result_length() {
        // Concatenating a string containing an embedded NUL must carry the full
        // byte length through the header, not truncate at the NUL. This is the
        // core regression the length-header work fixes: previously the result
        // would report its length as 1 (scanning stopped at the first NUL).
        let source = r#"
            function main(): number {
              std.log(std.strlen("foo" + "\x00" + "bar"));
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "concat_nul");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["7"],
            "concat must keep the embedded-NUL byte in the concatenated length: expected 7");
    }

    #[test]
    fn std_net_sockaddr_in_binds_socket() {
        // std.net.sockaddrIn must build a real struct sockaddr_in (proper
        // htons/htonl network byte order) that is valid enough to bind a real
        // IPv4 socket to. bind returns 0 on success.
        //
        // Port 0 asks the kernel to assign an ephemeral port. This is deliberate:
        // binding a fixed port (as the HTTP server does with 5000) would make the
        // test collide with leftover TIME_WAIT sockets on that port (the regression
        // test does not set SO_REUSEADDR), causing EADDRINUSE and flaky failures.
        // The socket is closed immediately, so no resource lingers.
        let source = r#"
            function main(): number {
              let addr: Pointer = std.net.sockaddrIn(0, 0);
              let fd: number = unsafe { std.net.socket(2, 1, 0) };
              let bound: number = unsafe { std.net.bind(fd, addr, 16) };
              std.log(bound);
              unsafe { std.net.close(fd); }
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "std_net_bind");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["0"],
            "std.net.sockaddrIn+socket+bind must bind successfully (return 0)");
    }

    #[test]
    fn std_process_fork_child_and_parent_both_log_then_wait() {
        // fork hands back 0 to the child and the child's PID to the parent.
        // Both must log their line; "child exited" (after waitpid) must come
        // last. The first two lines may appear in either order due to real
        // process scheduling. nexa_process_exit flushes so the child's own
        // buffered output survives the (fully-buffered, piped) capture.
        let source = r#"
            function main(): number {
              let pid: number = unsafe { std.process.fork() };
              if (pid == 0) {
                std.log("child running");
                unsafe { std.process.exit(0); }
                return 0;
              } else {
                std.log("parent waiting");
                let status: number = unsafe { std.process.wait(pid) };
                std.log("child exited");
                return 0;
              }
            }
            main();
        "#;
        let out = build_and_run_prog(source, "std_process_fork");
        let lines: Vec<&str> = out.lines().collect();
        assert!(lines.contains(&"child running"), "child must log 'child running', got {lines:?}");
        assert!(lines.contains(&"parent waiting"), "parent must log 'parent waiting', got {lines:?}");
        assert_eq!(lines.last().copied(), Some("child exited"),
            "'child exited' must be the last line (after wait), got {lines:?}");
    }

    #[test]
    fn std_process_pipe_returns_two_distinct_fds() {
        // pipe() must hand back a pointer to two real, distinct, non-negative
        // file descriptors (read at index 0, write at index 1).
        let source = r#"
            function main(): number {
              let p: Pointer = unsafe { std.process.pipe() };
              let readFd: number = std.process.pipeReadFd(p);
              let writeFd: number = std.process.pipeWriteFd(p);
              std.log(readFd);
              std.log(writeFd);
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "std_process_pipe");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines.len(), 2, "expected two fd lines, got {lines:?}");
        let read_fd: i64 = lines[0].parse().expect("read fd must be a number");
        let write_fd: i64 = lines[1].parse().expect("write fd must be a number");
        assert!(read_fd >= 0 && write_fd >= 0, "fds must be non-negative, got {lines:?}");
        assert_ne!(read_fd, write_fd, "read and write fds must be distinct, got {lines:?}");
    }

    #[test]
    fn std_charat_extracts_one_character_string() {
        // std.charAt returns a NEW one-character Nexa string (no separate char
        // type). Verifying its own length is 1 and its content matches.
        let source = r#"
            function main(): number {
              std.log(std.charAt("hello", 0));
              std.log(std.charAt("hello", 2));
              std.log(std.strlen(std.charAt("hi", 1)));
              return 0;
            }
            main();
        "#;
        let out = build_and_run_prog(source, "charat");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["h", "l", "1"],
            "charAt must return h, l, and a length-1 string");
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
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle classes");
        assert_eq!(classes.len(), 1, "should parse one class");
        assert_eq!(classes[0].name, "Counter");
        assert_eq!(classes[0].fields.len(), 1);
        assert_eq!(classes[0].fields[0].0, "count");
        assert!(!functions.is_empty(), "should have main function");

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions, &[]).expect("compile classes and methods");
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
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle extern/unsafe");
        assert!(classes.is_empty());
        let (externs, _) = extract_extern_blocks(source).expect("extract extern signatures");
        assert_eq!(externs.len(), 2);
        assert_eq!(externs["malloc"].params, vec![Ty::Number]);
        assert_eq!(externs["malloc"].ret, Ty::Pointer);
        assert_eq!(externs["free"].ret, Ty::Void);

        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&externs).expect("declare extern imports");
        c.compile(&classes, &functions, &[]).expect("compile extern program");
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
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle the std namespace");
        assert!(matches!(
            functions[0].body.first(),
            Some(Stmt::Expr(Expr::Call(n, _))) if n == "std.log"
        ));
        assert!(functions[0].body.iter().any(|s| matches!(
            s,
            Stmt::Let(_, Some(ir::IrType::String), Expr::Call(n, args)) if n == "std.in" && args.is_empty()
        )));

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions, &[]).expect("compile std program");
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
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle generic declarations and call sites");
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
        c.compile(&classes, &mono, &[]).expect("compile monomorphized program");
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
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle std.parseNumber");
        assert!(functions[0].body.iter().any(|s| matches!(
            s,
            Stmt::Let(_, Some(ir::IrType::Number), Expr::Call(n, args)) if n == "std.parseNumber" && args.len() == 1
        )));

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions, &[]).expect("compile parseNumber program");
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
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle std.parseNumber");
        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions, &[]).expect("compile parseNumber program");
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
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle string fields");
        assert_eq!(classes.len(), 1, "should parse one class");
        assert_eq!(classes[0].name, "Person");
        assert_eq!(classes[0].fields.len(), 1);
        assert_eq!(classes[0].fields[0].0, "name");
        assert_eq!(classes[0].fields[0].1, ir::IrType::String);

        let mut c = Compiler::new().expect("compiler init");
        c.compile(&classes, &functions, &[]).expect("compile classes and methods");
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
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle Pointer fields and std.toCString");
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
        c.compile(&classes, &functions, &[]).expect("compile pointer field + toCString program");
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
    fn from_cstring_roundtrip_copies_not_aliases() {
        // Round-trip: toCString -> fromCString must reproduce the exact bytes,
        // and fromCString must COPY (not alias), so the returned string stays
        // valid even after the source Pointer's buffer is freed. The source is
        // a heap string (built by concat) so free() is legal.
        let source = r#"
            extern "C" {
              function nexa_str_free(ptr: Pointer): void;
            }
            function main(): number {
              let original: string = "he" + "llo";
              let asPtr: Pointer = std.toCString(original);
              let back: string = std.fromCString(asPtr, 5);
              unsafe { nexa_str_free(asPtr); }
              std.log(back);
              std.log(back + " world");
              return 0;
            }
        "#;
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle std.fromCString");
        let (externs, _) = extract_extern_blocks(source).expect("extract extern signatures");
        assert_eq!(externs.len(), 1);
        assert_eq!(externs["nexa_str_free"].params, vec![Ty::Pointer]);

        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&externs).expect("declare extern imports");
        c.compile(&classes, &functions, &[]).expect("compile fromCString program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_from_cstring.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_from_cstring"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed: nexa_str_free must resolve against runtime.c");
        let output = Command::new("/tmp/nexa_test_from_cstring").output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines, vec!["hello", "hello world"],
            "fromCString must copy the buffer so it survives freeing the source, and remain concatenable");
    }

    #[test]
    fn from_cstring_preserves_embedded_nuls_with_explicit_length() {
        // fromCString takes an explicit length and does a raw byte copy, so a
        // buffer with embedded NUL bytes (like a recv() result) must not be
        // truncated. Writes all 5 bytes of "a\0b\0c" and checks them exactly.
        let source = r#"
            extern "C" {
              function write(fd: number, buf: Pointer, n: number): number;
            }
            function main(): number {
              let blob: string = "a\x00b\x00c";
              let p: Pointer = std.toCString(blob);
              let s: string = std.fromCString(p, 5);
              unsafe { write(1, std.toCString(s), 5); }
              return 0;
            }
        "#;
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle \\x00 escapes and std.fromCString");
        let (externs, _) = extract_extern_blocks(source).expect("extract extern signatures");
        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&externs).expect("declare extern imports");
        c.compile(&classes, &functions, &[]).expect("compile embedded-nul fromCString program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_from_cstring_nul.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_from_cstring_nul"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed: write must resolve against libc");
        let output = Command::new("/tmp/nexa_test_from_cstring_nul").output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        assert_eq!(output.stdout, vec![b'a', 0x00, b'b', 0x00, b'c'],
            "explicit-length fromCString must preserve embedded NUL bytes in order");
    }

    #[test]
    fn string_eq_compares_content_not_pointer_identity() {
        // The case literal-only testing would silently miss: the compiler
        // DEDUPLICATES identical string literals to the same buffer, so "a==b"
        // over two equal literals passes even under pointer-identity equality.
        // Only comparing a runtime-built (concatenated) string against a
        // literal -- which live at different addresses -- can detect that ==
        // must compare bytes, not pointers.
        let source = r#"
            function main(): number {
              let a: string = "Hello, " + "World!";
              let b: string = "Hello, World!";
              if (a == b) {
                std.log("concat equals literal: correct");
              } else {
                std.log("BUG: same content reported unequal");
              }
              return 0;
            }
        "#;
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle string concat and ==");
        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&HashMap::new()).expect("no externs");
        c.compile(&classes, &functions, &[]).expect("compile string == program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_str_eq.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_str_eq"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let output = Command::new("/tmp/nexa_test_str_eq").output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains("concat equals literal: correct"),
            "equal string content must compare equal regardless of pointer identity, got: {stdout}");
    }

    #[test]
    fn string_eq_distinguishes_different_content() {
        // Guard that the content fix does not collapse to "everything equal":
        // truly different bytes must still report != .
        let source = r#"
            function main(): number {
              let a: string = "Hello, " + "World!";
              let b: string = "Hello, Tiold!";
              if (a == b) {
                std.log("BUG: different content reported equal");
              } else {
                std.log("correctly distinguished");
              }
              return 0;
            }
        "#;
        let (classes, functions, _globals) = parse_nexa(source).expect("parser should handle string concat and ==");
        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&HashMap::new()).expect("no externs");
        c.compile(&classes, &functions, &[]).expect("compile string == program");
        let obj = c.m.finish();
        let objpath = "/tmp/nexa_test_str_eq_neq.o";
        fs::write(objpath, obj.emit().map_err(|e| e.to_string()).unwrap()).unwrap();
        let status = Command::new("gcc")
            .args([objpath, "runtime.c", "-o", "/tmp/nexa_test_str_eq_neq"])
            .status()
            .unwrap();
        assert!(status.success(), "gcc link failed");
        let output = Command::new("/tmp/nexa_test_str_eq_neq").output().unwrap();
        assert!(output.status.success(), "program must exit cleanly");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains("correctly distinguished"),
            "different string content must NOT compare equal, got: {stdout}");
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
        let (classes, functions, _globals) = parse_nexa_with_externs(&clean, &externs).expect("parse funcPtr program");
        let mut c = Compiler::new().expect("compiler init");
        c.declare_externs(&externs).expect("declare externs");
        c.compile(&classes, &functions, &[]).expect("compile funcPtr program");
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

    fn scratch_dir(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("nexa_globals_{}__{}", name, std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        dir
    }
    fn write_module(dir: &std::path::Path, file: &str, src: &str) -> std::path::PathBuf {
        let p = dir.join(file);
        fs::write(&p, src).unwrap();
        p
    }
    fn build_and_run(entry: &std::path::Path) -> Result<String, String> {
        let flat = crate::modules::resolve_and_flatten(entry)?;
        let (externs, clean) = extract_extern_blocks(&flat)?;
        let swc_src = blank_unsafe_markers(&clean)?;
        let filename = entry.file_name().unwrap_or_default().to_string_lossy().to_string();
        let module = parse_swc_module(&swc_src, &filename)?;
        check_module_with_externs(&module, &externs)?;
        let (classes, functions, globals) = parse_nexa_with_externs(&clean, &externs)?;
        let mut functions = monomorphize(functions)?;
        inject_global_init(&mut functions, &globals);
        let mut c = Compiler::new().map_err(|e| e.to_string())?;
        c.register_class_layouts(&classes)?;
        c.declare_externs(&externs)?;
        c.compile(&classes, &functions, &globals)?;
        let unique = entry.parent().unwrap_or(Path::new("/tmp")).join(entry.file_stem().unwrap_or_default());
        let objpath = unique.with_extension("o");
        fs::write(&objpath, c.m.finish().emit().map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
        let out = unique.with_extension("bin");
        let status = Command::new("gcc").args([objpath.to_str().unwrap(), "runtime.c", "-o", out.to_str().unwrap()]).status().map_err(|e| e.to_string())?;
        if !status.success() { return Err("gcc link failed".into()); }
        let output = Command::new(&out).output().map_err(|e| e.to_string())?;
        if !output.status.success() { return Err(format!("program failed: {}", String::from_utf8_lossy(&output.stderr))); }
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
    fn build_error(entry: &std::path::Path) -> Result<(), String> {
        let flat = crate::modules::resolve_and_flatten(entry)?;
        let (externs, clean) = extract_extern_blocks(&flat)?;
        let swc_src = blank_unsafe_markers(&clean)?;
        let filename = entry.file_name().unwrap_or_default().to_string_lossy().to_string();
        let module = parse_swc_module(&swc_src, &filename)?;
        check_module_with_externs(&module, &externs)?;
        let (classes, functions, globals) = parse_nexa_with_externs(&clean, &externs)?;
        let mut functions = monomorphize(functions)?;
        inject_global_init(&mut functions, &globals);
        let mut c = Compiler::new().map_err(|e| e.to_string())?;
        c.declare_externs(&externs)?;
        c.compile(&classes, &functions, &globals)?;
        Ok(())
    }

    #[test]
    fn module_global_export_import_acceptance() {
        let dir = scratch_dir("acceptance");
        write_module(&dir, "state.ts", r#"
            export let counter: number = 0;

            export function increment(): number {
              counter = counter + 1;
              return counter;
            }
        "#);
        let entry = write_module(&dir, "main.ts", r#"
            import { counter, increment } from "./state.ts";

            function main(): number {
              std.log(increment());  // 1
              std.log(increment());  // 2
              counter = 0;
              std.log(counter);       // 0
              std.log(increment());   // 1
              return 0;
            }
        "#);
        let out = build_and_run(&entry).expect("acceptance program must compile and run");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["1", "2", "0", "1"],
            "imported global must be shared, readable and writable from the importing file");
    }

    #[test]
    fn module_global_read_write_boolean_string() {
        let dir = scratch_dir("boolstring");
        write_module(&dir, "state.ts", r#"
            export let flag: boolean = false;
            export let label: string = "hi";
        "#);
        let entry = write_module(&dir, "main.ts", r#"
            import { flag, label } from "./state.ts";

            function main(): number {
              flag = true;
              std.log(flag);   // true
              std.log(label);  // hi
              flag = false;
              std.log(flag);   // false
              return 0;
            }
        "#);
        let out = build_and_run(&entry).expect("boolean/string globals must compile and run");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["true", "hi", "false"]);
    }

    #[test]
    fn module_global_cross_file_init_order_is_dependency_first() {
        let dir = scratch_dir("initorder");
        write_module(&dir, "dep.ts", r#"
            export let base: number = 10;
            export let derived: number = base + 5;
        "#);
        let entry = write_module(&dir, "main.ts", r#"
            import { base, derived } from "./dep.ts";

            let own: number = derived + 1;

            function main(): number {
              std.log(base);     // 10
              std.log(derived);  // 15
              std.log(own);      // 16
              return 0;
            }
        "#);
        let out = build_and_run(&entry).expect("cross-file init order must compile and run");
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines, vec!["10", "15", "16"],
            "an imported file's globals must initialize before the importer's own globals");
    }

    #[test]
    fn global_forward_reference_same_file_is_error() {
        let dir = scratch_dir("fwd");
        let entry = write_module(&dir, "main.ts", r#"
            let b: number = a + 1;
            let a: number = 5;
            function main(): number { return 0; }
        "#);
        let err = build_error(&entry).unwrap_err();
        assert!(err.contains("forward-reference"), "expected forward-reference error, got: {err}");
        assert!(err.contains("declaration order"), "expected order message, got: {err}");
    }

    #[test]
    fn global_cross_file_forward_reference_cycle_is_circular_import() {
        let dir = scratch_dir("circ");
        write_module(&dir, "a.ts", r#"
            import { b } from "./b.ts";
            let a: number = b + 1;
            export { a };
        "#);
        write_module(&dir, "b.ts", r#"
            import { a } from "./a.ts";
            let b: number = a + 1;
            export { b };
        "#);
        let entry = write_module(&dir, "main.ts", r#"
            import { a } from "./a.ts";
            function main(): number {
              std.log(a);
              return 0;
            }
        "#);
        let err = build_error(&entry).unwrap_err();
        assert!(err.contains("circular import"), "cross-file global cycle must be caught by circular-import detection, got: {err}");
    }
}

fn compile_with_externs(source: &str, externs: &HashMap<String, ExternSig>) -> Result<(), String> {
    let (classes, functions, _globals) = parse_nexa_with_externs(source, externs)?;
    let mut c = Compiler::new().map_err(|e| e.to_string())?;
    c.register_class_layouts(&classes)?;
    c.declare_externs(externs)?;
    c.compile(&classes, &functions, &[])?;
    Ok(())
}

