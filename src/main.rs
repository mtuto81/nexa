use swc_common::{sync::Lrc, FileName, SourceMap};
use swc_ecma_ast::{EsVersion, Module as SwcModule};
use swc_ecma_parser::{lexer::Lexer, Parser as SwcParser, StringInput, Syntax, TsSyntax};
use std::{collections::HashMap, env, fs, path::Path, process::Command};
mod ir;
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

fn ty_tag(ty: ir::IrType) -> String { match ty { ir::IrType::Number => "number".into(), ir::IrType::Boolean => "boolean".into(), ir::IrType::String => "string".into(), ir::IrType::Pointer => "Pointer".into(), ir::IrType::NumberArray => "numberArray".into(), ir::IrType::ClosureNumber => "closureNumber".into(), ir::IrType::Void => "void".into(), ir::IrType::Any => "any".into(), ir::IrType::TParam => "TParam".into(), ir::IrType::Class(name) => format!("class.{name}") } }

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
                const xs: number[] = [];
                return take(xs);
            }
            main();
        "#;
        let module = parse_swc_module(source, "array-any.ts").expect("SWC parse");
        checker::check_module(&module).expect("number[] should pass the checker");
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

