use cranelift_codegen::ir::{types, AbiParam, Function, InstBuilder, Signature, Value};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use swc_common::{sync::Lrc, FileName, SourceMap};
use swc_ecma_ast::{AssignOp, BinaryOp, Callee, Decl, EsVersion, Expr as SExpr, Lit, MemberProp, Module as SwcModule, ModuleItem, Pat, Stmt as SStmt, TsKeywordTypeKind, TsType};
use swc_ecma_parser::{lexer::Lexer, Parser as SwcParser, StringInput, Syntax, TsSyntax};
use std::{collections::HashMap, env, fs, path::Path, process::Command};
mod ir;

#[derive(Clone, Copy, Debug, PartialEq, Eq)] enum Ty { Number, Boolean, String, NumberArray, Void, Any }
#[derive(Clone, Debug)] struct FnSig { params: Vec<Ty>, ret: Ty }

fn type_annotation(ann: Option<&swc_ecma_ast::TsTypeAnn>) -> Result<Option<Ty>, String> {
    let Some(ann) = ann else { return Ok(None); };
    match &*ann.type_ann {
        TsType::TsKeywordType(k) => Ok(Some(match k.kind { TsKeywordTypeKind::TsNumberKeyword => Ty::Number, TsKeywordTypeKind::TsBooleanKeyword => Ty::Boolean, TsKeywordTypeKind::TsStringKeyword => Ty::String, TsKeywordTypeKind::TsVoidKeyword => Ty::Void, TsKeywordTypeKind::TsAnyKeyword => return Err("Nexa does not compile any through the raw typed ABI; use a concrete type".into()), _ => return Err("Nexa supports only number, boolean, string, void, and number[] type annotations".into()) })),
        TsType::TsArrayType(a) => match &*a.elem_type { TsType::TsKeywordType(k) if k.kind == TsKeywordTypeKind::TsNumberKeyword => Ok(Some(Ty::NumberArray)), _ => Err("Nexa currently supports only number[] arrays".into()) },
        TsType::TsUnionOrIntersectionType(_) => Err("Nexa union/intersection type checking is not implemented yet".into()),
        _ => Err("Nexa type-level checker supports only scalar keyword types".into()),
    }
}

fn compatible(expected: Ty, actual: Ty) -> bool { expected == actual }
fn required_type(ann: Option<&swc_ecma_ast::TsTypeAnn>, what: &str) -> Result<Ty, String> { type_annotation(ann)?.ok_or_else(|| format!("Nexa requires a concrete type for {what}; implicit any cannot enter native code")) }
fn check_expr(e: &SExpr, env: &HashMap<String, Ty>, fns: &HashMap<String, FnSig>) -> Result<Ty, String> {
    match e {
        SExpr::Lit(Lit::Num(_)) => Ok(Ty::Number), SExpr::Lit(Lit::Bool(_)) => Ok(Ty::Boolean), SExpr::Lit(Lit::Str(_)) => Ok(Ty::String),
        SExpr::Lit(_) => Err("Nexa supports only number, boolean, and string literals".into()),
        SExpr::Ident(i) => env.get(i.sym.as_ref()).copied().ok_or_else(|| format!("unknown variable {}", i.sym)),
        SExpr::Paren(p) => check_expr(&p.expr, env, fns), SExpr::TsAs(a) => check_expr(&a.expr, env, fns), SExpr::TsNonNull(n) => check_expr(&n.expr, env, fns),
        SExpr::Unary(u) => { let t = check_expr(&u.arg, env, fns)?; match u.op { swc_ecma_ast::UnaryOp::Bang => { if t != Ty::Boolean && t != Ty::Any { return Err("! expects boolean".into()); } Ok(Ty::Boolean) }, swc_ecma_ast::UnaryOp::Minus | swc_ecma_ast::UnaryOp::Plus => { if t != Ty::Number && t != Ty::Any { return Err("numeric unary operator expects number".into()); } Ok(Ty::Number) }, _ => Err("unsupported unary operator in Nexa".into()) } }
        SExpr::Bin(b) => { let l = check_expr(&b.left, env, fns)?; let r = check_expr(&b.right, env, fns)?; match b.op { BinaryOp::Add => { if l == Ty::String && r == Ty::String { Ok(Ty::String) } else if compatible(Ty::Number, l) && compatible(Ty::Number, r) { Ok(Ty::Number) } else { Err("+ expects two numbers or two strings".into()) } }, BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => { if !compatible(Ty::Number, l) || !compatible(Ty::Number, r) { return Err("arithmetic operators expect numbers".into()); } Ok(Ty::Number) }, BinaryOp::LogicalAnd | BinaryOp::LogicalOr => { if !compatible(Ty::Boolean, l) || !compatible(Ty::Boolean, r) { return Err("logical operators expect booleans".into()); } Ok(Ty::Boolean) }, BinaryOp::EqEq | BinaryOp::NotEq | BinaryOp::EqEqEq | BinaryOp::NotEqEq | BinaryOp::Lt | BinaryOp::LtEq | BinaryOp::Gt | BinaryOp::GtEq => { if l != Ty::Any && r != Ty::Any && l != r { return Err("comparison operands must have compatible types".into()); } Ok(Ty::Boolean) }, _ => Err("unsupported binary operator in Nexa".into()) } }
        SExpr::Array(a) => { for x in a.elems.iter().flatten() { if check_expr(&x.expr, env, fns)? != Ty::Number { return Err("Nexa arrays currently contain only numbers".into()); } } Ok(Ty::NumberArray) }
        SExpr::Member(m) => { let object = check_expr(&m.obj, env, fns)?; if object != Ty::NumberArray && object != Ty::Any { return Err("indexed access requires a number[]".into()); } if let MemberProp::Computed(c) = &m.prop { if !compatible(Ty::Number, check_expr(&c.expr, env, fns)?) { return Err("array index must be a number".into()); } } Ok(Ty::Number) }
        SExpr::Assign(a) => { let new = check_expr(&a.right, env, fns)?; match &a.left { swc_ecma_ast::AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Ident(i)) => { let name = i.id.sym.to_string(); let old = env.get(&name).copied().ok_or_else(|| format!("unknown variable {name}"))?; if a.op != AssignOp::Assign && old != Ty::Number { return Err("compound assignment requires number".into()); } if !compatible(old, new) { return Err(format!("cannot assign {new:?} to {old:?}")); } Ok(old) }, swc_ecma_ast::AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Member(m)) => { if a.op != AssignOp::Assign { return Err("compound array assignment is not implemented".into()); } let object = check_expr(&m.obj, env, fns)?; if object != Ty::NumberArray && object != Ty::Any { return Err("indexed assignment requires a number[]".into()); } if let MemberProp::Computed(c) = &m.prop { if !compatible(Ty::Number, check_expr(&c.expr, env, fns)?) { return Err("array index must be a number".into()); } } if !compatible(Ty::Number, new) { return Err("number[] elements must be numbers".into()); } Ok(Ty::Number) }, _ => Err("Nexa assignments require a local identifier or array element".into()) } }
        SExpr::Call(c) => { let name = match &c.callee { Callee::Expr(x) => match &**x { SExpr::Ident(i) => i.sym.to_string(), SExpr::Member(m) if matches!(&m.obj.as_ref(), SExpr::Ident(i) if i.sym == "console") && matches!(&m.prop, MemberProp::Ident(i) if i.sym == "log") => "console.log".into(), _ => return Err("Nexa calls require a named function".into()) }, _ => return Err("unsupported call target".into()) }; if name == "console.log" { if c.args.len() != 1 { return Err("console.log accepts one argument".into()); } check_expr(&c.args[0].expr, env, fns)?; return Ok(Ty::Void); } let sig = fns.get(&name).ok_or_else(|| format!("unknown function {name}"))?; if sig.params.len() != c.args.len() { return Err(format!("function {name} expects {} arguments", sig.params.len())); } for (p, a) in sig.params.iter().zip(&c.args) { let t = check_expr(&a.expr, env, fns)?; if !compatible(*p, t) { return Err(format!("argument type {t:?} does not match {p:?}")); } } Ok(sig.ret) }
        _ => Err("unsupported expression in Nexa type checker".into()),
    }
}

fn check_stmt(s: &SStmt, env: &mut HashMap<String, Ty>, fns: &HashMap<String, FnSig>, ret: Ty) -> Result<(), String> {
    match s {
        SStmt::Decl(Decl::Var(v)) => for d in &v.decls { let Pat::Ident(i) = &d.name else { return Err("Nexa local declarations require identifiers".into()); }; let actual = d.init.as_ref().map(|x| check_expr(x, env, fns)).transpose()?.unwrap_or(Ty::Any); if actual == Ty::Any { return Err(format!("Nexa requires an initializer or concrete annotation for {}", i.id.sym)); } let declared = type_annotation(i.type_ann.as_deref())?.unwrap_or(actual); if !compatible(declared, actual) { return Err(format!("initializer type {actual:?} does not match {declared:?}")); } env.insert(i.id.sym.to_string(), declared); },
        SStmt::Expr(e) => { check_expr(&e.expr, env, fns)?; },
        SStmt::Return(r) => { let actual = r.arg.as_ref().map(|x| check_expr(x, env, fns)).transpose()?.unwrap_or(Ty::Void); if !compatible(ret, actual) { return Err(format!("return type {actual:?} does not match {ret:?}")); } },
        SStmt::Block(b) => for s in &b.stmts { check_stmt(s, env, fns, ret)?; },
        SStmt::If(i) => { let t = check_expr(&i.test, env, fns)?; if t != Ty::Boolean && t != Ty::Any { return Err("if condition must be boolean".into()); } check_stmt(&i.cons, env, fns, ret)?; if let Some(a) = &i.alt { check_stmt(a, env, fns, ret)?; } },
        SStmt::While(w) => { let t = check_expr(&w.test, env, fns)?; if t != Ty::Boolean && t != Ty::Any { return Err("while condition must be boolean".into()); } check_stmt(&w.body, env, fns, ret)?; },
        SStmt::For(f) => { if let Some(init) = &f.init { match init { swc_ecma_ast::VarDeclOrExpr::VarDecl(v) => for d in &v.decls { let Pat::Ident(i) = &d.name else { return Err("Nexa for declarations require identifiers".into()); }; let actual = d.init.as_ref().map(|x| check_expr(x, env, fns)).transpose()?.unwrap_or(Ty::Any); let declared = type_annotation(i.type_ann.as_deref())?.unwrap_or(actual); if !compatible(declared, actual) { return Err(format!("initializer type {actual:?} does not match {declared:?}")); } env.insert(i.id.sym.to_string(), declared); }, swc_ecma_ast::VarDeclOrExpr::Expr(e) => { check_expr(e, env, fns)?; } } } if let Some(test) = &f.test { let t = check_expr(test, env, fns)?; if t != Ty::Boolean && t != Ty::Any { return Err("for condition must be boolean".into()); } } if let Some(update) = &f.update { check_expr(update, env, fns)?; } check_stmt(&f.body, env, fns, ret)?; },
        SStmt::Empty(_) => {},
        _ => return Err("unsupported statement in Nexa type checker".into()),
    } Ok(())
}

fn check_module(module: &SwcModule) -> Result<(), String> {
    let mut fns = HashMap::new();
    for item in &module.body { if let ModuleItem::Stmt(SStmt::Decl(Decl::Fn(f))) = item { let params = f.function.params.iter().map(|p| match &p.pat { Pat::Ident(i) => required_type(i.type_ann.as_deref(), "function parameter"), _ => Err("Nexa function parameters require identifiers".into()) }).collect::<Result<Vec<_>, String>>()?; let ret = required_type(f.function.return_type.as_deref(), "function return type")?; fns.insert(f.ident.sym.to_string(), FnSig { params, ret }); } }
    for item in &module.body { if let ModuleItem::Stmt(SStmt::Decl(Decl::Fn(f))) = item { let mut env = HashMap::new(); for p in &f.function.params { let Pat::Ident(i) = &p.pat else { return Err("Nexa function parameters require identifiers".into()); }; env.insert(i.id.sym.to_string(), required_type(i.type_ann.as_deref(), "function parameter")?); } let ret = required_type(f.function.return_type.as_deref(), "function return type")?; if let Some(body) = &f.function.body { for s in &body.stmts { check_stmt(s, &mut env, &fns, ret)?; } } } }
    Ok(())
}

fn parse_typescript(source: &str, filename: &str) -> Result<(), String> {
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
    check_module(&module)?;
    Ok(())
}

#[derive(Clone, Debug)]
enum Tok { Id(String), Num(i64), Str(String), True, False, Plus, Minus, Star, Slash, Percent, Eq, EqEq, NotEq, Lt, Le, Gt, Ge, Bang, And, Or, Colon, Dot, LParen, RParen, LBrace, RBrace, LBracket, RBracket, Comma, Semi, Eof }

fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let mut out = Vec::new(); let b = s.as_bytes(); let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_whitespace() { i += 1; continue; }
        if i + 1 < b.len() && b[i] == b'/' && b[i + 1] == b'/' { while i < b.len() && b[i] != b'\n' { i += 1; } continue; }
        if i + 1 < b.len() {
            if i + 3 <= b.len() && &s[i..i + 3] == "===" { out.push(Tok::EqEq); i += 3; continue; }
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

#[derive(Clone, Debug)] pub(crate) enum Expr { Num(i64), Bool(bool), Str(String), Array, Index(Box<Expr>, Box<Expr>), Var(String), Unary(char, Box<Expr>), Bin(Box<Expr>, String, Box<Expr>), Call(String, Vec<Expr>) }
#[derive(Clone, Debug)] pub(crate) enum Stmt { Let(String, Expr), Assign(String, Expr), IndexAssign(Expr, Expr, Expr), Return(Expr), Expr(Expr), If(Expr, Vec<Stmt>, Vec<Stmt>), While(Expr, Vec<Stmt>), For(Box<Stmt>, Expr, Box<Stmt>, Vec<Stmt>) }
#[derive(Clone, Debug)] pub(crate) struct Fun { pub(crate) name: String, pub(crate) params: Vec<String>, pub(crate) param_types: Vec<ir::IrType>, pub(crate) return_type: ir::IrType, pub(crate) body: Vec<Stmt> }

struct Parser { t: Vec<Tok>, p: usize }
impl Parser {
    fn peek(&self) -> &Tok { &self.t[self.p] }
    fn eat(&mut self) -> Tok { let x = self.t[self.p].clone(); self.p += 1; x }
    fn id(&mut self) -> Result<String, String> { match self.eat() { Tok::Id(x) => Ok(x), x => Err(format!("expected identifier, got {x:?}")) } }
    fn expect(&mut self, f: fn(&Tok) -> bool, msg: &str) -> Result<(), String> { if f(self.peek()) { self.eat(); Ok(()) } else { Err(msg.into()) } }
    fn annotation(&mut self) -> Result<Option<ir::IrType>, String> { if matches!(self.peek(), Tok::Colon) { self.eat(); let ty = self.id()?; let array = if matches!(self.peek(), Tok::LBracket) { self.eat(); self.expect(|x| matches!(x, Tok::RBracket), "expected ] in type annotation")?; true } else { false }; return Ok(Some(if array { ir::IrType::Any } else { match ty.as_str() { "number" => ir::IrType::Number, "string" => ir::IrType::String, "boolean" => ir::IrType::Boolean, "void" => ir::IrType::Void, "any" => ir::IrType::Any, _ => return Err(format!("unsupported type annotation: {ty}")) } })); } Ok(None) }
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
    fn atom(&mut self) -> Result<Expr, String> { let mut x = match self.eat() {
        Tok::Num(x) => Expr::Num(x), Tok::True => Expr::Bool(true), Tok::False => Expr::Bool(false), Tok::Str(x) => Expr::Str(x), Tok::LBracket => { self.expect(|x| matches!(x, Tok::RBracket), "Nexa currently supports only empty array literals")?; Expr::Array },
        Tok::Id(mut x) => { if matches!(self.peek(), Tok::Dot) { self.eat(); x.push('.'); x.push_str(&self.id()?); } if matches!(self.peek(), Tok::LParen) { self.eat(); let mut a = Vec::new(); if !matches!(self.peek(), Tok::RParen) { loop { a.push(self.expr()?); if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; } } } self.expect(|x| matches!(x, Tok::RParen), "expected )")?; Expr::Call(x, a) } else { Expr::Var(x) } }
        Tok::LParen => { let x = self.expr()?; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; x }, x => return Err(format!("expected expression, got {x:?}"))
    }; while matches!(self.peek(), Tok::LBracket) { self.eat(); let index = self.expr()?; self.expect(|x| matches!(x, Tok::RBracket), "expected ]")?; x = Expr::Index(Box::new(x), Box::new(index)); } Ok(x) }
    fn block(&mut self) -> Result<Vec<Stmt>, String> { self.expect(|x| matches!(x, Tok::LBrace), "expected {")?; let mut b = Vec::new(); while !matches!(self.peek(), Tok::RBrace | Tok::Eof) { b.push(self.stmt()?); } self.expect(|x| matches!(x, Tok::RBrace), "expected }")?; Ok(b) }
    fn stmt(&mut self) -> Result<Stmt, String> { match self.peek() {
        Tok::Id(k) if k == "let" || k == "const" => { self.eat(); let n = self.id()?; self.annotation()?; self.expect(|x| matches!(x, Tok::Eq), "expected =")?; let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Let(n, e)) }
        Tok::Id(k) if k == "return" => { self.eat(); let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Return(e)) }
        Tok::Id(k) if k == "if" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let c = self.expr()?; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; let yes = self.block()?; let no = if matches!(self.peek(), Tok::Id(x) if x == "else") { self.eat(); if matches!(self.peek(), Tok::Id(x) if x == "if") { vec![self.stmt()?] } else { self.block()? } } else { Vec::new() }; Ok(Stmt::If(c, yes, no)) }
        Tok::Id(k) if k == "while" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let c = self.expr()?; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; Ok(Stmt::While(c, self.block()?)) }
        Tok::Id(k) if k == "for" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let init = if matches!(self.peek(), Tok::Id(k) if k == "let" || k == "const") { self.stmt()? } else { let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Stmt::Expr(e) }; let cond = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; let update = { let n = self.id()?; self.expect(|x| matches!(x, Tok::Eq), "expected =")?; let e = self.expr()?; Stmt::Assign(n, e) }; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; Ok(Stmt::For(Box::new(init), cond, Box::new(update), self.block()?)) }
        Tok::Id(n) => { let n = n.clone(); if self.t.get(self.p + 1).is_some_and(|x| matches!(x, Tok::Eq)) { self.eat(); self.eat(); let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Assign(n, e)) } else { let left = self.expr()?; if matches!(self.peek(), Tok::Eq) { self.eat(); let value = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; match left { Expr::Index(a, i) => Ok(Stmt::IndexAssign(*a, *i, value)), Expr::Var(name) => Ok(Stmt::Assign(name, value)), _ => Err("invalid assignment target".into()) } } else { self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Expr(left)) } } }
        _ => { let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Expr(e)) }
    } }
    fn fun(&mut self) -> Result<Fun, String> { if self.id()? != "function" { return Err("expected function".into()); } let name = self.id()?; self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let mut params = Vec::new(); let mut param_types = Vec::new(); if !matches!(self.peek(), Tok::RParen) { loop { let p = self.id()?; let ty = self.annotation()?.unwrap_or(ir::IrType::Any); params.push(p); param_types.push(ty); if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; } } } self.expect(|x| matches!(x, Tok::RParen), "expected )")?; let return_type = self.annotation()?.unwrap_or(ir::IrType::Any); Ok(Fun { name, params, param_types, return_type, body: self.block()? }) }
    fn program(&mut self) -> Result<Vec<Fun>, String> { let mut f = Vec::new(); while !matches!(self.peek(), Tok::Eof) { f.push(self.fun()?); } Ok(f) }
}

struct Compiler { m: ObjectModule, funcs: HashMap<String, FuncId>, returns: HashMap<String, ir::IrType>, active_kinds: HashMap<String, ir::IrType>, print_i64: FuncId, print_bool: FuncId, print_str: FuncId, array_new: FuncId, array_get: FuncId, array_set: FuncId, concat_str: FuncId, strings: HashMap<String, DataId> }
impl Compiler {
    fn new() -> Result<Self, String> { let isa = cranelift_codegen::isa::lookup(target_lexicon::HOST).map_err(|e| e.to_string())?.finish(settings::Flags::new(settings::builder())).map_err(|e| e.to_string())?; let b = ObjectBuilder::new(isa, "nexa", cranelift_module::default_libcall_names()).map_err(|e| e.to_string())?; let m = ObjectModule::new(b); let mut c = Self { m, funcs: HashMap::new(), returns: HashMap::new(), active_kinds: HashMap::new(), print_i64: FuncId::from_u32(0), print_bool: FuncId::from_u32(0), print_str: FuncId::from_u32(0), array_new: FuncId::from_u32(0), array_get: FuncId::from_u32(0), array_set: FuncId::from_u32(0), concat_str: FuncId::from_u32(0), strings: HashMap::new() }; c.print_i64 = c.import("nexa_print_i64", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.print_bool = c.import("nexa_print_bool", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.print_str = c.import("nexa_print_str", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_new = c.import("nexa_array_new", vec![AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_get = c.import("nexa_array_get", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.array_set = c.import("nexa_array_set", vec![AbiParam::new(types::I64), AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; c.concat_str = c.import("nexa_concat_str", vec![AbiParam::new(types::I64), AbiParam::new(types::I64)], vec![AbiParam::new(types::I64)])?; Ok(c) }
    fn import(&mut self, n: &str, params: Vec<AbiParam>, returns: Vec<AbiParam>) -> Result<FuncId, String> { let mut s = Signature::new(self.m.isa().default_call_conv()); s.params = params; s.returns = returns; self.m.declare_function(n, Linkage::Import, &s).map_err(|e| e.to_string()) }
    fn compile(&mut self, fs: &[Fun]) -> Result<(), String> { for f in fs { let mut s = Signature::new(self.m.isa().default_call_conv()); s.params = (0..f.params.len()).map(|_| AbiParam::new(types::I64)).collect(); s.returns.push(AbiParam::new(types::I64)); let id = self.m.declare_function(&f.name, Linkage::Export, &s).map_err(|e| e.to_string())?; self.funcs.insert(f.name.clone(), id); self.returns.insert(f.name.clone(), f.return_type); } for f in fs { self.one(f)?; } Ok(()) }
    fn one(&mut self, f: &Fun) -> Result<(), String> { let id = self.funcs[&f.name]; let mut fun = Function::new(); let mut sig = Signature::new(self.m.isa().default_call_conv()); sig.params = (0..f.params.len()).map(|_| AbiParam::new(types::I64)).collect(); sig.returns.push(AbiParam::new(types::I64)); fun.signature = sig; let mut cx = FunctionBuilderContext::new(); let mut b = FunctionBuilder::new(&mut fun, &mut cx); let entry = b.create_block(); b.append_block_params_for_function_params(entry); b.switch_to_block(entry); self.active_kinds.clear(); let mut vars = HashMap::new(); for (i, n) in f.params.iter().enumerate() { let v = b.declare_var(types::I64); b.def_var(v, b.block_params(entry)[i]); vars.insert(n.clone(), v); self.active_kinds.insert(n.clone(), f.param_types.get(i).copied().unwrap_or(ir::IrType::Any)); } let terminated = self.stmts(&mut b, &f.body, &mut vars)?; if !terminated { let z = b.ins().iconst(types::I64, 0); b.ins().return_(&[z]); } b.seal_all_blocks(); b.finalize(); let mut ctx = cranelift_codegen::Context::for_function(fun); self.m.define_function(id, &mut ctx).map_err(|e| format!("{e:?}"))?; Ok(()) }
    fn stmts(&mut self, b: &mut FunctionBuilder, ss: &[Stmt], vars: &mut HashMap<String, Variable>) -> Result<bool, String> { for s in ss { if self.stmt(b, s, vars)? { return Ok(true); } } Ok(false) }
    fn stmt(&mut self, b: &mut FunctionBuilder, s: &Stmt, vars: &mut HashMap<String, Variable>) -> Result<bool, String> { match s {
        Stmt::Let(n, e) => { let v = b.declare_var(types::I64); let x = self.emit(b, e, vars)?; b.def_var(v, x); vars.insert(n.clone(), v); self.active_kinds.insert(n.clone(), self.expr_kind(e)); Ok(false) }
        Stmt::Assign(n, e) => { let v = *vars.get(n).ok_or_else(|| format!("unknown variable {n}"))?; let x = self.emit(b, e, vars)?; b.def_var(v, x); Ok(false) }
        Stmt::IndexAssign(a, i, e) => { let array = self.emit(b, a, vars)?; let index = self.emit(b, i, vars)?; let value = self.emit(b, e, vars)?; let callee = self.m.declare_func_in_func(self.array_set, b.func); b.ins().call(callee, &[array, index, value]); Ok(false) }
        Stmt::Return(e) => { let x = self.emit(b, e, vars)?; b.ins().return_(&[x]); Ok(true) }
        Stmt::Expr(e) => { self.emit(b, e, vars)?; Ok(false) }
        Stmt::If(c, yes, no) => { let t = b.create_block(); let f = b.create_block(); let join = b.create_block(); let x = self.emit(b, c, vars)?; b.ins().brif(x, t, &[], f, &[]); b.switch_to_block(t); let yt = self.stmts(b, yes, vars)?; if !yt { b.ins().jump(join, &[]); } b.switch_to_block(f); let ft = self.stmts(b, no, vars)?; if !ft { b.ins().jump(join, &[]); } b.switch_to_block(join); b.seal_block(t); b.seal_block(f); b.seal_block(join); Ok(yt && ft) }
        Stmt::While(c, body) => { let head = b.create_block(); let loop_b = b.create_block(); let exit = b.create_block(); b.ins().jump(head, &[]); b.switch_to_block(head); let x = self.emit(b, c, vars)?; b.ins().brif(x, loop_b, &[], exit, &[]); b.switch_to_block(loop_b); let bt = self.stmts(b, body, vars)?; if !bt { b.ins().jump(head, &[]); } b.switch_to_block(exit); b.seal_block(head); b.seal_block(loop_b); b.seal_block(exit); Ok(false) }
        Stmt::For(init, c, update, body) => { self.stmt(b, init, vars)?; let head = b.create_block(); let loop_b = b.create_block(); let exit = b.create_block(); b.ins().jump(head, &[]); b.switch_to_block(head); let x = self.emit(b, c, vars)?; b.ins().brif(x, loop_b, &[], exit, &[]); b.switch_to_block(loop_b); let bt = self.stmts(b, body, vars)?; if !bt { self.stmt(b, update, vars)?; b.ins().jump(head, &[]); } b.switch_to_block(exit); b.seal_block(head); b.seal_block(loop_b); b.seal_block(exit); Ok(false) }
    } }
    fn expr_kind(&self, e: &Expr) -> ir::IrType { match e { Expr::Num(_) => ir::IrType::Number, Expr::Bool(_) => ir::IrType::Boolean, Expr::Str(_) => ir::IrType::String, Expr::Array => ir::IrType::Any, Expr::Index(_, _) => ir::IrType::Number, Expr::Var(n) => self.active_kinds.get(n).copied().unwrap_or(ir::IrType::Any), Expr::Unary(op, _) => if *op == '!' { ir::IrType::Boolean } else { ir::IrType::Number }, Expr::Bin(a, op, c) => if op == "+" && self.expr_kind(a) == ir::IrType::String && self.expr_kind(c) == ir::IrType::String { ir::IrType::String } else if matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||") { ir::IrType::Boolean } else { ir::IrType::Number }, Expr::Call(n, _) => if n == "console.log" { ir::IrType::Void } else { self.returns.get(n).copied().unwrap_or(ir::IrType::Any) } } }
    fn emit(&mut self, b: &mut FunctionBuilder, e: &Expr, vars: &HashMap<String, Variable>) -> Result<Value, String> { match e {
        Expr::Num(x) => Ok(b.ins().iconst(types::I64, *x)), Expr::Bool(x) => Ok(b.ins().iconst(types::I64, i64::from(*x))), Expr::Array => { let callee = self.m.declare_func_in_func(self.array_new, b.func); let n = b.ins().iconst(types::I64, 1_000_000); let call = b.ins().call(callee, &[n]); Ok(b.func.dfg.inst_results(call)[0]) }, Expr::Index(a, i) => { let array = self.emit(b, a, vars)?; let index = self.emit(b, i, vars)?; let callee = self.m.declare_func_in_func(self.array_get, b.func); let call = b.ins().call(callee, &[array, index]); Ok(b.func.dfg.inst_results(call)[0]) }, Expr::Var(n) => Ok(b.use_var(*vars.get(n).ok_or_else(|| format!("unknown variable {n}"))?)),
        Expr::Unary(op, x) => { let v = self.emit(b, x, vars)?; Ok(if *op == '-' { b.ins().ineg(v) } else { b.ins().icmp_imm(IntCC::Equal, v, 0) }) }
        Expr::Bin(a, op, c) => { let string_add = op == "+" && self.expr_kind(a) == ir::IrType::String && self.expr_kind(c) == ir::IrType::String; let x = self.emit(b, a, vars)?; let y = self.emit(b, c, vars)?; if string_add { let callee = self.m.declare_func_in_func(self.concat_str, b.func); let call = b.ins().call(callee, &[x, y]); return Ok(b.func.dfg.inst_results(call)[0]); } let v = match op.as_str() { "+" => b.ins().iadd(x, y), "-" => b.ins().isub(x, y), "*" => b.ins().imul(x, y), "/" => b.ins().sdiv(x, y), "%" => b.ins().srem(x, y), "==" => b.ins().icmp(IntCC::Equal, x, y), "!=" => b.ins().icmp(IntCC::NotEqual, x, y), "<" => b.ins().icmp(IntCC::SignedLessThan, x, y), "<=" => b.ins().icmp(IntCC::SignedLessThanOrEqual, x, y), ">" => b.ins().icmp(IntCC::SignedGreaterThan, x, y), ">=" => b.ins().icmp(IntCC::SignedGreaterThanOrEqual, x, y), "&&" => b.ins().band(x, y), "||" => b.ins().bor(x, y), _ => return Err(format!("unknown operator {op}")) }; let v = if matches!(op.as_str(), "==" | "!=" | "<" | "<=" | ">" | ">=") { b.ins().uextend(types::I64, v) } else { v }; Ok(v) }
        Expr::Call(n, a) => { if n == "console.log" { if a.len() != 1 { return Err("console.log accepts one expression".into()); } if let Expr::Str(s) = &a[0] { let id = if let Some(id) = self.strings.get(s) { *id } else { let id = self.m.declare_data(&format!("str{}", self.strings.len()), Linkage::Local, false, false).map_err(|e| e.to_string())?; let mut d = DataDescription::new(); d.define(s.as_bytes().to_vec().into_boxed_slice()); self.m.define_data(id, &d).map_err(|e| e.to_string())?; self.strings.insert(s.clone(), id); id }; let gv = self.m.declare_data_in_func(id, b.func); let p = b.ins().symbol_value(types::I64, gv); let l = b.ins().iconst(types::I64, s.len() as i64); let callee = self.m.declare_func_in_func(self.print_str, b.func); let call = b.ins().call(callee, &[p, l]); return Ok(b.func.dfg.inst_results(call)[0]); } let x = self.emit(b, &a[0], vars)?; let fid = if self.expr_kind(&a[0]) == ir::IrType::Boolean { self.print_bool } else { self.print_i64 }; let callee = self.m.declare_func_in_func(fid, b.func); let call = b.ins().call(callee, &[x]); Ok(b.func.dfg.inst_results(call)[0]) } else { let id = *self.funcs.get(n).ok_or_else(|| format!("unknown function {n}"))?; let mut xs = Vec::new(); for a in a { xs.push(self.emit(b, a, vars)?); } let callee = self.m.declare_func_in_func(id, b.func); let call = b.ins().call(callee, &xs); Ok(b.func.dfg.inst_results(call)[0]) } }
        Expr::Str(s) => { let id = if let Some(id) = self.strings.get(s) { *id } else { let id = self.m.declare_data(&format!("str{}", self.strings.len()), Linkage::Local, false, false).map_err(|e| e.to_string())?; let mut bytes = s.as_bytes().to_vec(); bytes.push(0); let mut d = DataDescription::new(); d.define(bytes.into_boxed_slice()); self.m.define_data(id, &d).map_err(|e| e.to_string())?; self.strings.insert(s.clone(), id); id }; let gv = self.m.declare_data_in_func(id, b.func); let p = b.ins().symbol_value(types::I64, gv); let tag = b.ins().iconst(types::I64, i64::MIN); Ok(b.ins().bor(p, tag)) }
    } }
}

fn main() { if let Err(e) = run() { eprintln!("nexa: {e}"); std::process::exit(1); } }
fn strip_top_level_entry_call(source: &str) -> String { source.lines().filter(|line| line.trim() != "main();").collect::<Vec<_>>().join("\n") }
fn run() -> Result<(), String> { let a: Vec<String> = env::args().collect(); if a.len() < 2 { return Err("usage: nexa <source.ts> [-o executable]".into()); } let src = fs::read_to_string(&a[1]).map_err(|e| e.to_string())?; parse_typescript(&src, &a[1])?; let lowered_src = strip_top_level_entry_call(&src); let mut p = Parser { t: lex(&lowered_src)?, p: 0 }; let fs = p.program()?; let ir = ir::lower_program(&fs); if env::var_os("NEXA_DUMP_IR").is_some() { eprintln!("{ir}"); } let mut c = Compiler::new()?; c.compile(&fs)?; let obj = c.m.finish(); let objpath = "/tmp/nexa.o"; fs::write(objpath, obj.emit().map_err(|e| e.to_string())?).map_err(|e| e.to_string())?; let out = a.iter().position(|x| x == "-o").and_then(|i| a.get(i + 1)).cloned().unwrap_or_else(|| "a.out".into()); if !Path::new("runtime.c").exists() { return Err("runtime.c is missing".into()); } let status = Command::new("gcc").args([objpath, "runtime.c", "-o", &out]).status().map_err(|e| e.to_string())?; if !status.success() { return Err("link failed".into()); } println!("built {out}"); Ok(()) }
