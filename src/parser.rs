use std::collections::HashSet;

use crate::ir;
use crate::{Expr, Fun, Stmt, leak_str};

#[derive(Clone, Debug)]
pub enum Tok { Id(String), Num(i64), FNum(f64), Str(Vec<u8>), True, False, Plus, Minus, Star, Slash, Percent, Eq, EqEq, NotEq, Lt, Le, Gt, Ge, Bang, And, Or, Colon, Dot, Arrow, LParen, RParen, LBrace, RBrace, LBracket, RBracket, Comma, Semi, Eof }

pub fn lex(s: &str) -> Result<Vec<Tok>, String> {
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
            b'0'..=b'9' => {
                let j = i;
                while i < b.len() && b[i].is_ascii_digit() { i += 1; }
                let mut is_float = false;
                if i < b.len() && b[i] == b'.' {
                    is_float = true;
                    i += 1;
                    while i < b.len() && b[i].is_ascii_digit() { i += 1; }
                }
                if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
                    let k = i + 1;
                    let mut digits_start = k;
                    if k < b.len() && (b[k] == b'+' || b[k] == b'-') { digits_start = k + 1; }
                    if digits_start < b.len() && b[digits_start].is_ascii_digit() {
                        is_float = true;
                        i = digits_start;
                        while i < b.len() && b[i].is_ascii_digit() { i += 1; }
                    }
                }
                if is_float {
                    out.push(Tok::FNum(s[j..i].parse().map_err(|_| format!("invalid float literal `{}`", &s[j..i]))?));
                } else {
                    out.push(Tok::Num(s[j..i].parse().unwrap()));
                }
            }
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => { let j = i; while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') { i += 1; } out.push(match &s[j..i] { "true" => Tok::True, "false" => Tok::False, x => Tok::Id(x.into()) }); }
            b'"' => { i += 1; let mut raw: Vec<u8> = Vec::new(); loop { if i >= b.len() { return Err("unterminated string".into()); } if b[i] == b'"' { i += 1; break; } if b[i] == b'\\' { i += 1; if i >= b.len() { return Err("unterminated escape sequence".into()); } match b[i] { b'n' => { raw.push(b'\n'); i += 1; } b'r' => { raw.push(b'\r'); i += 1; } b't' => { raw.push(b'\t'); i += 1; } b'\\' => { raw.push(b'\\'); i += 1; } b'"' => { raw.push(b'"'); i += 1; } b'x' => { i += 1; if i + 2 > b.len() { return Err("bad \\x escape".into()); } let hex = |c: u8| -> Option<u8> { match c { b'0'..=b'9' => Some(c - b'0'), b'a'..=b'f' => Some(c - b'a' + 10), b'A'..=b'F' => Some(c - b'A' + 10), _ => None } }; if let (Some(hi), Some(lo)) = (hex(b[i]), hex(b[i + 1])) { raw.push(hi * 16 + lo); i += 2; } else { return Err("bad hex digit in \\x escape".into()); } } other => return Err(format!("unsupported escape sequence \\{}", other as char)), } } else { raw.push(b[i]); i += 1; } } out.push(Tok::Str(raw)); }
            b'+' => { out.push(Tok::Plus); i += 1; } b'-' => { out.push(Tok::Minus); i += 1; } b'*' => { out.push(Tok::Star); i += 1; } b'/' => { out.push(Tok::Slash); i += 1; } b'%' => { out.push(Tok::Percent); i += 1; }
            b'=' => { out.push(Tok::Eq); i += 1; } b'!' => { out.push(Tok::Bang); i += 1; } b'<' => { out.push(Tok::Lt); i += 1; } b'>' => { out.push(Tok::Gt); i += 1; }
            b':' => { out.push(Tok::Colon); i += 1; } b'.' => { out.push(Tok::Dot); i += 1; } b'(' => { out.push(Tok::LParen); i += 1; } b')' => { out.push(Tok::RParen); i += 1; }
            b'{' => { out.push(Tok::LBrace); i += 1; } b'}' => { out.push(Tok::RBrace); i += 1; } b'[' => { out.push(Tok::LBracket); i += 1; } b']' => { out.push(Tok::RBracket); i += 1; } b',' => { out.push(Tok::Comma); i += 1; } b';' => { out.push(Tok::Semi); i += 1; }
            _ => return Err(format!("unexpected character: {}", b[i] as char)),
        }
    }
    out.push(Tok::Eof); Ok(out)
}

pub fn resolve_ty_name(name: &str) -> Result<ir::IrType, String> { match name { "number" => Ok(ir::IrType::Number), "string" => Ok(ir::IrType::String), "boolean" => Ok(ir::IrType::Boolean), "Pointer" => Ok(ir::IrType::Pointer), other => Err(format!("unsupported generic type argument: {other}")) } }

pub struct Parser { pub t: Vec<Tok>, pub p: usize, pub unsafe_depth: usize, pub extern_names: HashSet<String>, pub scope_type_param: Option<String>, pub obj_lit_index: usize }
impl Parser {
    pub fn peek(&self) -> &Tok { &self.t[self.p] }
    pub fn eat(&mut self) -> Tok { let x = self.t[self.p].clone(); self.p += 1; x }
    pub fn id(&mut self) -> Result<String, String> { match self.eat() { Tok::Id(x) => Ok(x), x => Err(format!("expected identifier, got {x:?}")) } }
    pub fn expect(&mut self, f: fn(&Tok) -> bool, msg: &str) -> Result<(), String> { if f(self.peek()) { self.eat(); Ok(()) } else { Err(msg.into()) } }
    pub fn annotation(&mut self, type_param: Option<&str>) -> Result<Option<ir::IrType>, String> { if matches!(self.peek(), Tok::Colon) { self.eat(); if matches!(self.peek(), Tok::LParen) { self.eat(); if matches!(self.peek(), Tok::RParen) { self.eat(); self.expect(|x| matches!(x, Tok::Arrow), "expected => in closure type")?; let ret = self.id()?; if ret != "number" { return Err("Nexa v1 closures must return number".into()); } return Ok(Some(ir::IrType::ClosureNumber)); } else if matches!(self.peek(), Tok::LParen) { self.eat(); self.expect(|x| matches!(x, Tok::RParen), "Nexa v1 closure types take no arguments")?; self.expect(|x| matches!(x, Tok::Arrow), "expected => in closure type")?; let ret = self.id()?; if ret != "number" { return Err("Nexa v1 closures must return number".into()); } self.expect(|x| matches!(x, Tok::RParen), "expected ) in closure type")?; return Ok(Some(ir::IrType::ClosureNumber)); } else { return Err("Nexa v1 closure types take no arguments".into()); } } let ty = self.id()?; if Some(ty.as_str()) == type_param { return Ok(Some(ir::IrType::TParam)); } let array = if matches!(self.peek(), Tok::LBracket) { self.eat(); self.expect(|x| matches!(x, Tok::RBracket), "expected ] in type annotation")?; true } else { false }; return Ok(Some(if array { match ty.as_str() { "number" => ir::IrType::NumberArray, "f32" => ir::IrType::Float32Array, "f64" => ir::IrType::Float64Array, _ => return Err(format!("invalid array element type `{ty}`; supported: number, f32, f64")) } } else { match ty.as_str() { "number" => ir::IrType::Number, "f32" => ir::IrType::F32, "f64" => ir::IrType::F64, "string" => ir::IrType::String, "boolean" => ir::IrType::Boolean, "void" => ir::IrType::Void, "any" => ir::IrType::Any, "Pointer" => ir::IrType::Pointer, _ => ir::IrType::Class(leak_str(&ty)) } })); } Ok(None) }
    pub fn expr(&mut self) -> Result<Expr, String> { self.or() }
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
    pub fn member_chain(&mut self) -> Result<Expr, String> {
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
            Tok::FNum(x) => Expr::FNum(x),
            Tok::True => Expr::Bool(true),
            Tok::False => Expr::Bool(false),
            Tok::Str(x) => Expr::Str(x),
            Tok::LBracket => {
                if matches!(self.peek(), Tok::RBracket) {
                    self.eat();
                    return Err("unsized array literal `[]` is not supported in this version; use `new Array<number>(n)` to allocate an explicit size".into());
                }
                let mut elems = Vec::new();
                loop {
                    elems.push(self.expr()?);
                    if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; }
                }
                self.expect(|x| matches!(x, Tok::RBracket), "expected ] to close array literal")?;
                Expr::Array(elems)
            }
            Tok::LBrace => {
                // Object literal `{ x: 1, y: 2 }`. Only legal where a named
                // interface type is expected (verified by the checker); each
                // literal site receives its own automatically-synthesized
                // struct layout (`__objlit_n`).
                let mut fields = Vec::new();
                while !matches!(self.peek(), Tok::RBrace | Tok::Eof) {
                    let field_name = self.id()?;
                    self.expect(|x| matches!(x, Tok::Colon), "expected : after object literal field name")?;
                    let value = self.expr()?;
                    fields.push((field_name, value));
                    if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; }
                }
                self.expect(|x| matches!(x, Tok::RBrace), "expected } to close object literal")?;
                let synth = format!("__objlit_{}", self.obj_lit_index);
                self.obj_lit_index += 1;
                Expr::ObjectLiteral(synth, fields)
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
                    } else if obj_name == "std" && (field == "log" || field == "in" || field == "parseNumber" || field == "toCString" || field == "fromCString" || field == "funcPtr" || field == "strlen" || field == "charAt" || field == "toF64" || field == "toF32" || field == "toInt") {
                        x = Expr::Call(format!("std.{field}"), args);
                    } else {
                        x = Expr::MethodCall(Box::new(x), field, args);
                    }
                } else if let Expr::FieldAccess(base, sub) = &x {
                    let is_std_net = matches!(&**base, Expr::Var(oname) if oname == "std")
                        && sub == "net"
                        && matches!(field.as_str(), "sockaddrIn" | "socket" | "bind" | "listen" | "accept" | "recv" | "send" | "close");
                    let is_std_process = matches!(&**base, Expr::Var(oname) if oname == "std")
                        && sub == "process"
                        && matches!(field.as_str(), "fork" | "exec1" | "exec2" | "pipe" | "pipeReadFd" | "pipeWriteFd" | "wait" | "exit");
                    if is_std_net {
                        x = Expr::Call(format!("std.net.{field}"), args);
                    } else if is_std_process {
                        x = Expr::Call(format!("std.process.{field}"), args);
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
    pub fn atom(&mut self) -> Result<Expr, String> {
        match self.peek() {
            Tok::Id(name) if name == "new" => {
                self.eat();
                let class_name = self.id()?;
                if matches!(self.peek(), Tok::Lt)
                    && matches!(self.t.get(self.p + 1), Some(Tok::Id(_)))
                    && matches!(self.t.get(self.p + 2), Some(Tok::Gt)) {
                    self.eat();
                    self.eat();
                    self.eat();
                }
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
    pub fn block(&mut self) -> Result<Vec<Stmt>, String> { self.expect(|x| matches!(x, Tok::LBrace), "expected {")?; let mut b = Vec::new(); while !matches!(self.peek(), Tok::RBrace | Tok::Eof) { b.push(self.stmt()?); } self.expect(|x| matches!(x, Tok::RBrace), "expected }")?; Ok(b) }
    pub fn stmt(&mut self) -> Result<Stmt, String> { match self.peek() {
        Tok::Id(k) if k == "let" || k == "const" => { self.eat(); let n = self.id()?; let tp = self.scope_type_param.clone(); let annotation = self.annotation(tp.as_deref())?; self.expect(|x| matches!(x, Tok::Eq), "expected =")?; let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Let(n, annotation, e)) }
        Tok::Id(k) if k == "return" => { self.eat(); let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Ok(Stmt::Return(e)) }
        Tok::Id(k) if k == "if" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let c = self.expr()?; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; let yes = self.block()?; let no = if matches!(self.peek(), Tok::Id(x) if x == "else") { self.eat(); if matches!(self.peek(), Tok::Id(x) if x == "if") { vec![self.stmt()?] } else { self.block()? } } else { Vec::new() }; Ok(Stmt::If(c, yes, no)) }
        Tok::Id(k) if k == "while" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let c = self.expr()?; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; Ok(Stmt::While(c, self.block()?)) }
        Tok::Id(k) if k == "for" => { self.eat(); self.expect(|x| matches!(x, Tok::LParen), "expected (")?; if matches!(self.peek(), Tok::Id(x) if x == "let" || x == "const") { let is_const = matches!(self.peek(), Tok::Id(x) if x == "const"); self.eat(); let bname = self.id()?; let tp = self.scope_type_param.clone(); let annotation = self.annotation(tp.as_deref())?; if matches!(self.peek(), Tok::Id(x) if x == "of") { if !is_const { return Err("Nexa v1 for...of supports only `const` loop binders".into()); } self.eat(); let iter = self.expr()?; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; return Ok(Stmt::ForOf(iter, bname, self.block()?)); } self.expect(|x| matches!(x, Tok::Eq), "expected =")?; let init_e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; let cond = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; let update = { let n = self.id()?; self.expect(|x| matches!(x, Tok::Eq), "expected =")?; let e = self.expr()?; Stmt::Assign(n, e) }; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; Ok(Stmt::For(Box::new(Stmt::Let(bname, annotation, init_e)), cond, Box::new(update), self.block()?)) } else { let init = { let e = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; Stmt::Expr(e) }; let cond = self.expr()?; self.expect(|x| matches!(x, Tok::Semi), "expected ;")?; let update = { let n = self.id()?; self.expect(|x| matches!(x, Tok::Eq), "expected =")?; let e = self.expr()?; Stmt::Assign(n, e) }; self.expect(|x| matches!(x, Tok::RParen), "expected )")?; Ok(Stmt::For(Box::new(init), cond, Box::new(update), self.block()?)) } }
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
    pub fn fun(&mut self) -> Result<Fun, String> { if self.id()? != "function" { return Err("expected function".into()); } let name = self.id()?; let type_param = if matches!(self.peek(), Tok::Lt) { self.eat(); let tp = self.id()?; self.expect(|x| matches!(x, Tok::Gt), "expected > after type parameter")?; Some(tp) } else { None }; self.expect(|x| matches!(x, Tok::LParen), "expected (")?; let mut params = Vec::new(); let mut param_types = Vec::new(); if !matches!(self.peek(), Tok::RParen) { loop { let p = self.id()?; let ty = self.annotation(type_param.as_deref())?.unwrap_or(ir::IrType::Any); params.push(p); param_types.push(ty); if matches!(self.peek(), Tok::Comma) { self.eat(); } else { break; } } } self.expect(|x| matches!(x, Tok::RParen), "expected )")?; let return_type = self.annotation(type_param.as_deref())?.unwrap_or(ir::IrType::Any); let saved = self.scope_type_param.clone(); self.scope_type_param = type_param.clone(); let body = self.block()?; self.scope_type_param = saved; Ok(Fun { name, params, param_types, return_type, body, type_param }) }
    fn program(&mut self) -> Result<Vec<Fun>, String> { let mut f = Vec::new(); while !matches!(self.peek(), Tok::Eof) { f.push(self.fun()?); } Ok(f) }
}
