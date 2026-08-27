use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use swc_common::{sync::Lrc, BytePos, FileName, SourceMap};
use swc_ecma_ast::{Decl, EsVersion, ImportSpecifier, Module as SwcModule, ModuleDecl, ModuleExportName, ModuleItem, Stmt as SStmt};
use swc_ecma_parser::{lexer::Lexer, Parser as SwcParser, StringInput, Syntax, TsSyntax};

use crate::{blank_unsafe_markers, extract_extern_blocks};

struct LoadedModule {
    display: String,
    canon: PathBuf,
    stripped: String,
    exports: HashSet<String>,
    imports: Vec<(String, PathBuf)>,
}

pub(crate) fn resolve_and_flatten(entry: &Path) -> Result<String, String> {
    let mut done: HashMap<PathBuf, usize> = HashMap::new();
    let mut order: Vec<LoadedModule> = Vec::new();
    let mut stack: Vec<(PathBuf, String)> = Vec::new();
    let mut owners: HashMap<String, String> = HashMap::new();
    visit(entry, &mut stack, &mut done, &mut order, &mut owners)?;
    Ok(order.iter().map(|m| m.stripped.as_str()).collect::<Vec<_>>().join("\n"))
}

fn visit(path: &Path, stack: &mut Vec<(PathBuf, String)>, done: &mut HashMap<PathBuf, usize>, order: &mut Vec<LoadedModule>, owners: &mut HashMap<String, String>) -> Result<(), String> {
    let display = path.display().to_string();
    let canon = fs_canonicalize(path)?;
    if let Some(pos) = stack.iter().position(|(c, _)| *c == canon) {
        let mut chain: Vec<String> = stack[pos..].iter().map(|(_, d)| d.clone()).collect();
        chain.push(display);
        return Err(format!("circular import detected: {}", chain.join(" -> ")));
    }
    if done.contains_key(&canon) { return Ok(()); }
    let loaded = load_module(path, &display, &canon, owners)?;
    stack.push((canon.clone(), display));
    for (_, target) in loaded.imports.clone() {
        visit(&target, stack, done, order, owners)?;
    }
    stack.pop();
    for (name, target) in &loaded.imports {
        let tcanon = fs_canonicalize(target)?;
        let idx = *done.get(&tcanon).ok_or_else(|| format!("internal error: module `{}` was not resolved before import validation", target.display()))?;
        if !order[idx].exports.contains(name) {
            return Err(format!("`{}` imports `{name}` from `{}`, which does not export it; only exported functions and classes can be imported", loaded.display, order[idx].display));
        }
    }
    done.insert(canon, order.len());
    order.push(loaded);
    Ok(())
}

fn fs_canonicalize(path: &Path) -> Result<PathBuf, String> { std::fs::canonicalize(path).map_err(|_| format!("cannot read module `{}`: no such file", path.display())) }

fn load_module(path: &Path, display: &str, canon: &Path, owners: &mut HashMap<String, String>) -> Result<LoadedModule, String> {
    let src = std::fs::read_to_string(path).map_err(|e| format!("cannot read module `{display}`: {e}"))?;
    let (_externs, clean) = extract_extern_blocks(&src)?;
    let blanked = blank_unsafe_markers(&clean)?;
    let (module, base) = parse_swc_with_base(&blanked, display)?;
    let mut cuts: Vec<(usize, usize)> = Vec::new();
    let mut exports: HashSet<String> = HashSet::new();
    let mut clause_exports: Vec<String> = Vec::new();
    let mut locals: HashSet<String> = HashSet::new();
    let mut imports: Vec<(String, PathBuf)> = Vec::new();
    let mut raw_imports: Vec<(String, String)> = Vec::new();
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    for item in &module.body {
        match item {
            ModuleItem::ModuleDecl(d) => match d {
                ModuleDecl::Import(i) => {
                    if i.type_only { return Err(format!("`{display}`: `import type` is not supported")); }
                    for sp in &i.specifiers {
                        match sp {
                            ImportSpecifier::Named(n) => {
                                if n.is_type_only { return Err(format!("`{display}`: inline type-only import of `{}` is not supported", n.local.sym)); }
                                if n.imported.is_some() { return Err(format!("`{display}`: import renaming (`{{ x as y }}`) is not supported; import `{}` under its own name", n.local.sym)); }
                                raw_imports.push((n.local.sym.to_string(), i.src.value.as_str().unwrap_or_default().to_string()));
                            }
                            ImportSpecifier::Default(_) => return Err(format!("`{display}`: default imports are not supported in this version; use named imports `{{ X }} from \"./file.ts\"`")),
                            ImportSpecifier::Namespace(_) => return Err(format!("`{display}`: `import * as ns` is not supported in this version; use named imports")),
                        }
                    }
                    cuts.push(stmt_cut(&src, off(base, i.span.lo), off(base, i.span.hi), "import", display)?);
                }
                ModuleDecl::ExportDecl(e) => match &e.decl {
                    Decl::Fn(f) => {
                        exports.insert(f.ident.sym.to_string());
                        locals.insert(f.ident.sym.to_string());
                        cuts.push(export_prefix_cut(&src, off(base, e.span.lo), off(base, f.function.span.lo), display)?);
                    }
                    Decl::Class(c) => {
                        exports.insert(c.ident.sym.to_string());
                        locals.insert(c.ident.sym.to_string());
                        cuts.push(export_prefix_cut(&src, off(base, e.span.lo), off(base, c.class.span.lo), display)?);
                    }
                    Decl::Var(_) => return Err(format!("`{display}`: exporting top-level `let`/`const` is out of scope for this version; only functions and classes may be exported")),
                    _ => return Err(format!("`{display}`: only top-level function and class declarations may be exported")),
                },
                ModuleDecl::ExportNamed(e) => {
                    if e.src.is_some() { return Err(format!("`{display}`: re-exporting from another module (`export {{ x }} from ...`) is not supported in this version")); }
                    if e.type_only { return Err(format!("`{display}`: `export type` is not supported")); }
                    for sp in &e.specifiers {
                        match sp {
                            swc_ecma_ast::ExportSpecifier::Named(n) => {
                                if n.is_type_only { return Err(format!("`{display}`: inline type-only export is not supported")); }
                                if n.exported.is_some() { return Err(format!("`{display}`: export renaming (`{{ x as y }}`) is not supported in this version")); }
                                let name = match &n.orig {
                                    ModuleExportName::Ident(id) => id.sym.to_string(),
                                    ModuleExportName::Str(_) => return Err(format!("`{display}`: string export names are not supported")),
                                };
                                clause_exports.push(name.clone());
                                exports.insert(name);
                            }
                            _ => return Err(format!("`{display}`: only named exports are supported; `export default` and `export *` are out of scope for this version")),
                        }
                    }
                    cuts.push(stmt_cut(&src, off(base, e.span.lo), off(base, e.span.hi), "export", display)?);
                }
                ModuleDecl::ExportAll(_) => return Err(format!("`{display}`: `export * from` is not supported in this version; use named exports")),
                ModuleDecl::ExportDefaultExpr(_) | ModuleDecl::ExportDefaultDecl(_) => return Err(format!("`{display}`: `export default` is not supported in this version; use named exports")),
                _ => return Err(format!("`{display}`: unsupported module-level declaration")),
            },
            ModuleItem::Stmt(SStmt::Decl(Decl::Fn(f))) => { locals.insert(f.ident.sym.to_string()); }
            ModuleItem::Stmt(SStmt::Decl(Decl::Class(c))) => { locals.insert(c.ident.sym.to_string()); }
            _ => {}
        }
    }
    for name in &clause_exports {
        if !locals.contains(name) {
            return Err(format!("`{display}`: `export {{ {name} }}` refers to a name that is not a top-level function or class declared in this file"));
        }
    }
    for name in &locals {
        if let Some(prev) = owners.get(name) {
            if prev != canon { return Err(format!("duplicate top-level declaration `{name}` defined in both `{prev}` and `{display}`")); }
        } else {
            owners.insert(name.clone(), canon.display().to_string());
        }
    }
    for (name, spec) in raw_imports {
        validate_specifier(display, &spec)?;
        imports.push((name, parent.join(spec.strip_prefix("./").unwrap_or(&spec))));
    }
    cuts.sort_by(|a, b| b.0.cmp(&a.0));
    let mut out = src;
    for (start, end) in cuts { out.replace_range(start..end, ""); }
    Ok(LoadedModule { display: display.to_string(), canon: canon.to_path_buf(), stripped: out, exports, imports })
}

fn validate_specifier(display: &str, spec: &str) -> Result<(), String> {
    if !(spec.starts_with("./") || spec.starts_with("../")) {
        return Err(format!("`{display}`: import \"{spec}\" is not a relative path; only `./` and `../` imports are supported (package/bare-specifier resolution is out of scope for this version)"));
    }
    if !spec.ends_with(".ts") {
        return Err(format!("`{display}`: import \"{spec}\" must end with an explicit `.ts` extension"));
    }
    Ok(())
}

fn off(base: u32, pos: BytePos) -> usize { (pos.0 - base) as usize }

fn stmt_cut(src: &str, start: usize, end: usize, keyword: &str, display: &str) -> Result<(usize, usize), String> {
    let end = end.min(src.len());
    let slice = &src[start..end];
    if !slice.trim_start().starts_with(keyword) {
        return Err(format!("internal error while processing `{display}`: expected {keyword} statement at byte offset {start}, found {:?}; this indicates a span-mapping bug in the module resolver", slice.trim()));
    }
    let b = src.as_bytes();
    let mut e = end;
    while e < b.len() && (b[e] == b' ' || b[e] == b'\t' || b[e] == b'\r' || b[e] == b';') { e += 1; }
    if e < b.len() && b[e] == b'\n' { e += 1; }
    Ok((start, e))
}

fn export_prefix_cut(src: &str, start: usize, decl_start: usize, display: &str) -> Result<(usize, usize), String> {
    let end = decl_start.min(src.len());
    let start = start.min(end);
    if src[start..end].trim() != "export" {
        return Err(format!("internal error while processing `{display}`: expected an `export` keyword at byte offset {start}, found {:?}; this indicates a span-mapping bug in the module resolver", src[start..end].trim()));
    }
    Ok((start, end))
}

fn parse_swc_with_base(source: &str, filename: &str) -> Result<(SwcModule, u32), String> {
    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(FileName::Custom(filename.into()).into(), source.to_string());
    let base = fm.start_pos.0;
    let lexer = Lexer::new(
        Syntax::Typescript(TsSyntax { tsx: false, decorators: true, ..Default::default() }),
        EsVersion::latest(),
        StringInput::from(&*fm),
        None,
    );
    let mut parser = SwcParser::new_from(lexer);
    let module = parser.parse_module().map_err(|e| format!("TypeScript parse error in `{filename}`: {e:?}"))?;
    if let Some(error) = parser.take_errors().into_iter().next() { return Err(format!("TypeScript parse error in `{filename}`: {error:?}")); }
    Ok((module, base))
}
