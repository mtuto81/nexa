use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use swc_common::{sync::Lrc, BytePos, FileName, SourceMap};
use swc_ecma_ast::{Decl, EsVersion, ImportSpecifier, Module as SwcModule, ModuleDecl, ModuleExportName, ModuleItem, Stmt as SStmt};
use swc_ecma_parser::{lexer::Lexer, Parser as SwcParser, StringInput, Syntax, TsSyntax};

use crate::{blank_unsafe_markers, extract_extern_blocks};

// Result of module resolution: the flattened single-file program plus the
// static namespace-import bindings it needs at parse/check time.
//
// `namespaces` maps each `import * as ns` alias to the exported member names
// of the module it points at. Both the swc checker and the Nexa parser consult
// it so `ns.member(...)` can be resolved to the flat top-level name `member`.
pub(crate) struct FlattenResult {
    pub(crate) code: String,
    pub(crate) namespaces: HashMap<String, HashSet<String>>,
}

struct LoadedModule {
    display: String,
    canon: PathBuf,
    stripped: String,
    exports: HashSet<String>,
    imports: Vec<(String, PathBuf)>,
    // `import * as ns` bindings: (alias, resolved target path). The target may
    // be a real file or a bundled std/<name> module.
    namespace_imports: Vec<(String, PathBuf)>,
}

// Bundled stdlib modules, embedded into the compiler binary. The `std/` import
// prefix is reserved for these; they are not searched as files on disk. Each
// one is a normal Nexa module that happens to be compiled into the binary.
const BUNDLED_STD: &[(&str, &str)] = &[
    ("net", include_str!("../std/net.ts")),
    ("process", include_str!("../std/process.ts")),
    ("time", include_str!("../std/time.ts")),
    ("fs", include_str!("../std/fs.ts")),
    ("mem", include_str!("../std/mem.ts")),
];
const BUNDLED_STD_PREFIX: &str = "/nexa_std/";

fn bundled_keys() -> Vec<&'static str> {
    BUNDLED_STD.iter().map(|(name, _)| *name).collect()
}

fn bundled_source(name: &str) -> Result<&'static str, String> {
    BUNDLED_STD
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, src)| *src)
        .ok_or_else(|| format!("unknown bundled std module `std/{name}`; available: {}", bundled_keys().join(", ")))
}

fn bundled_path(name: &str) -> PathBuf {
    PathBuf::from(format!("{BUNDLED_STD_PREFIX}{name}.ts"))
}

fn is_bundled_path(p: &Path) -> bool {
    p.starts_with(BUNDLED_STD_PREFIX)
}

pub(crate) fn resolve_and_flatten(entry: &Path) -> Result<FlattenResult, String> {
    let mut done: HashMap<PathBuf, usize> = HashMap::new();
    let mut order: Vec<LoadedModule> = Vec::new();
    let mut stack: Vec<(PathBuf, String)> = Vec::new();
    let mut owners: HashMap<String, String> = HashMap::new();
    visit(entry, &mut stack, &mut done, &mut order, &mut owners)?;
    let mut namespaces: HashMap<String, HashSet<String>> = HashMap::new();
    for m in &order {
        for (ns, target) in &m.namespace_imports {
            if ns == "std" || ns == "console" {
                return Err(format!("`{}`: the namespace alias `{ns}` is reserved for built-in std/console intrinsics", m.display));
            }
            if owners.contains_key(ns) {
                return Err(format!("`{}`: namespace alias `{ns}` conflicts with a top-level declaration (in `{}`)", m.display, owners[ns]));
            }
            let tcanon = fs_canonicalize(target)?;
            let idx = *done.get(&tcanon).ok_or_else(|| format!("internal error: namespace import `{ns}` target `{}` was not resolved", target.display()))?;
            let members: HashSet<String> = order[idx].exports.iter().cloned().collect();
            if let Some(prev) = namespaces.get(ns) {
                if *prev != members {
                    return Err(format!("`{}`: namespace alias `{ns}` is bound to more than one different module", m.display));
                }
            } else {
                namespaces.insert(ns.clone(), members);
            }
        }
    }
    let code = order.iter().map(|m| m.stripped.as_str()).collect::<Vec<_>>().join("\n");
    Ok(FlattenResult { code, namespaces })
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
    for (_, target) in loaded.namespace_imports.clone() {
        visit(&target, stack, done, order, owners)?;
    }
    stack.pop();
    for (name, target) in &loaded.imports {
        let tcanon = fs_canonicalize(target)?;
        let idx = *done.get(&tcanon).ok_or_else(|| format!("internal error: module `{}` was not resolved before import validation", target.display()))?;
        if !order[idx].exports.contains(name) {
            return Err(format!("`{}` imports `{name}` from `{}`, which does not export it; only exported functions, classes, and module-scope globals can be imported", loaded.display, order[idx].display));
        }
    }
    done.insert(canon, order.len());
    order.push(loaded);
    Ok(())
}

fn fs_canonicalize(path: &Path) -> Result<PathBuf, String> {
    if is_bundled_path(path) {
        let name = path.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
        bundled_source(&name)?; // validate that the bundled module actually exists
        return Ok(path.to_path_buf());
    }
    std::fs::canonicalize(path).map_err(|_| format!("cannot read module `{}`: no such file", path.display()))
}

fn load_module(path: &Path, display: &str, canon: &Path, owners: &mut HashMap<String, String>) -> Result<LoadedModule, String> {
    let src = if is_bundled_path(path) {
        let name = path.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
        bundled_source(&name)?.to_string()
    } else {
        std::fs::read_to_string(path).map_err(|e| format!("cannot read module `{display}`: {e}"))?
    };
    let (_externs, clean) = extract_extern_blocks(&src)?;
    let blanked = blank_unsafe_markers(&clean)?;
    let (module, base) = parse_swc_with_base(&blanked, display)?;
    let mut cuts: Vec<(usize, usize)> = Vec::new();
    let mut exports: HashSet<String> = HashSet::new();
    let mut clause_exports: Vec<String> = Vec::new();
    let mut locals: HashSet<String> = HashSet::new();
    let mut imports: Vec<(String, PathBuf)> = Vec::new();
    let mut namespace_imports: Vec<(String, PathBuf)> = Vec::new();
    let mut raw_imports: Vec<(String, String)> = Vec::new();
    let mut raw_namespace_imports: Vec<(String, String)> = Vec::new();
    let parent = if is_bundled_path(path) { Path::new(BUNDLED_STD_PREFIX) } else { path.parent().unwrap_or_else(|| Path::new(".")) };
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
                            ImportSpecifier::Default(_) => return Err(format!("`{display}`: default imports are not supported in this version; use named imports `{{ X }} from \"./file.ts\"` or `import * as ns from \"./file.ts\"`")),
                            ImportSpecifier::Namespace(n) => {
                                // `import * as ns from "..."`: a static
                                // namespace alias over the target module's
                                // exports. Every target (including std/<name>
                                // bundles) is pulled into the flat program as a
                                // dependency and the alias is recorded for the
                                // parser/checker.
                                raw_namespace_imports.push((n.local.sym.to_string(), i.src.value.as_str().unwrap_or_default().to_string()));
                            }
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
                    Decl::Var(v) => {
                        if v.decls.len() != 1 { return Err(format!("`{display}`: only single-declarator top-level `let`/`const` declarations are supported")) }
                        let swc_ecma_ast::Pat::Ident(p) = &v.decls[0].name else { return Err(format!("`{display}`: top-level global declarations require an identifier")) };
                        exports.insert(p.id.sym.to_string());
                        locals.insert(p.id.sym.to_string());
                        cuts.push(export_prefix_cut(&src, off(base, e.span.lo), off(base, v.span.lo), display)?);
                    }
                    _ => return Err(format!("`{display}`: only top-level function, class, and module-scope variable declarations may be exported")),
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
            ModuleItem::Stmt(SStmt::Decl(Decl::Var(v))) => {
                if v.decls.len() != 1 { return Err(format!("`{display}`: only single-declarator top-level `let`/`const` declarations are supported")) }
                let swc_ecma_ast::Pat::Ident(p) = &v.decls[0].name else { return Err(format!("`{display}`: top-level global declarations require an identifier")) };
                locals.insert(p.id.sym.to_string());
            }
            _ => {}
        }
    }
    for name in &clause_exports {
        if !locals.contains(name) {
            return Err(format!("`{display}`: `export {{ {name} }}` refers to a name that is not a top-level function, class, or module-scope global declared in this file"));
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
        imports.push((name, resolve_target(display, &spec, parent)?));
    }
    for (name, spec) in raw_namespace_imports {
        namespace_imports.push((name, resolve_target(display, &spec, parent)?));
    }
    cuts.sort_by(|a, b| b.0.cmp(&a.0));
    let mut out = src;
    for (start, end) in cuts { out.replace_range(start..end, ""); }
    Ok(LoadedModule { display: display.to_string(), canon: canon.to_path_buf(), stripped: out, exports, imports, namespace_imports })
}

fn resolve_target(display: &str, spec: &str, parent: &Path) -> Result<PathBuf, String> {
    if let Some(rest) = spec.strip_prefix("std/") {
        validate_specifier(display, spec)?;
        return Ok(bundled_path(rest));
    }
    validate_specifier(display, spec)?;
    Ok(parent.join(spec.strip_prefix("./").unwrap_or(spec)))
}

fn validate_specifier(display: &str, spec: &str) -> Result<(), String> {
    if let Some(rest) = spec.strip_prefix("std/") {
        if rest.is_empty() || rest.contains('/') || rest.starts_with('.') {
            return Err(format!("`{display}`: invalid std path \"{spec}\"; expected `std/<name>` with no slashes or dots"));
        }
        bundled_source(rest)?;
        return Ok(());
    }
    if !(spec.starts_with("./") || spec.starts_with("../")) {
        return Err(format!("`{display}`: import \"{spec}\" is not a relative path or a bundled std module; only `./`, `../`, and `std/` imports are supported (package/bare-specifier resolution is out of scope for this version)"));
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
