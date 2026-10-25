use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{Expr, UseTree};
use quote::ToTokens;

#[derive(Debug, serde::Deserialize)]
struct Lock {
    schema_version: u32,
    files: Vec<LockedFile>,
}

#[derive(Debug, serde::Deserialize)]
struct LockedFile {
    path: String,
    component: String,
    sha256: Option<String>,
}

#[derive(Clone, Copy, Serialize)]
struct SourceSpan {
    line: usize,
    column: usize,
    end_line: usize,
    end_column: usize,
}

fn source_span(span: Span) -> SourceSpan {
    let start = span.start();
    let end = span.end();
    SourceSpan {
        line: start.line,
        column: start.column,
        end_line: end.line,
        end_column: end.column,
    }
}

fn sha256(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn hash_file(root: &Path, relative: &str) -> Result<String, String> {
    let path = root.join(relative);
    let bytes = fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))?;
    Ok(sha256(&bytes))
}

fn tokens(tokens: impl ToTokens) -> String {
    tokens.to_token_stream().to_string()
}

#[derive(Serialize)]
struct Inventory {
    schema_version: u32,
    analyzer: AnalyzerInfo,
    source_lock: SourceLockInfo,
    limitations: Vec<&'static str>,
    source_files: Vec<SourceFileRecord>,
    symbols: Vec<SymbolRecord>,
    enum_variants: Vec<EnumVariantRecord>,
    match_arms: Vec<MatchArmRecord>,
    imports: Vec<ImportRecord>,
    call_sites: Vec<CallSiteRecord>,
    macro_sites: Vec<MacroSiteRecord>,
    candidate_graph: Vec<CandidateGroup>,
    import_candidate_graph: Vec<CandidateGroup>,
    mir_variant_dispatch_candidates: Vec<VariantDispatchCandidate>,
    machine_hook_candidates: Vec<MachineHookCandidate>,
    summary: Summary,
}

#[derive(Serialize)]
struct AnalyzerInfo {
    crate_name: &'static str,
    syn_version: &'static str,
    schema: &'static str,
    manifest_sha256: String,
    cargo_lock_sha256: String,
    source_sha256: String,
}

#[derive(Serialize)]
struct SourceLockInfo {
    path: &'static str,
    file_count: usize,
    rust_file_count: usize,
    sha256: String,
}

#[derive(Serialize)]
struct SourceFileRecord {
    path: String,
    component: String,
    source_sha256: String,
    parsed: bool,
    parse_error: Option<String>,
    syntax_adapters: Vec<&'static str>,
}

#[derive(Clone, Serialize)]
struct SymbolRecord {
    id: String,
    path: String,
    component: String,
    kind: String,
    name: String,
    symbol: String,
    span: SourceSpan,
    visibility: Option<String>,
    signature: Option<String>,
    has_body: Option<bool>,
    body_span: Option<SourceSpan>,
    body_token_sha256: Option<String>,
    owner: Option<String>,
    enum_category: Option<String>,
    machine_context: bool,
    machine_hook_candidate: bool,
}

#[derive(Serialize)]
struct EnumVariantRecord {
    id: String,
    path: String,
    component: String,
    enum_symbol: String,
    enum_name: String,
    name: String,
    symbol: String,
    span: SourceSpan,
    shape: String,
    fields: Vec<String>,
    enum_category: String,
}

#[derive(Serialize)]
struct ImportRecord {
    id: String,
    path: String,
    component: String,
    imported_path: String,
    terminal_name: Option<String>,
    is_glob: bool,
    alias: Option<String>,
    visibility: String,
    span: SourceSpan,
}

#[derive(Serialize)]
struct CallSiteRecord {
    id: String,
    path: String,
    component: String,
    enclosing_symbol: Option<String>,
    kind: String,
    callee: String,
    callee_path: Option<String>,
    receiver: Option<String>,
    terminal_name: Option<String>,
    span: SourceSpan,
}

#[derive(Serialize)]
struct MacroSiteRecord {
    id: String,
    path: String,
    component: String,
    enclosing_symbol: Option<String>,
    macro_path: String,
    macro_name: String,
    site_kind: String,
    classification: String,
    span: SourceSpan,
}

#[derive(Serialize)]
struct MatchArmRecord {
    id: String,
    path: String,
    component: String,
    enclosing_symbol: Option<String>,
    match_id: String,
    scrutinee: String,
    pattern: String,
    variant_paths: Vec<String>,
    has_guard: bool,
    span: SourceSpan,
}

#[derive(Serialize)]
struct VariantDispatchCandidate {
    variant_id: String,
    match_arm_ids: Vec<String>,
    explicit_qualified_candidates: Vec<String>,
    unqualified_candidates: Vec<String>,
    classification: &'static str,
}

#[derive(Serialize)]
struct MachineHookCandidate {
    trait_method_id: String,
    method_name: String,
    trait_method_path: String,
    has_default_body: bool,
    implementation_candidate_ids: Vec<String>,
    classification: &'static str,
}

#[derive(Serialize)]
struct CandidateGroup {
    terminal_name: String,
    call_site_ids: Vec<String>,
    candidate_definition_ids: Vec<String>,
    candidate_count: usize,
    resolution: String,
    basis: &'static str,
}

#[derive(Serialize)]
struct Summary {
    locked_rust_files: usize,
    parsed_rust_files: usize,
    parse_failures: usize,
    syntax_adapted_files: usize,
    symbols: usize,
    functions: usize,
    functions_with_bodies: usize,
    enums: usize,
    enum_variants: usize,
    mir_enum_variants: usize,
    machine_trait_or_impl_methods: usize,
    machine_hook_name_candidates: usize,
    imports: usize,
    function_and_method_call_sites: usize,
    match_arms: usize,
    macro_call_sites: usize,
    macro_definition_sites: usize,
    diagnostic_macro_call_sites: usize,
    mir_variant_dispatch_candidates: usize,
    machine_trait_hook_candidates: usize,
    unresolved_call_name_groups: usize,
    ambiguous_call_name_groups: usize,
    unresolved_import_name_groups: usize,
}

struct SourceContext {
    path: String,
    component: String,
    inserted_columns: BTreeMap<usize, Vec<usize>>,
}

#[derive(Default)]
struct Collector {
    context: Option<SourceContext>,
    scopes: Vec<String>,
    function_stack: Vec<String>,
    symbols: Vec<SymbolRecord>,
    variants: Vec<EnumVariantRecord>,
    match_arms: Vec<MatchArmRecord>,
    imports: Vec<ImportRecord>,
    calls: Vec<CallSiteRecord>,
    macros: Vec<MacroSiteRecord>,
    serial: usize,
}

impl Collector {
    fn span(&self, span: Span) -> SourceSpan {
        let mut result = source_span(span);
        if let Some(context) = &self.context {
            for (line, column) in [
                (&mut result.line, &mut result.column),
                (&mut result.end_line, &mut result.end_column),
            ] {
                if let Some(insertions) = context.inserted_columns.get(line) {
                    for threshold in insertions {
                        if *column >= *threshold {
                            *column = column.saturating_sub(2);
                        }
                    }
                }
            }
        }
        result
    }

    fn context(&self) -> (&str, &str) {
        let ctx = self.context.as_ref().expect("collector context is set");
        (&ctx.path, &ctx.component)
    }

    fn current_owner(&self) -> Option<String> {
        if self.scopes.is_empty() {
            None
        } else {
            Some(self.scopes.join("::"))
        }
    }

    fn in_machine_context(&self) -> bool {
        self.scopes.iter().any(|scope| {
            scope == "trait Machine"
                || scope.starts_with("impl ")
                    && scope
                        .strip_prefix("impl ")
                        .and_then(|rest| rest.split_once(" for ").map(|(trait_path, _)| trait_path))
                        .is_some_and(is_machine_trait_path)
        })
    }

    fn next_id(&mut self, kind: &str, symbol: &str, span: Span) -> String {
        self.serial += 1;
        let (path, _) = self.context();
        let loc = self.span(span);
        format!("{}#{}:{}@{}:{}#{}", path, kind, symbol, loc.line, loc.column, self.serial)
    }

    fn full_symbol(&self, name: &str) -> String {
        match self.current_owner() {
            Some(owner) => format!("{owner}::{name}"),
            None => name.to_owned(),
        }
    }

    fn record_symbol(
        &mut self,
        kind: &str,
        name: &str,
        span: Span,
        visibility: Option<String>,
        signature: Option<String>,
        has_body: Option<bool>,
        body_span: Option<Span>,
        body_tokens: Option<String>,
        enum_category: Option<String>,
    ) -> String {
        let (path, component) = self.context();
        let path = path.to_owned();
        let component = component.to_owned();
        let symbol = self.full_symbol(name);
        let id = self.next_id(kind, &symbol, span);
        let machine_context = self.in_machine_context();
        let machine_hook_candidate = is_hook_name(name);
        self.symbols.push(SymbolRecord {
            id: id.clone(),
            path,
            component,
            kind: kind.to_owned(),
            name: name.to_owned(),
            symbol,
            span: self.span(span),
            visibility,
            signature,
            has_body,
            body_span: body_span.map(source_span),
            body_token_sha256: body_tokens.as_ref().map(|body| sha256(body.as_bytes())),
            owner: self.current_owner(),
            enum_category,
            machine_context,
            machine_hook_candidate,
        });
        id
    }

    fn record_function(
        &mut self,
        kind: &str,
        name: &str,
        span: Span,
        visibility: Option<String>,
        signature: String,
        body: Option<&syn::Block>,
    ) -> String {
        self.record_symbol(
            kind,
            name,
            span,
            visibility,
            Some(signature),
            Some(body.is_some()),
            body.map(Spanned::span),
            body.map(tokens),
            None,
        )
    }

    fn record_call(&mut self, kind: &str, callee: String, callee_path: Option<String>,
                   receiver: Option<String>, terminal: Option<String>, span: Span) {
        let (path, component) = self.context();
        let path = path.to_owned();
        let component = component.to_owned();
        let id = self.next_id(kind, &callee, span);
        self.calls.push(CallSiteRecord {
            id,
            path,
            component,
            enclosing_symbol: self.function_stack.last().cloned(),
            kind: kind.to_owned(),
            callee,
            callee_path,
            receiver,
            terminal_name: terminal,
            span: self.span(span),
        });
    }

    fn add_import_leaf(&mut self, raw: String, terminal: Option<String>, glob: bool,
                       alias: Option<String>, visibility: String, span: Span) {
        let (path, component) = self.context();
        let path = path.to_owned();
        let component = component.to_owned();
        let id = self.next_id("import", &raw, span);
        self.imports.push(ImportRecord {
            id,
            path,
            component,
            imported_path: raw,
            terminal_name: terminal,
            is_glob: glob,
            alias,
            visibility,
            span: self.span(span),
        });
    }
}

fn is_hook_name(name: &str) -> bool {
    ["before_", "after_", "atomic_", "call_", "eval_", "enforce_", "validate_", "retag", "find_mir"]
        .iter()
        .any(|prefix| name.starts_with(prefix))
}

fn is_machine_trait_path(trait_path: &str) -> bool {
    trait_path.split('<').next().unwrap_or(trait_path)
        .trim()
        .rsplit("::")
        .next()
        .is_some_and(|terminal| terminal.trim() == "Machine")
}

fn enum_category(name: &str) -> String {
    match name {
        "StatementKind" => "mir_statement".to_owned(),
        "TerminatorKind" => "mir_terminator".to_owned(),
        "Rvalue" => "mir_rvalue".to_owned(),
        "BinOp" | "UnOp" | "NullOp" => "mir_operator".to_owned(),
        "CastKind" => "mir_cast".to_owned(),
        "Intrinsic" | "NonDivergingIntrinsic" => "mir_intrinsic".to_owned(),
        _ => "other_enum".to_owned(),
    }
}

fn use_tree_leaves(tree: &UseTree, prefix: &str, output: &mut Vec<(String, Option<String>, bool, Option<String>)>) {
    match tree {
        UseTree::Path(path) => {
            let next = if prefix.is_empty() { path.ident.to_string() } else { format!("{prefix}::{}", path.ident) };
            use_tree_leaves(&path.tree, &next, output);
        }
        UseTree::Name(name) => {
            let full = if prefix.is_empty() { name.ident.to_string() } else { format!("{prefix}::{}", name.ident) };
            output.push((full, Some(name.ident.to_string()), false, None));
        }
        UseTree::Rename(rename) => {
            let full = if prefix.is_empty() { rename.ident.to_string() } else { format!("{prefix}::{}", rename.ident) };
            output.push((full, Some(rename.rename.to_string()), false, Some(rename.rename.to_string())));
        }
        UseTree::Glob(_) => output.push((format!("{prefix}::*"), None, true, None)),
        UseTree::Group(group) => {
            for item in &group.items {
                use_tree_leaves(item, prefix, output);
            }
        }
    }
}

fn expr_path_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(path) => path.path.segments.last().map(|segment| segment.ident.to_string()),
        Expr::Paren(paren) => expr_path_name(&paren.expr),
        Expr::Group(group) => expr_path_name(&group.expr),
        _ => None,
    }
}

fn expr_full_path(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(path) => Some(tokens(&path.path)),
        Expr::Paren(paren) => expr_full_path(&paren.expr),
        Expr::Group(group) => expr_full_path(&group.expr),
        _ => None,
    }
}

#[derive(Default)]
struct PatternPathCollector {
    paths: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for PatternPathCollector {
    fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
        self.paths.insert(tokens(&node.path));
        visit::visit_expr_path(self, node);
    }

    fn visit_pat_tuple_struct(&mut self, node: &'ast syn::PatTupleStruct) {
        self.paths.insert(tokens(&node.path));
        visit::visit_pat_tuple_struct(self, node);
    }

    fn visit_pat_struct(&mut self, node: &'ast syn::PatStruct) {
        self.paths.insert(tokens(&node.path));
        visit::visit_pat_struct(self, node);
    }
}

fn classify_macro(name: &str) -> String {
    let lower = name.to_ascii_lowercase();
    if lower.starts_with("throw_ub") || lower.starts_with("err_ub") || lower == "ub" {
        "ub".to_owned()
    } else if lower.starts_with("throw_unsup") || lower.starts_with("err_unsup") || lower.contains("unsupported") {
        "unsupported".to_owned()
    } else if lower.starts_with("throw_inval") || lower.starts_with("err_inval") || lower.contains("invalid_program") {
        "invalid_program".to_owned()
    } else if matches!(lower.as_str(), "bug" | "span_bug" | "unreachable" | "unreachable_unchecked" | "assert" | "debug_assert") {
        "panic_or_invariant".to_owned()
    } else {
        "other_macro".to_owned()
    }
}

impl<'ast> Visit<'ast> for Collector {
    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        self.record_symbol("module", &node.ident.to_string(), node.span(), Some(tokens(&node.vis)), None,
                           None, None, None, None);
        if node.content.is_some() {
            self.scopes.push(format!("mod {}", node.ident));
            visit::visit_item_mod(self, node);
            self.scopes.pop();
        }
    }

    fn visit_item_trait(&mut self, node: &'ast syn::ItemTrait) {
        let name = node.ident.to_string();
        self.record_symbol("trait", &name, node.span(), Some(tokens(&node.vis)), Some(tokens(&node.supertraits)),
                           None, None, None, None);
        self.scopes.push(format!("trait {name}"));
        visit::visit_item_trait(self, node);
        self.scopes.pop();
    }

    fn visit_item_impl(&mut self, node: &'ast syn::ItemImpl) {
        let self_ty = tokens(&node.self_ty);
        let trait_path = node.trait_.as_ref().map(|(_, path, _)| tokens(path));
        let scope = match &trait_path {
            Some(path) => format!("impl {path} for {self_ty}"),
            None => format!("impl {self_ty}"),
        };
        self.record_symbol("impl", &scope, node.span(), None, trait_path.clone(), None, None, None, None);
        self.scopes.push(scope);
        visit::visit_item_impl(self, node);
        self.scopes.pop();
    }

    fn visit_item_enum(&mut self, node: &'ast syn::ItemEnum) {
        let name = node.ident.to_string();
        let category = enum_category(&name);
        let enum_symbol = self.full_symbol(&name);
        self.record_symbol("enum", &name, node.span(), Some(tokens(&node.vis)), Some(format!("variants={}", node.variants.len())),
                           None, None, None, Some(category.clone()));
        for variant in &node.variants {
            let variant_name = variant.ident.to_string();
            let shape = match &variant.fields {
                syn::Fields::Unit => "unit",
                syn::Fields::Unnamed(_) => "tuple",
                syn::Fields::Named(_) => "struct",
            }.to_owned();
            let fields = variant.fields.iter().map(|field| {
                let name = field.ident.as_ref().map(ToString::to_string).unwrap_or_default();
                format!("{}: {}", name, tokens(&field.ty))
            }).collect();
            let (path, component) = self.context();
            let path = path.to_owned();
            let component = component.to_owned();
            let symbol = format!("{}::{variant_name}", enum_symbol);
            let id = self.next_id("enum_variant", &symbol, variant.span());
            self.variants.push(EnumVariantRecord {
                id,
                path,
                component,
                enum_symbol: enum_symbol.clone(),
                enum_name: name.clone(),
                name: variant_name,
                symbol,
                span: self.span(variant.span()),
                shape,
                fields,
                enum_category: category.clone(),
            });
        }
        visit::visit_item_enum(self, node);
    }

    fn visit_item_struct(&mut self, node: &'ast syn::ItemStruct) {
        self.record_symbol("struct", &node.ident.to_string(), node.span(), Some(tokens(&node.vis)),
                           Some(tokens(&node.fields)), None, None, None, None);
        visit::visit_item_struct(self, node);
    }

    fn visit_item_union(&mut self, node: &'ast syn::ItemUnion) {
        self.record_symbol("union", &node.ident.to_string(), node.span(), Some(tokens(&node.vis)),
                           Some(tokens(&node.fields)), None, None, None, None);
        visit::visit_item_union(self, node);
    }

    fn visit_item_type(&mut self, node: &'ast syn::ItemType) {
        self.record_symbol("type_alias", &node.ident.to_string(), node.span(), Some(tokens(&node.vis)),
                           Some(tokens(&node.ty)), None, None, None, None);
        visit::visit_item_type(self, node);
    }

    fn visit_item_const(&mut self, node: &'ast syn::ItemConst) {
        self.record_symbol("const", &node.ident.to_string(), node.span(), Some(tokens(&node.vis)),
                           Some(tokens(&node.ty)), Some(true), Some(node.expr.span()), Some(tokens(&node.expr)), None);
        visit::visit_item_const(self, node);
    }

    fn visit_item_static(&mut self, node: &'ast syn::ItemStatic) {
        self.record_symbol("static", &node.ident.to_string(), node.span(), Some(tokens(&node.vis)),
                           Some(tokens(&node.ty)), Some(true), Some(node.expr.span()), Some(tokens(&node.expr)), None);
        visit::visit_item_static(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        let name = node.sig.ident.to_string();
        let id = self.record_function("function", &name, node.span(), Some(tokens(&node.vis)),
                                      tokens(&node.sig), Some(&node.block));
        self.function_stack.push(id);
        visit::visit_item_fn(self, node);
        self.function_stack.pop();
    }

    fn visit_trait_item_fn(&mut self, node: &'ast syn::TraitItemFn) {
        let name = node.sig.ident.to_string();
        let body = node.default.as_ref();
        let id = self.record_function("trait_method", &name, node.span(), Some("trait_member".to_owned()),
                                      tokens(&node.sig), body);
        self.function_stack.push(id);
        visit::visit_trait_item_fn(self, node);
        self.function_stack.pop();
    }

    fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
        let name = node.sig.ident.to_string();
        let id = self.record_function("method", &name, node.span(), Some(tokens(&node.vis)),
                                      tokens(&node.sig), Some(&node.block));
        self.function_stack.push(id);
        visit::visit_impl_item_fn(self, node);
        self.function_stack.pop();
    }

    fn visit_item_use(&mut self, node: &'ast syn::ItemUse) {
        let mut leaves = Vec::new();
        use_tree_leaves(&node.tree, "", &mut leaves);
        for (path, terminal, glob, alias) in leaves {
            self.add_import_leaf(path, terminal, glob, alias, tokens(&node.vis), node.span());
        }
        visit::visit_item_use(self, node);
    }

    fn visit_item_extern_crate(&mut self, node: &'ast syn::ItemExternCrate) {
        let raw = node.ident.to_string();
        let alias = node.rename.as_ref().map(|(_, alias)| alias.to_string());
        self.add_import_leaf(raw.clone(), Some(alias.clone().unwrap_or_else(|| raw.clone())), false,
                             alias, tokens(&node.vis), node.span());
        visit::visit_item_extern_crate(self, node);
    }

    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        let callee = tokens(&node.func);
        let callee_path = expr_full_path(&node.func);
        self.record_call("function_call", callee, callee_path, None,
                         expr_path_name(&node.func), node.span());
        visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        let callee = node.method.to_string();
        self.record_call("method_call", callee.clone(), None, Some(tokens(&node.receiver)),
                         Some(callee), node.span());
        visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_match(&mut self, node: &'ast syn::ExprMatch) {
        let scrutinee = tokens(&node.expr);
        let match_id = self.next_id("match", &scrutinee, node.span());
        for arm in &node.arms {
            let pattern = tokens(&arm.pat);
            let mut collector = PatternPathCollector::default();
            collector.visit_pat(&arm.pat);
            let variant_paths = collector.paths.into_iter().collect();
            let (path, component) = self.context();
            let path = path.to_owned();
            let component = component.to_owned();
            let id = self.next_id("match_arm", &pattern, arm.span());
            self.match_arms.push(MatchArmRecord {
                id,
                path,
                component,
                enclosing_symbol: self.function_stack.last().cloned(),
                match_id: match_id.clone(),
                scrutinee: scrutinee.clone(),
                pattern,
                variant_paths,
                has_guard: arm.guard.is_some(),
                span: self.span(arm.span()),
            });
        }
        visit::visit_expr_match(self, node);
    }

    fn visit_macro(&mut self, node: &'ast syn::Macro) {
        let (path, component) = self.context();
        let path = path.to_owned();
        let component = component.to_owned();
        let macro_path = tokens(&node.path);
        let macro_name = node.path.segments.last().map(|part| part.ident.to_string()).unwrap_or_default();
        let id = self.next_id("macro", &macro_path, node.span());
        self.macros.push(MacroSiteRecord {
            id,
            path,
            component,
            enclosing_symbol: self.function_stack.last().cloned(),
            macro_path,
            classification: classify_macro(&macro_name),
            macro_name,
            site_kind: "invocation".to_owned(),
            span: self.span(node.span()),
        });
        visit::visit_macro(self, node);
    }

    fn visit_item_macro(&mut self, node: &'ast syn::ItemMacro) {
        if let Some(ident) = &node.ident {
            let (path, component) = self.context();
            let path = path.to_owned();
            let component = component.to_owned();
            let macro_path = tokens(&node.mac.path);
            let macro_name = ident.to_string();
            let id = self.next_id("macro_definition", &macro_name, node.span());
            self.macros.push(MacroSiteRecord {
                id,
                path,
                component,
                enclosing_symbol: self.function_stack.last().cloned(),
                macro_path,
                macro_name,
                site_kind: "definition".to_owned(),
                classification: "macro_definition".to_owned(),
                span: self.span(node.span()),
            });
            for attribute in &node.attrs {
                self.visit_attribute(attribute);
            }
        } else {
            for attribute in &node.attrs {
                self.visit_attribute(attribute);
            }
            self.visit_macro(&node.mac);
        }
    }
}

fn candidate_groups(calls: &[CallSiteRecord], symbols: &[SymbolRecord]) -> Vec<CandidateGroup> {
    let mut definitions: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for symbol in symbols.iter().filter(|symbol| matches!(symbol.kind.as_str(), "function" | "method" | "trait_method")) {
        definitions.entry(symbol.name.clone()).or_default().push(symbol.id.clone());
    }
    let mut call_sites: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for call in calls {
        if let Some(name) = &call.terminal_name {
            call_sites.entry(name.clone()).or_default().push(call.id.clone());
        }
    }
    let names: BTreeSet<String> = call_sites.keys().cloned().collect();
    names.into_iter().map(|name| {
        let ids = definitions.get(&name).cloned().unwrap_or_default();
        let resolution = match ids.len() {
            0 => "unresolved_in_selected_rust_sources",
            1 => "single_name_candidate_only_not_resolved",
            _ => "ambiguous_name_candidates_only_not_resolved",
        }.to_owned();
        CandidateGroup {
            terminal_name: name.clone(),
            call_site_ids: call_sites.remove(&name).unwrap_or_default(),
            candidate_count: ids.len(),
            candidate_definition_ids: ids,
            resolution,
            basis: "simple terminal identifier equality; not Rust name resolution",
        }
    }).collect()
}

fn import_candidate_groups(imports: &[ImportRecord], symbols: &[SymbolRecord]) -> Vec<CandidateGroup> {
    let mut definitions: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for symbol in symbols {
        definitions.entry(symbol.name.clone()).or_default().push(symbol.id.clone());
    }
    let mut import_sites: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for import in imports {
        if let Some(name) = &import.terminal_name {
            import_sites.entry(name.clone()).or_default().push(import.id.clone());
        }
    }
    import_sites.into_iter().map(|(name, call_site_ids)| {
        let ids = definitions.get(&name).cloned().unwrap_or_default();
        let resolution = match ids.len() {
            0 => "unresolved_in_selected_rust_sources",
            1 => "single_name_candidate_only_not_resolved",
            _ => "ambiguous_name_candidates_only_not_resolved",
        }.to_owned();
        CandidateGroup {
            terminal_name: name,
            call_site_ids,
            candidate_count: ids.len(),
            candidate_definition_ids: ids,
            resolution,
            basis: "simple imported terminal identifier equality; not Rust name resolution",
        }
    }).collect()
}

struct SyntaxReplacement {
    byte_start: usize,
    source_len: usize,
    replacement: String,
}

fn macro_or_attribute_group(trees: &[TokenTree], index: usize) -> bool {
    if index > 0 {
        if let TokenTree::Punct(punct) = &trees[index - 1] {
            if punct.as_char() == '!' || punct.as_char() == '#' {
                return true;
            }
        }
    }
    let start = index.saturating_sub(3);
    trees[start..index].iter().any(|tree| matches!(tree, TokenTree::Punct(punct) if punct.as_char() == '!'))
}

fn collect_gen_replacements(stream: TokenStream, output: &mut Vec<(usize, usize)>) {
    let trees: Vec<TokenTree> = stream.into_iter().collect();
    let mut index = 0;
    while index < trees.len() {
        if matches!(&trees[index], TokenTree::Ident(ident) if ident == "gen") {
            let mut body_index = index + 1;
            if matches!(trees.get(body_index), Some(TokenTree::Ident(ident)) if ident == "move") {
                body_index += 1;
            }
            if matches!(trees.get(body_index), Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Brace) {
                let location = trees[index].span().start();
                output.push((location.line, location.column));
            }
        }
        if let TokenTree::Group(group) = &trees[index] {
            if !macro_or_attribute_group(&trees, index) {
                collect_gen_replacements(group.stream(), output);
            }
        }
        index += 1;
    }
}

fn collect_const_impl_replacements(stream: TokenStream, output: &mut Vec<(usize, usize)>) {
    let trees: Vec<TokenTree> = stream.into_iter().collect();
    let mut index = 0;
    while index < trees.len() {
        if matches!(&trees[index], TokenTree::Ident(ident) if ident == "const")
            && matches!(trees.get(index + 1), Some(TokenTree::Ident(ident)) if ident == "impl")
        {
            let location = trees[index].span().start();
            output.push((location.line, location.column));
        }
        if let TokenTree::Group(group) = &trees[index] {
            if !macro_or_attribute_group(&trees, index) {
                collect_const_impl_replacements(group.stream(), output);
            }
        }
        index += 1;
    }
}

fn line_start_offsets(source: &str) -> Vec<usize> {
    let mut offsets = vec![0];
    for (index, byte) in source.bytes().enumerate() {
        if byte == b'\n' {
            offsets.push(index + 1);
        }
    }
    offsets
}

fn adapt_syntax_for_syn(source: &str) -> Result<(String, BTreeMap<usize, Vec<usize>>, Vec<&'static str>), String> {
    let stream = TokenStream::from_str(source).map_err(|error| format!("Rust tokenization failed: {error}"))?;
    let mut gen_locations = Vec::new();
    collect_gen_replacements(stream.clone(), &mut gen_locations);
    gen_locations.sort_unstable();
    gen_locations.dedup();
    let mut const_impl_locations = Vec::new();
    collect_const_impl_replacements(stream, &mut const_impl_locations);
    const_impl_locations.sort_unstable();
    const_impl_locations.dedup();
    let line_starts = line_start_offsets(source);
    let mut replacements = Vec::new();
    let mut inserted_columns: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut shifts_by_line: BTreeMap<usize, usize> = BTreeMap::new();
    for (line, original_column) in gen_locations {
        let line_start = *line_starts.get(line.saturating_sub(1))
            .ok_or_else(|| format!("gen block span refers to missing line {line}"))?;
        let byte_start = line_start + original_column;
        if source.get(byte_start..byte_start + 3) != Some("gen") {
            return Err(format!("gen block span does not point to the expected source token at {line}:{original_column}"));
        }
        let shift = shifts_by_line.entry(line).or_default();
        let transformed_end_column = original_column + *shift + "async".len();
        inserted_columns.entry(line).or_default().push(transformed_end_column);
        *shift += "async".len() - "gen".len();
        replacements.push(SyntaxReplacement { byte_start, source_len: 3, replacement: "async".to_owned() });
    }
    for &(line, original_column) in &const_impl_locations {
        let line_start = *line_starts.get(line.saturating_sub(1))
            .ok_or_else(|| format!("const impl span refers to missing line {line}"))?;
        let byte_start = line_start + original_column;
        if source.get(byte_start..byte_start + 5) != Some("const") {
            return Err(format!("const impl span does not point to the expected source token at {line}:{original_column}"));
        }
        // Preserve byte and column offsets while presenting syntax accepted by syn.
        replacements.push(SyntaxReplacement { byte_start, source_len: 5, replacement: "     ".to_owned() });
    }
    let mut transformed = source.to_owned();
    replacements.sort_by_key(|replacement| std::cmp::Reverse(replacement.byte_start));
    for replacement in replacements {
        transformed.replace_range(
            replacement.byte_start..replacement.byte_start + replacement.source_len,
            &replacement.replacement,
        );
    }
    for columns in inserted_columns.values_mut() {
        columns.sort_unstable();
    }
    let mut adapters = Vec::new();
    if !inserted_columns.is_empty() {
        adapters.push("rust-2024-gen-block-span-rebased-to-async-syntax");
    }
    if !const_impl_locations.is_empty() {
        adapters.push("rust-2024-const-impl-elided-for-syn-syntax");
    }
    Ok((transformed, inserted_columns, adapters))
}

fn path_segments(path: &str) -> Vec<&str> {
    path.split("::").map(str::trim).filter(|segment| !segment.is_empty()).collect()
}

fn mir_variant_dispatch_candidates(
    variants: &[EnumVariantRecord],
    match_arms: &[MatchArmRecord],
) -> Vec<VariantDispatchCandidate> {
    variants.iter().filter(|variant| variant.enum_category.starts_with("mir_")).map(|variant| {
        let mut explicit = Vec::new();
        let mut unqualified = Vec::new();
        for arm in match_arms {
            let exact_in_arm = arm.variant_paths.iter().any(|path| {
                let segments = path_segments(path);
                segments.last().copied() == Some(variant.name.as_str())
                    && segments.len() >= 2
                    && segments[segments.len() - 2] == variant.enum_name
            });
            let bare_in_arm = arm.variant_paths.iter().any(|path| {
                let segments = path_segments(path);
                segments.len() == 1 && segments[0] == variant.name
            });
            if exact_in_arm {
                explicit.push(arm.id.clone());
            } else if bare_in_arm {
                unqualified.push(arm.id.clone());
            }
        }
        let mut all = explicit.clone();
        all.extend(unqualified.iter().cloned());
        all.sort();
        all.dedup();
        VariantDispatchCandidate {
            variant_id: variant.id.clone(),
            match_arm_ids: all,
            explicit_qualified_candidates: explicit,
            unqualified_candidates: unqualified,
            classification: "candidate_edges_only_requires_manual_review",
        }
    }).collect()
}

fn is_machine_trait_owner(owner: Option<&str>) -> bool {
    owner.is_some_and(|owner| owner == "trait Machine")
}

fn is_machine_impl_owner(owner: Option<&str>) -> bool {
    owner.and_then(|owner| owner.strip_prefix("impl "))
        .and_then(|rest| rest.split_once(" for ").map(|(trait_path, _)| trait_path))
        .is_some_and(is_machine_trait_path)
}

fn machine_hook_candidates(symbols: &[SymbolRecord]) -> Vec<MachineHookCandidate> {
    symbols.iter()
        .filter(|symbol| symbol.kind == "trait_method" && is_machine_trait_owner(symbol.owner.as_deref()))
        .map(|trait_method| {
            let implementations = symbols.iter().filter(|candidate| {
                candidate.kind == "method"
                    && candidate.name == trait_method.name
                    && is_machine_impl_owner(candidate.owner.as_deref())
            }).map(|candidate| candidate.id.clone()).collect();
            MachineHookCandidate {
                trait_method_id: trait_method.id.clone(),
                method_name: trait_method.name.clone(),
                trait_method_path: trait_method.path.clone(),
                has_default_body: trait_method.has_body == Some(true),
                implementation_candidate_ids: implementations,
                classification: "name_matched_impl_candidates_only_requires_type_resolution_and_review",
            }
        }).collect()
}

fn check_source_file(root: &Path, file: &LockedFile) -> Result<(SourceFileRecord, Collector), String> {
    let full_path = root.join(&file.path);
    let bytes = fs::read(&full_path).map_err(|error| format!("{}: {error}", file.path))?;
    let digest = sha256(&bytes);
    if file.sha256.as_deref() != Some(digest.as_str()) {
        return Err(format!("{}: source SHA256 differs from source-lock (locked {:?}, actual {})", file.path, file.sha256, digest));
    }
    let source = std::str::from_utf8(&bytes).map_err(|error| format!("{}: invalid UTF-8: {error}", file.path))?;
    let (parse_source, inserted_columns, syntax_adapters) = match adapt_syntax_for_syn(source) {
        Ok(adapted) => adapted,
        Err(error) => {
            return Ok((SourceFileRecord {
                path: file.path.clone(),
                component: file.component.clone(),
                source_sha256: digest,
                parsed: false,
                parse_error: Some(error),
                syntax_adapters: Vec::new(),
            }, Collector::default()));
        }
    };
    let mut collector = Collector::default();
    collector.context = Some(SourceContext { path: file.path.clone(), component: file.component.clone(), inserted_columns });
    match syn::parse_file(&parse_source) {
        Ok(file_ast) => {
            collector.visit_file(&file_ast);
            Ok((SourceFileRecord {
                path: file.path.clone(),
                component: file.component.clone(),
                source_sha256: digest,
                parsed: true,
                parse_error: None,
                syntax_adapters,
            }, collector))
        }
        Err(error) => {
            let location = collector.span(error.span());
            let source_line = source.lines().nth(location.line.saturating_sub(1)).unwrap_or("").trim();
            Ok((SourceFileRecord {
                path: file.path.clone(),
                component: file.component.clone(),
                source_sha256: digest,
                parsed: false,
                parse_error: Some(format!("{error} at {}:{} near `{}`", location.line, location.column, source_line)),
                syntax_adapters,
            }, collector))
        }
    }
}

fn parse_lock(path: &Path) -> Result<(Lock, String), String> {
    let bytes = fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?;
    let digest = sha256(&bytes);
    let lock: Lock = serde_json::from_slice(&bytes).map_err(|error| format!("{}: {error}", path.display()))?;
    if lock.schema_version != 1 {
        return Err(format!("source-lock schema_version must be 1, got {}", lock.schema_version));
    }
    Ok((lock, digest))
}

fn analyze(root: &Path) -> Result<Inventory, String> {
    let lock_path = root.join("upstream/source-lock.json");
    let (lock, lock_digest) = parse_lock(&lock_path)?;
    let analyzer_manifest_hash = hash_file(root, "tools/source-analysis/Cargo.toml")?;
    let analyzer_lock_hash = hash_file(root, "tools/source-analysis/Cargo.lock")?;
    let analyzer_source_hash = hash_file(root, "tools/source-analysis/src/main.rs")?;
    let mut rust_files: Vec<&LockedFile> = lock.files.iter().filter(|file| file.path.ends_with(".rs")).collect();
    rust_files.sort_by(|a, b| a.path.cmp(&b.path));
    if rust_files.is_empty() {
        return Err("source-lock has no Rust units".to_owned());
    }
    let mut source_files = Vec::with_capacity(rust_files.len());
    let mut symbols = Vec::new();
    let mut enum_variants = Vec::new();
    let mut match_arms = Vec::new();
    let mut imports = Vec::new();
    let mut call_sites = Vec::new();
    let mut macro_sites = Vec::new();
    let mut parse_failures = Vec::new();
    for locked in &rust_files {
        let (record, mut collector) = check_source_file(root, locked)?;
        if !record.parsed {
            parse_failures.push(format!("{}: {}", record.path, record.parse_error.as_deref().unwrap_or("parse failed")));
        }
        source_files.push(record);
        symbols.append(&mut collector.symbols);
        enum_variants.append(&mut collector.variants);
        match_arms.append(&mut collector.match_arms);
        imports.append(&mut collector.imports);
        call_sites.append(&mut collector.calls);
        macro_sites.append(&mut collector.macros);
    }
    if !parse_failures.is_empty() {
        return Err(format!("{} Rust file(s) failed syn parsing:\n{}", parse_failures.len(), parse_failures.join("\n")));
    }
    source_files.sort_by(|a, b| a.path.cmp(&b.path));
    symbols.sort_by(|a, b| (&a.path, a.span.line, a.span.column, &a.kind, &a.symbol).cmp(&(&b.path, b.span.line, b.span.column, &b.kind, &b.symbol)));
    enum_variants.sort_by(|a, b| (&a.path, a.span.line, a.span.column, &a.symbol).cmp(&(&b.path, b.span.line, b.span.column, &b.symbol)));
    match_arms.sort_by(|a, b| (&a.path, a.span.line, a.span.column, &a.pattern).cmp(&(&b.path, b.span.line, b.span.column, &b.pattern)));
    imports.sort_by(|a, b| (&a.path, a.span.line, a.span.column, &a.imported_path).cmp(&(&b.path, b.span.line, b.span.column, &b.imported_path)));
    call_sites.sort_by(|a, b| (&a.path, a.span.line, a.span.column, &a.kind, &a.callee).cmp(&(&b.path, b.span.line, b.span.column, &b.kind, &b.callee)));
    macro_sites.sort_by(|a, b| (&a.path, a.span.line, a.span.column, &a.macro_path).cmp(&(&b.path, b.span.line, b.span.column, &b.macro_path)));

    let candidate_graph = candidate_groups(&call_sites, &symbols);
    let import_candidate_graph = import_candidate_groups(&imports, &symbols);
    let variant_dispatch = mir_variant_dispatch_candidates(&enum_variants, &match_arms);
    let machine_hooks = machine_hook_candidates(&symbols);
    let function_count = symbols.iter().filter(|symbol| matches!(symbol.kind.as_str(), "function" | "method" | "trait_method")).count();
    let body_count = symbols.iter().filter(|symbol| matches!(symbol.kind.as_str(), "function" | "method" | "trait_method") && symbol.has_body == Some(true)).count();
    let enum_count = symbols.iter().filter(|symbol| symbol.kind == "enum").count();
    let mir_variant_count = enum_variants.iter().filter(|variant| variant.enum_category.starts_with("mir_")).count();
    let machine_count = symbols.iter().filter(|symbol| matches!(symbol.kind.as_str(), "method" | "trait_method") && symbol.machine_context).count();
    let hook_count = symbols.iter().filter(|symbol| symbol.machine_hook_candidate).count();
    let diagnostic_count = macro_sites.iter().filter(|site| site.site_kind == "invocation" && site.classification != "other_macro").count();
    let unresolved_call_groups = candidate_graph.iter().filter(|group| group.resolution == "unresolved_in_selected_rust_sources").count();
    let ambiguous_call_groups = candidate_graph.iter().filter(|group| group.resolution == "ambiguous_name_candidates_only_not_resolved").count();
    let unresolved_import_groups = import_candidate_graph.iter().filter(|group| group.resolution == "unresolved_in_selected_rust_sources").count();
    let symbol_count = symbols.len();
    let variant_count = enum_variants.len();
    let import_count = imports.len();
    let call_count = call_sites.len();
    let macro_count = macro_sites.iter().filter(|site| site.site_kind == "invocation").count();
    let macro_definition_count = macro_sites.iter().filter(|site| site.site_kind == "definition").count();
    let match_arm_count = match_arms.len();
    let variant_dispatch_count = variant_dispatch.len();
    let machine_hook_count = machine_hooks.len();
    let syntax_adapted_files = source_files.iter().filter(|file| !file.syntax_adapters.is_empty()).count();

    Ok(Inventory {
        schema_version: 1,
        analyzer: AnalyzerInfo {
            crate_name: "lean-miri-source-analysis",
            syn_version: "2.0.108",
            schema: "syn-ast-inventory-v1",
            manifest_sha256: analyzer_manifest_hash,
            cargo_lock_sha256: analyzer_lock_hash,
            source_sha256: analyzer_source_hash,
        },
        source_lock: SourceLockInfo { path: "upstream/source-lock.json", file_count: lock.files.len(), rust_file_count: rust_files.len(), sha256: lock_digest },
        limitations: vec![
            "This inventory parses source text with syn; it does not expand declarative or procedural macros, derive macros, include!, cfg-selected code, build scripts, or generated Rust.",
            "It inventories declarations, enum variants, function bodies, imports, direct-call syntax, and macro call sites; it does not type-check, resolve names, infer effects, or prove Miri/Lean semantic correspondence.",
            "The candidate call/import graph uses terminal identifier equality only. Candidate edges are over-approximations and unresolved entries may refer to generated code, external crates, macros, or source outside the selected archive.",
            "MIR enum names are classified syntactically by selected enum identifiers; this is an inventory aid, not a claim that every execution path or enum is semantically covered.",
            "The selected Rust inventory excludes native C/C++ implementation sources and archived fixture trees as declared by source-lock and tracking/exclusions.json.",
            "The Rust AST does not reveal macro-expanded UB checks, so diagnostic macro call sites are only source-level candidates.",
            "Rust 2024 gen blocks and const trait impl syntax unsupported by syn 2.0.108 use narrow token-aware adapters: `gen [move] {` is parsed as `async [move] {` with source columns rebased, and `const impl` is parsed as `impl` with source columns preserved. These adapters do not model generator or const-impl semantics; token-body hashes in affected declarations describe adapted syntax, while source-file hashes and source references use original locked bytes.",
            "Match-arm links to MIR enum variants are syntactic name candidates. They do not prove that a match handles a variant on all paths, that the match is reachable, or that it implements the required semantics; wildcard arms and macro-generated matches require separate review.",
            "Machine trait method links to implementation methods use trait/impl owner shape and equal method names only. Rust type resolution, conditional compilation, generated impls, and default-method behavior are not established by this link graph.",
            "Explicit path calls and receiver-bearing method calls are retained individually. The graph does not perform Rust type/name resolution; method calls remain dynamically dispatched/unresolved candidates unless a separate reviewed relation is recorded.",
        ],
        source_files,
        symbols,
        enum_variants,
        match_arms,
        imports,
        call_sites,
        macro_sites,
        candidate_graph,
        import_candidate_graph,
        mir_variant_dispatch_candidates: variant_dispatch,
        machine_hook_candidates: machine_hooks,
        summary: Summary {
            locked_rust_files: rust_files.len(),
            parsed_rust_files: rust_files.len() - parse_failures.len(),
            parse_failures: parse_failures.len(),
            syntax_adapted_files,
            symbols: symbol_count,
            functions: function_count,
            functions_with_bodies: body_count,
            enums: enum_count,
            enum_variants: variant_count,
            mir_enum_variants: mir_variant_count,
            machine_trait_or_impl_methods: machine_count,
            machine_hook_name_candidates: hook_count,
            imports: import_count,
            function_and_method_call_sites: call_count,
            match_arms: match_arm_count,
            macro_call_sites: macro_count,
            macro_definition_sites: macro_definition_count,
            diagnostic_macro_call_sites: diagnostic_count,
            mir_variant_dispatch_candidates: variant_dispatch_count,
            machine_trait_hook_candidates: machine_hook_count,
            unresolved_call_name_groups: unresolved_call_groups,
            ambiguous_call_name_groups: ambiguous_call_groups,
            unresolved_import_name_groups: unresolved_import_groups,
        },
    })
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: lean-miri-source-analysis <repo-root> <output.json>");
        std::process::exit(2);
    }
    let root = PathBuf::from(&args[1]);
    let output = PathBuf::from(&args[2]);
    match analyze(&root) {
        Ok(inventory) => {
            if let Some(parent) = output.parent() {
                if let Err(error) = fs::create_dir_all(parent) {
                    eprintln!("{}: {error}", parent.display());
                    std::process::exit(1);
                }
            }
            let serialized = match serde_json::to_vec_pretty(&inventory) {
                Ok(bytes) => bytes,
                Err(error) => {
                    eprintln!("JSON serialization failed: {error}");
                    std::process::exit(1);
                }
            };
            if let Err(error) = fs::write(&output, [serialized.as_slice(), b"\n"].concat()) {
                eprintln!("{}: {error}", output.display());
                std::process::exit(1);
            }
            eprintln!("parsed {} Rust units; wrote AST inventory to {}", inventory.summary.parsed_rust_files, output.display());
        }
        Err(error) => {
            eprintln!("source analysis failed: {error}");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_variants_machine_methods_calls_imports_and_ub_macros() {
        let source = r#"
            use crate::runtime::run;
            trait Machine { fn before_call(&self); }
            enum StatementKind { Assign(i32), Nop }
            struct TestMachine;
            impl Machine for TestMachine {
                fn before_call(&self) { throw_ub!("forbidden"); helper(); run(); match StatementKind::Nop { StatementKind::Assign(_) => {}, StatementKind::Nop => {} } }
            }
            fn helper() {}
        "#;
        let parsed = syn::parse_file(source).expect("sample is valid Rust syntax");
        let mut collector = Collector::default();
        collector.context = Some(SourceContext {
            path: "sample.rs".to_owned(),
            component: "fixture".to_owned(),
            inserted_columns: BTreeMap::new(),
        });
        collector.visit_file(&parsed);

        assert_eq!(collector.variants.len(), 2);
        assert!(collector.variants.iter().all(|variant| variant.enum_category == "mir_statement"));
        assert!(collector.symbols.iter().any(|symbol| symbol.kind == "trait_method" && symbol.machine_context));
        assert!(collector.symbols.iter().any(|symbol| symbol.kind == "method" && symbol.machine_context));
        assert!(collector.symbols.iter().any(|symbol| symbol.name == "before_call" && symbol.machine_hook_candidate));
        let hooks = machine_hook_candidates(&collector.symbols);
        assert!(hooks.iter().any(|hook| hook.method_name == "before_call" && hook.implementation_candidate_ids.len() == 1));
        assert_eq!(collector.imports.len(), 1);
        assert_eq!(collector.calls.len(), 2);
        assert!(collector.calls.iter().any(|call| call.terminal_name.as_deref() == Some("helper")));
        assert!(collector.calls.iter().any(|call| call.terminal_name.as_deref() == Some("run")));
        assert!(collector.calls.iter().any(|call| call.callee_path.as_deref() == Some("run")));
        assert_eq!(collector.macros.len(), 1);
        assert_eq!(collector.macros[0].classification, "ub");
        assert_eq!(collector.match_arms.len(), 2);
        assert!(collector.match_arms.iter().any(|arm| arm.variant_paths.contains(&"StatementKind :: Assign".to_owned())));
        let dispatch = mir_variant_dispatch_candidates(&collector.variants, &collector.match_arms);
        assert_eq!(dispatch.len(), 2);
        assert!(dispatch.iter().any(|row| !row.explicit_qualified_candidates.is_empty()));
        assert!(collector.symbols.iter().any(|symbol| symbol.name == "before_call" && symbol.body_token_sha256.is_some()));
    }

    #[test]
    fn macro_definition_is_not_misreported_as_invocation() {
        let source = "macro_rules! local_check { () => { panic!() } }\nfn caller() { local_check!(); }";
        let parsed = syn::parse_file(source).expect("sample parses");
        let mut collector = Collector::default();
        collector.context = Some(SourceContext { path: "sample.rs".into(), component: "fixture".into(), inserted_columns: BTreeMap::new() });
        collector.visit_file(&parsed);
        assert_eq!(collector.macros.iter().filter(|site| site.site_kind == "definition").count(), 1);
        assert_eq!(collector.macros.iter().filter(|site| site.site_kind == "invocation").count(), 1);
        assert_eq!(collector.macros.iter().find(|site| site.site_kind == "definition").unwrap().macro_name, "local_check");
    }

    #[test]
    fn machine_trait_path_accepts_generic_and_qualified_paths() {
        assert!(is_machine_trait_path("Machine"));
        assert!(is_machine_trait_path("rustc_const_eval :: interpret :: Machine < 'tcx >"));
        assert!(!is_machine_trait_path("MachineStopType"));
    }

    #[test]
    fn gen_block_adapter_rebases_spans_and_leaves_macro_tokens_opaque() {
        let source = "fn f() { let x = gen move { yield 1; }; fn later() {} }";
        let (adapted, inserted, adapters) = adapt_syntax_for_syn(source).expect("source tokens");
        assert!(adapted.contains("async move { yield 1; }"));
        assert!(adapters.contains(&"rust-2024-gen-block-span-rebased-to-async-syntax"));
        let parsed = syn::parse_file(&adapted).expect("adapted syntax parses");
        let mut collector = Collector::default();
        collector.context = Some(SourceContext {
            path: "sample.rs".into(), component: "fixture".into(), inserted_columns: inserted,
        });
        collector.visit_file(&parsed);
        let later = collector.symbols.iter().find(|symbol| symbol.name == "later").unwrap();
        assert_eq!(source.find("fn later").unwrap(), later.span.column);

        let macro_source = "fn f() { opaque!(gen move {}); }";
        let (unchanged, macro_insertions, macro_adapters) = adapt_syntax_for_syn(macro_source).expect("macro tokens");
        assert_eq!(macro_source, unchanged);
        assert!(macro_insertions.is_empty());
        assert!(macro_adapters.is_empty());
        assert!(syn::parse_file(&unchanged).is_ok());
    }

    #[test]
    fn const_impl_adapter_keeps_source_columns_and_ignores_macro_tokens() {
        let source = "const impl Default for X { fn default() -> Self { X } }\nfn after() {}";
        let (adapted, inserted, adapters) = adapt_syntax_for_syn(source).expect("source tokens");
        assert!(adapted.starts_with("      impl Default"));
        assert!(adapters.contains(&"rust-2024-const-impl-elided-for-syn-syntax"));
        assert!(inserted.is_empty());
        let parsed = syn::parse_file(&adapted).expect("adapted syntax parses");
        let mut collector = Collector::default();
        collector.context = Some(SourceContext {
            path: "sample.rs".into(), component: "fixture".into(), inserted_columns: inserted,
        });
        collector.visit_file(&parsed);
        let after = collector.symbols.iter().find(|symbol| symbol.name == "after").unwrap();
        assert_eq!(source.lines().nth(1).unwrap().find("fn after").unwrap(), after.span.column);

        let macro_source = "fn f() { opaque!(const impl Default for X {}); }";
        let (unchanged, _, macro_adapters) = adapt_syntax_for_syn(macro_source).expect("macro tokens");
        assert_eq!(macro_source, unchanged);
        assert!(macro_adapters.is_empty());
    }

    #[test]
    fn reports_candidate_edges_as_unresolved_name_matches() {
        let mut calls = vec![CallSiteRecord {
            id: "c0".to_owned(),
            path: "sample.rs".to_owned(),
            component: "fixture".to_owned(),
            enclosing_symbol: None,
            kind: "function_call".to_owned(),
            callee: "mystery".to_owned(),
            callee_path: Some("mystery".to_owned()),
            receiver: None,
            terminal_name: Some("mystery".to_owned()),
            span: SourceSpan { line: 1, column: 0, end_line: 1, end_column: 8 },
        }];
        calls.push(CallSiteRecord {
            id: "c1".to_owned(),
            path: "sample.rs".to_owned(),
            component: "fixture".to_owned(),
            enclosing_symbol: None,
            kind: "function_call".to_owned(),
            callee: "known".to_owned(),
            callee_path: Some("known".to_owned()),
            receiver: None,
            terminal_name: Some("known".to_owned()),
            span: SourceSpan { line: 2, column: 0, end_line: 2, end_column: 6 },
        });
        let symbols = vec![SymbolRecord {
            id: "s0".to_owned(),
            path: "sample.rs".to_owned(),
            component: "fixture".to_owned(),
            kind: "function".to_owned(),
            name: "known".to_owned(),
            symbol: "known".to_owned(),
            span: SourceSpan { line: 3, column: 0, end_line: 3, end_column: 12 },
            visibility: None,
            signature: None,
            has_body: Some(true),
            body_span: None,
            body_token_sha256: None,
            owner: None,
            enum_category: None,
            machine_context: false,
            machine_hook_candidate: false,
        }];
        let groups = candidate_groups(&calls, &symbols);
        assert_eq!(groups.len(), 2);
        assert_eq!(groups[0].resolution, "single_name_candidate_only_not_resolved");
        assert_eq!(groups[1].resolution, "unresolved_in_selected_rust_sources");
    }
}
