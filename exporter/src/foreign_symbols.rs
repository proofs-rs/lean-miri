//! Exact foreign-symbol and allocator-shim evidence used by Miri's
//! `foreign_items.rs` and `machine.rs` lookup paths.
use super::*;

use rustc_ast::expand::allocator;
use rustc_attr_ir::Linkage as SymbolLinkage;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags as F;
use rustc_middle::middle::dependency_format::Linkage as DependencyLinkage;
use rustc_middle::middle::exported_symbols::ExportedSymbol;

#[derive(serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum ImportLinkage {
    None,
    ExternalWeak { raw: String },
    Other { raw: String },
}
#[derive(serde::Serialize)]
struct Declaration {
    definition: u64,
    symbol: String,
    typing_env: &'static str,
    #[serde(rename = "type")]
    ty: u64,
    layout: u64,
    import_linkage: ImportLinkage,
    definition_mutability: &'static str,
    type_is_freeze: bool,
    decl_is_mut: bool,
}
#[derive(Clone, serde::Serialize)]
struct Candidate {
    iteration_index: usize,
    used: bool,
    symbol: String,
    definition: u64,
    explicit_symbol: bool,
    crate_index: u32,
    crate_name: String,
    weak: bool,
    span: u64,
    definition_kind: &'static str,
    compiler_builtins: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    instance_id: Option<u64>,
}
#[derive(serde::Serialize)]
struct Ambiguous {
    symbol: String,
    resolution: &'static str,
    reason: &'static str,
}
impl Ambiguous {
    fn new(symbol: String) -> Self {
        Self {
            symbol,
            resolution: "ambiguous",
            reason: "source lookup_exported_symbol found equal-strength duplicate definitions",
        }
    }
}
#[derive(serde::Serialize)]
#[serde(untagged)]
enum SelectedExport {
    Ambiguous(Ambiguous),
    Other {
        symbol: String,
        kind: &'static str,
        definition: u64,
        instance_id: Option<u64>,
    },
    Static {
        symbol: String,
        kind: &'static str,
        definition: u64,
        declaration: Declaration,
        allocation: u64,
    },
}
#[derive(serde::Serialize)]
#[serde(untagged)]
enum Fallback {
    Ambiguous(Ambiguous),
    Candidate(Candidate),
}
#[derive(serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum AllocatorTarget {
    Special { method: &'static str },
    Redirect { symbol: String },
}
#[derive(serde::Serialize)]
struct AllocatorShim {
    symbol: String,
    target: AllocatorTarget,
}
#[derive(serde::Serialize)]
struct TargetFacts {
    os: String,
    env: String,
    binary_format: String,
    families: Vec<String>,
}
#[derive(serde::Serialize)]
struct ExternStatics {
    declarations: Vec<Declaration>,
    selected_exported: Vec<SelectedExport>,
    typing_env: &'static str,
}
#[derive(serde::Serialize)]
pub(super) struct Catalog {
    target: TargetFacts,
    no_alloc_shim_symbol: String,
    allocator_shims: Vec<AllocatorShim>,
    #[serde(skip_serializing_if = "Option::is_none")]
    exported_candidates: Option<Vec<Candidate>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    selected_foreign_fallbacks: Option<Vec<Fallback>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    extern_statics: Option<ExternStatics>,
}

fn definition_kind(tcx: TyCtxt<'_>, def: rustc_hir::def_id::DefId) -> &'static str {
    use rustc_hir::def::DefKind;
    match tcx.def_kind(def) {
        DefKind::Fn => "function",
        DefKind::AssocFn => "associated_function",
        DefKind::Static { .. } => "static",
        _ => "other",
    }
}

/// The exact `machine.rs::extern_static_pointer` declaration queries for a
/// demanded foreign static. The source uses the current typing environment;
/// static definitions are monomorphic, so the exported query environment is
/// the pinned fully-monomorphized one.
fn extern_static_declaration<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    def: rustc_hir::def_id::DefId,
) -> Result<Declaration, String> {
    use rustc_hir::def::DefKind;
    let DefKind::Static { mutability, .. } = tcx.def_kind(def) else {
        return Ok(export_failure(
            "foreign_symbols::extern_static_declaration",
            "extern-static declaration DefId is not a static",
        )?);
    };
    let instance = ty::Instance::mono(tcx, def);
    let symbol = tcx.symbol_name(instance).name.to_string();
    let def_ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
    let env = ty::TypingEnv::fully_monomorphized();
    let attrs = tcx.codegen_fn_attrs(def);
    let import_linkage = match attrs.import_linkage {
        None => ImportLinkage::None,
        Some(rustc_attr_ir::Linkage::ExternalWeak) => ImportLinkage::ExternalWeak {
            raw: format!("{:?}", rustc_attr_ir::Linkage::ExternalWeak),
        },
        Some(linkage) => ImportLinkage::Other {
            raw: format!("{linkage:?}"),
        },
    };
    let definition_mutability = match mutability {
        rustc_ast::Mutability::Mut => "mutable",
        rustc_ast::Mutability::Not => "immutable",
    };
    let type_ref = type_json(context, tcx, def_ty)?;
    Ok::<_, String>(match tcx.layout_of(env.as_query_input(def_ty)) {
        Ok(layout) => {
            let ty_is_freeze = layout.ty.is_freeze(tcx, env);
            let declaration_mutable = !(mutability == rustc_ast::Mutability::Not && ty_is_freeze);
            Declaration {
                definition: def_json(context, def),
                symbol,
                typing_env: "fully_monomorphized",
                ty: type_ref,
                layout: layout_value_json(context, tcx, layout),
                import_linkage,
                definition_mutability,
                type_is_freeze: ty_is_freeze,
                decl_is_mut: declaration_mutable,
            }
        }
        Err(error) => export_failure(
            "foreign_symbols::extern_static_declaration",
            format!(
                "{}; {}",
                "extern-static declaration layout query failed",
                format!("{error:?}")
            ),
        )?,
    })
}

fn candidate<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    crate_num: rustc_hir::def_id::CrateNum,
    def: rustc_hir::def_id::DefId,
    iteration_index: usize,
    used: bool,
) -> Result<Option<Candidate>, String> {
    let attrs = tcx.codegen_fn_attrs(def);
    // foreign_items.rs::lookup_exported_symbol performs this exact gate
    // before Instance::mono and tcx.symbol_name. Do not query non-candidates:
    // they may be generic/unreachable and are not semantically inspected.
    let explicit_symbol = attrs.symbol_name.is_some()
        || attrs.flags.contains(F::NO_MANGLE)
        || attrs.flags.contains(F::RUSTC_STD_INTERNAL_SYMBOL);
    if !explicit_symbol {
        return Ok(None);
    }
    // This is deliberately the same `Instance::mono` + `tcx.symbol_name`
    // query used by Miri, including for exports that are not callable.
    let instance = ty::Instance::mono(tcx, def);
    let symbol = tcx.symbol_name(instance).name.to_string();
    let kind = definition_kind(tcx, def);
    let instance_id = if kind == "function" || kind == "associated_function" {
        Some(context.register_instance_identity(instance))
    } else {
        None
    };
    let span = tcx.def_span(def);
    Ok(Some(Candidate {
        iteration_index,
        used,
        symbol,
        definition: def_json(context, def),
        explicit_symbol,
        crate_index: crate_num.as_u32(),
        crate_name: tcx.crate_name(crate_num).as_str().to_owned(),
        weak: attrs.linkage == Some(SymbolLinkage::WeakAny),
        span: span_json(context, tcx, span),
        definition_kind: kind,
        compiler_builtins: tcx.is_compiler_builtins(crate_num),
        instance_id,
    }))
}

/// Export source lookup winners for every exact symbol identity. The winner
/// selection is the same first/weak/strong rule as
/// `foreign_items.rs::lookup_exported_symbol`; equal-strength duplicates are
/// left as explicit ambiguity and their initializer is not queried.
fn selected_exports<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    candidates: &[Candidate],
    demanded_symbols: &[String],
) -> Result<Vec<SelectedExport>, String> {
    let mut winners: Vec<(String, Candidate, bool)> = Vec::new();
    for candidate in candidates {
        let symbol = candidate.symbol.clone();
        if !demanded_symbols.contains(&symbol) {
            continue;
        }
        let weak = candidate.weak;
        if let Some((_, current, ambiguous)) =
            winners.iter_mut().find(|(name, _, _)| *name == symbol)
        {
            if *ambiguous {
                continue;
            }
            let current_weak = current.weak;
            match (weak, current_weak) {
                (false, true) => *current = candidate.clone(),
                (true, false) => (),
                (true, true) | (false, false) => *ambiguous = true,
            }
        } else {
            winners.push((symbol, candidate.clone(), false));
        }
    }

    winners
        .into_iter()
        .map(|(symbol, winner, ambiguous)| {
            if ambiguous {
                return Ok(SelectedExport::Ambiguous(Ambiguous::new(symbol)));
            }
            let definition = winner.definition;
            let def = context
                .definitions
                .key(
                    usize::try_from(definition)
                        .map_err(|_| "selected definition ID exceeds host bounds")?,
                )
                .copied()
                .ok_or("selected definition ID is outside the definition pool")?;
            let kind = definition_kind(tcx, def);
            if kind != "static" {
                return Ok(SelectedExport::Other {
                    symbol,
                    kind,
                    definition,
                    instance_id: winner.instance_id,
                });
            }
            let declaration = extern_static_declaration(tcx, context, def)?;
            let allocation = if matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Static { .. })
            {
                let alloc_id = tcx.reserve_and_set_static_alloc(def);
                allocation_ref(context, tcx, alloc_id)?
            } else {
                return export_failure(
                    "foreign_symbols::selected_exports",
                    "selected definition ceased to be a static",
                );
            };
            Ok(SelectedExport::Static {
                symbol,
                kind: "static",
                definition,
                declaration,
                allocation,
            })
        })
        .collect()
}

/// Record the exact `lookup_exported_symbol` winner for demanded foreign-call
/// link names without querying a static initializer. Miri selects across all
/// symbol kinds first, then `lookup_exported_fn` checks that the winner is a
/// function; a static or other definition must therefore prevent a weaker
/// same-name function from being promoted.
fn selected_foreign_fallbacks(
    candidates: &[Candidate],
    demanded_symbols: &[String],
) -> Vec<Fallback> {
    let mut selected = Vec::new();
    for symbol in demanded_symbols {
        let mut winner: Option<&Candidate> = None;
        let mut ambiguous = false;
        for candidate in candidates {
            if candidate.symbol != *symbol {
                continue;
            }
            let weak = candidate.weak;
            if let Some(current) = winner {
                let current_weak = current.weak;
                match (weak, current_weak) {
                    (false, true) => winner = Some(candidate),
                    (true, false) => (),
                    (true, true) | (false, false) => ambiguous = true,
                }
                if ambiguous {
                    break;
                }
            } else {
                winner = Some(candidate);
            }
        }
        if ambiguous {
            selected.push(Fallback::Ambiguous(Ambiguous::new(symbol.clone())));
        } else if let Some(candidate) = winner {
            let row = candidate.clone();
            selected.push(Fallback::Candidate(row));
        }
    }
    selected
}

fn demanded_extern_statics<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Vec<Declaration>, String> {
    let mut definitions = context
        .allocation_ids
        .keys()
        .filter_map(|alloc_id| match tcx.try_get_global_alloc(*alloc_id) {
            Some(rustc_middle::mir::interpret::GlobalAlloc::Static(def))
                if tcx.is_foreign_item(def) =>
            {
                Some(def)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    definitions.sort_by_key(|def| (def.krate.as_u32(), def.index.as_u32()));
    definitions.dedup();
    Ok::<_, String>(
        definitions
            .into_iter()
            .map(|def| extern_static_declaration(tcx, context, def))
            .collect::<Result<Vec<_>, String>>()?,
    )
}

fn allocator_shims<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<AllocatorShim> {
    let Some(kind) = tcx.allocator_kind(()) else {
        return Vec::new();
    };
    let records = rustc_codegen_ssa::base::allocator_shim_contents(tcx, kind)
        .into_iter()
        .map(|method| {
            let source = rustc_symbol_mangling::mangle_internal_symbol(
                tcx,
                &allocator::global_fn_name(method.name),
            );
            let target = match method.special {
                Some(special) => {
                    let method = match special {
                        allocator::SpecialAllocatorMethod::Alloc => "alloc",
                        allocator::SpecialAllocatorMethod::AllocZeroed => "alloc_zeroed",
                        allocator::SpecialAllocatorMethod::Dealloc => "dealloc",
                        allocator::SpecialAllocatorMethod::Realloc => "realloc",
                    };
                    AllocatorTarget::Special { method }
                }
                None => AllocatorTarget::Redirect {
                    symbol: rustc_symbol_mangling::mangle_internal_symbol(
                        tcx,
                        &allocator::default_fn_name(method.name),
                    ),
                },
            };
            AllocatorShim {
                symbol: source,
                target,
            }
        })
        .collect::<Vec<_>>();
    records
}

/// Exact target facts used by `init_extern_statics` and dynamic-symbol
/// registration. These come from rustc's parsed Session target, not from the
/// target triple (whose spelling does not determine cfg families).
fn target_facts(tcx: TyCtxt<'_>) -> TargetFacts {
    let target = &tcx.sess.target;
    let mut families = target
        .families
        .iter()
        .map(|family| family.as_ref().to_owned())
        .collect::<Vec<_>>();
    families.sort();
    TargetFacts {
        os: target.os.desc_symbol().as_str().to_owned(),
        env: target.env.desc_symbol().as_str().to_owned(),
        binary_format: target.binary_format.desc_symbol().as_str().to_owned(),
        families,
    }
}

/// Reproduce `helpers::iter_exported_symbols` in its source order. For a
/// non-executable compilation does not demand executable-symbol lookup;
/// its catalog omits those queries instead of claiming an empty symbol set.
pub(super) fn export<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Catalog, String> {
    if !tcx
        .crate_types()
        .contains(&rustc_structures::CrateType::Executable)
    {
        // Executable exported-symbol traversal is not a query in library scope.
        let no_alloc = rustc_symbol_mangling::mangle_internal_symbol(
            tcx,
            allocator::NO_ALLOC_SHIM_IS_UNSTABLE,
        );
        return Ok(Catalog {
            target: target_facts(tcx),
            no_alloc_shim_symbol: no_alloc,
            allocator_shims: allocator_shims(tcx),
            exported_candidates: None,
            selected_foreign_fallbacks: None,
            extern_statics: None,
        });
    }
    let mut records = Vec::new();
    let mut iteration_index = 0usize;
    for def in tcx.hir_crate_items(()).definitions() {
        if !tcx.def_kind(def).has_codegen_attrs() || tcx.is_foreign_item(def) {
            continue;
        }
        let attrs = tcx.codegen_fn_attrs(def);
        let used = attrs.flags.contains(F::USED_COMPILER) || attrs.flags.contains(F::USED_LINKER);
        if used || attrs.contains_extern_indicator() {
            if let Some(entry) = candidate(
                tcx,
                context,
                LOCAL_CRATE,
                def.to_def_id(),
                iteration_index,
                used,
            )? {
                records.push(entry);
            }
            iteration_index += 1;
        }
    }

    let dependency_formats = tcx.dependency_formats(());
    let dependency_format = dependency_formats
        .get(&rustc_structures::CrateType::Executable)
        .ok_or_else(|| {
            "executable exported-symbol traversal lacks dependency_formats".to_owned()
        })?;

    for (crate_num, linkage) in dependency_format.iter_enumerated() {
        if crate_num == LOCAL_CRATE || *linkage == DependencyLinkage::NotLinked {
            continue;
        }
        for &(symbol, export_info) in tcx.exported_non_generic_symbols(crate_num) {
            if let ExportedSymbol::NonGeneric(def) = symbol {
                if !tcx.is_foreign_item(def) {
                    // The source helper passes `used`, but lookup ignores it.
                    // Preserve it for schema transparency and future consumers.
                    if let Some(entry) = candidate(
                        tcx,
                        context,
                        crate_num,
                        def,
                        iteration_index,
                        export_info.used,
                    )? {
                        records.push(entry);
                    }
                    iteration_index += 1;
                }
            }
        }
    }

    let no_alloc =
        rustc_symbol_mangling::mangle_internal_symbol(tcx, allocator::NO_ALLOC_SHIM_IS_UNSTABLE);
    let declarations = demanded_extern_statics(tcx, context)?;
    let demanded_symbols = declarations
        .iter()
        .map(|record| record.symbol.clone())
        .collect::<Vec<_>>();
    let selected = selected_exports(tcx, context, &records, &demanded_symbols)?;
    // foreign_items.rs first runs its Miri shim and then resolves an exported
    // function by the exact foreign link name when that shim delegates. Keep
    // those source-demanded candidates under the same iterator order and
    // weak/duplicate policy as runtime lookup, and promote only the selected
    // candidate to MIR. A missing or ambiguous symbol remains a runtime source
    // error; it is never replaced by a guessed body.
    let mut demanded_foreign_functions = context
        .instance_ids
        .keys()
        .filter(|instance| {
            matches!(instance.def, ty::InstanceKind::Item(_))
                && matches!(
                    tcx.def_kind(instance.def_id()),
                    rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
                )
                && tcx.is_foreign_item(instance.def_id())
        })
        .map(|instance| tcx.symbol_name(*instance).name.to_string())
        .collect::<Vec<_>>();
    demanded_foreign_functions.sort();
    demanded_foreign_functions.dedup();
    let selected_fallbacks = selected_foreign_fallbacks(&records, &demanded_foreign_functions);
    let mut promote = Vec::new();
    for row in &selected_fallbacks {
        let Fallback::Candidate(row) = row else {
            continue;
        };
        if !matches!(row.definition_kind, "function" | "associated_function") {
            continue;
        }
        if !demanded_foreign_functions
            .iter()
            .any(|demanded| demanded == &row.symbol)
        {
            continue;
        }
        let Some(id) = row.instance_id else {
            continue;
        };
        if let Some((instance, _)) = context
            .instance_ids
            .iter()
            .find(|(_, candidate_id)| **candidate_id == id)
        {
            promote.push(*instance);
        }
    }
    promote.sort_by_key(|instance| context.instance_ids[instance]);
    promote.dedup();
    for instance in promote {
        context.register_instance(instance);
    }
    Ok(Catalog {
        target: target_facts(tcx),
        no_alloc_shim_symbol: no_alloc,
        exported_candidates: Some(records),
        selected_foreign_fallbacks: Some(selected_fallbacks),
        extern_statics: Some(ExternStatics {
            declarations,
            selected_exported: selected,
            typing_env: "fully_monomorphized",
        }),
        allocator_shims: allocator_shims(tcx),
    })
}
