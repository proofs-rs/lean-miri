//! Exact foreign-symbol and allocator-shim evidence used by Miri's
//! `foreign_items.rs` and `machine.rs` lookup paths.
use super::*;

use rustc_ast::expand::allocator;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags as F;
use rustc_middle::middle::dependency_format::Linkage as DependencyLinkage;
use rustc_attr_ir::Linkage as SymbolLinkage;
use rustc_middle::middle::exported_symbols::ExportedSymbol;

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
) -> Value {
    use rustc_hir::def::DefKind;
    let DefKind::Static { mutability, .. } = tcx.def_kind(def) else {
        return json!({"status":"unsupported","reason":"extern-static declaration DefId is not a static"});
    };
    let instance = ty::Instance::mono(tcx, def);
    let symbol = tcx.symbol_name(instance).name.to_string();
    let def_ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
    let env = ty::TypingEnv::fully_monomorphized();
    let attrs = tcx.codegen_fn_attrs(def);
    let import_linkage = match attrs.import_linkage {
        None => json!({"kind":"none"}),
        Some(rustc_attr_ir::Linkage::ExternalWeak) => json!({
            "kind":"external_weak", "raw":format!("{:?}", rustc_attr_ir::Linkage::ExternalWeak)
        }),
        Some(linkage) => json!({"kind":"other", "raw":format!("{linkage:?}")}),
    };
    let definition_mutability = match mutability {
        rustc_ast::Mutability::Mut => "mutable",
        rustc_ast::Mutability::Not => "immutable",
    };
    let type_ref = type_json(context, tcx, def_ty);
    match tcx.layout_of(env.as_query_input(def_ty)) {
        Ok(layout) => {
            let ty_is_freeze = layout.ty.is_freeze(tcx, env);
            let declaration_mutable = !(mutability == rustc_ast::Mutability::Not && ty_is_freeze);
            json!({
                "status":"supported",
                "definition":def_json(def),
                "symbol":symbol,
                "typing_env":"fully_monomorphized",
                "type":type_ref,
                "layout":layout_value_json(context,tcx,layout),
                "import_linkage":import_linkage,
                "definition_mutability":definition_mutability,
                "type_is_freeze":ty_is_freeze,
                "decl_is_mut":declaration_mutable,
            })
        }
        Err(error) => json!({
            "status":"unsupported",
            "definition":def_json(def),
            "symbol":symbol,
            "typing_env":"fully_monomorphized",
            "type":type_ref,
            "import_linkage":import_linkage,
            "definition_mutability":definition_mutability,
            "reason":"extern-static declaration layout query failed",
            "error_debug":format!("{error:?}"),
        }),
    }
}

fn candidate<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    crate_num: rustc_hir::def_id::CrateNum,
    def: rustc_hir::def_id::DefId,
    iteration_index: usize,
    used: bool,
) -> Option<Value> {
    let attrs = tcx.codegen_fn_attrs(def);
    // foreign_items.rs::lookup_exported_symbol performs this exact gate
    // before Instance::mono and tcx.symbol_name. Do not query non-candidates:
    // they may be generic/unreachable and are not semantically inspected.
    let explicit_symbol = attrs.symbol_name.is_some()
        || attrs.flags.contains(F::NO_MANGLE)
        || attrs.flags.contains(F::RUSTC_STD_INTERNAL_SYMBOL);
    if !explicit_symbol {
        return None;
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
    let callable_identity = if instance_id.is_some() {
        Some(json!({
            "instance_kind": instance_kind_json(context, tcx, instance.def),
            "generic_args": generic_args_json(context, tcx, instance.args),
        }))
    } else {
        None
    };
    let span = tcx.def_span(def);
    let mut record = json!({
        "iteration_index": iteration_index,
        "used": used,
        "symbol": symbol,
        "definition": def_json(def),
        "explicit_symbol": explicit_symbol,
        "crate_index": crate_num.as_u32(),
        "crate_name": tcx.crate_name(crate_num).as_str(),
        "weak": attrs.linkage == Some(SymbolLinkage::WeakAny),
        "span": {"lo": span.lo().0, "hi": span.hi().0},
        "definition_kind": kind,
        "compiler_builtins": tcx.is_compiler_builtins(crate_num),
    });
    if let Some(instance_id) = instance_id {
        record["instance_id"] = json!(instance_id);
    }
    if let Some(identity) = callable_identity {
        record["callable_identity"] = identity;
    }
    Some(record)
}

/// Export source lookup winners for every exact symbol identity. The winner
/// selection is the same first/weak/strong rule as
/// `foreign_items.rs::lookup_exported_symbol`; equal-strength duplicates are
/// left as explicit ambiguity and their initializer is not queried.
fn selected_exports<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    candidates: &[Value],
    demanded_symbols: &[String],
) -> Value {
    let mut winners: Vec<(String, Value, bool)> = Vec::new();
    for candidate in candidates {
        let symbol = candidate["symbol"].as_str().unwrap_or_default().to_owned();
        if !demanded_symbols.contains(&symbol) {
            continue;
        }
        let weak = candidate["weak"].as_bool().unwrap_or(false);
        if let Some((_, current, ambiguous)) = winners.iter_mut().find(|(name, _, _)| *name == symbol) {
            if *ambiguous {
                continue;
            }
            let current_weak = current["weak"].as_bool().unwrap_or(false);
            match (weak, current_weak) {
                (false, true) => *current = candidate.clone(),
                (true, false) => (),
                (true, true) | (false, false) => *ambiguous = true,
            }
        } else {
            winners.push((symbol, candidate.clone(), false));
        }
    }

    Value::Array(winners.into_iter().map(|(symbol, winner, ambiguous)| {
        if ambiguous {
            return json!({"symbol":symbol,"status":"ambiguous",
                "reason":"source lookup_exported_symbol found equal-strength duplicate definitions"});
        }
        let Some(definition) = winner.get("definition") else {
            return json!({"symbol":symbol,"status":"unsupported",
                "reason":"selected source symbol has no exact DefId"});
        };
        let Some(crate_index) = definition.get("crate").and_then(Value::as_u64) else {
            return json!({"symbol":symbol,"status":"unsupported",
                "reason":"selected source symbol has no crate index"});
        };
        let Some(def_index) = definition.get("index").and_then(Value::as_u64) else {
            return json!({"symbol":symbol,"status":"unsupported",
                "reason":"selected source symbol has no DefId index"});
        };
        let def = rustc_hir::def_id::DefId {
            krate: rustc_hir::def_id::CrateNum::from_u32(crate_index as u32),
            index: rustc_hir::def_id::DefIndex::from_u32(def_index as u32),
        };
        let kind = definition_kind(tcx, def);
        if kind != "static" {
            return json!({"symbol":symbol,"status":"supported","kind":kind,
                "definition":definition,
                "instance_id":winner.get("instance_id").cloned().unwrap_or(Value::Null),
                "callable_identity":winner.get("callable_identity").cloned().unwrap_or(Value::Null)});
        }

        let declaration = extern_static_declaration(tcx, context, def);
        let allocation = if matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Static { .. }) {
            let alloc_id = tcx.reserve_and_set_static_alloc(def);
            let reference = allocation_ref(context, tcx, alloc_id);
            json!({"status":if allocation_status(context, &reference) == "supported" {
                    "supported"
                } else {
                    "unsupported"
                },"value":reference})
        } else {
            json!({"status":"unsupported","reason":"selected definition ceased to be a static"})
        };
        json!({"symbol":symbol,"status":if declaration["status"] == "supported"
                && allocation["status"] == "supported" {"supported"} else {"unsupported"},
            "kind":"static","definition":definition,"declaration":declaration,
            "allocation":allocation})
    }).collect())
}

/// Record the exact `lookup_exported_symbol` winner for demanded foreign-call
/// link names without querying a static initializer. Miri selects across all
/// symbol kinds first, then `lookup_exported_fn` checks that the winner is a
/// function; a static or other definition must therefore prevent a weaker
/// same-name function from being promoted.
fn selected_foreign_fallbacks(candidates: &[Value], demanded_symbols: &[String]) -> Value {
    let mut selected = Vec::new();
    for symbol in demanded_symbols {
        let mut winner: Option<&Value> = None;
        let mut ambiguous = false;
        for candidate in candidates {
            if candidate["symbol"].as_str() != Some(symbol.as_str()) { continue; }
            let weak = candidate["weak"].as_bool().unwrap_or(false);
            if let Some(current) = winner {
                let current_weak = current["weak"].as_bool().unwrap_or(false);
                match (weak, current_weak) {
                    (false, true) => winner = Some(candidate),
                    (true, false) => (),
                    (true, true) | (false, false) => ambiguous = true,
                }
                if ambiguous { break; }
            } else {
                winner = Some(candidate);
            }
        }
        if ambiguous {
            selected.push(json!({"symbol":symbol,"status":"ambiguous",
                "reason":"source lookup_exported_symbol found equal-strength duplicate definitions"}));
        } else if let Some(candidate) = winner {
            let mut row = candidate.clone();
            row["status"] = json!("supported");
            selected.push(row);
        }
    }
    Value::Array(selected)
}

fn demanded_extern_statics<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Value {
    let mut definitions = context.allocation_ids.keys().filter_map(|alloc_id| {
        match tcx.try_get_global_alloc(*alloc_id) {
            Some(rustc_middle::mir::interpret::GlobalAlloc::Static(def))
                if tcx.is_foreign_item(def) => Some(def),
            _ => None,
        }
    }).collect::<Vec<_>>();
    definitions.sort_by_key(|def| (def.krate.as_u32(), def.index.as_u32()));
    definitions.dedup();
    Value::Array(definitions.into_iter().map(|def| {
        extern_static_declaration(tcx, context, def)
    }).collect())
}

fn allocator_shims<'tcx>(tcx: TyCtxt<'tcx>) -> Value {
    let Some(kind) = tcx.allocator_kind(()) else {
        return compiler_fact(json!([]));
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
                    json!({"kind":"special","method":method})
                }
                None => json!({"kind":"redirect","symbol":
                    rustc_symbol_mangling::mangle_internal_symbol(
                        tcx, &allocator::default_fn_name(method.name))}),
            };
            json!({"symbol":source,"target":target})
        })
        .collect::<Vec<_>>();
    compiler_fact(json!(records))
}

/// Exact target facts used by `init_extern_statics` and dynamic-symbol
/// registration. These come from rustc's parsed Session target, not from the
/// target triple (whose spelling does not determine cfg families).
fn target_facts(tcx: TyCtxt<'_>) -> Value {
    let target = &tcx.sess.target;
    let mut families = target.families.iter()
        .map(|family| family.as_ref().to_owned())
        .collect::<Vec<_>>();
    families.sort();
    compiler_fact(json!({
        "os": target.os.desc_symbol().as_str().to_owned(),
        "env": target.env.desc_symbol().as_str().to_owned(),
        "binary_format": target.binary_format.desc_symbol().as_str().to_owned(),
        "families": families,
    }))
}

/// Reproduce `helpers::iter_exported_symbols` in its source order. For a
/// non-executable compilation Miri's query is unavailable; retain local
/// candidates for diagnosis, but mark the whole table unsupported so callers
/// cannot treat an incomplete dependency walk as a successful lookup.
pub(super) fn export<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>) -> Value {
    let mut records = Vec::new();
    let mut iteration_index = 0usize;
    for def in tcx.hir_crate_items(()).definitions() {
        if !tcx.def_kind(def).has_codegen_attrs() || tcx.is_foreign_item(def) {
            continue;
        }
        let attrs = tcx.codegen_fn_attrs(def);
        let used = attrs.flags.contains(F::USED_COMPILER) || attrs.flags.contains(F::USED_LINKER);
        if used || attrs.contains_extern_indicator() {
            if let Some(entry) = candidate(tcx, context, LOCAL_CRATE, def.to_def_id(), iteration_index, used) {
                records.push(entry);
            }
            iteration_index += 1;
        }
    }

    let dependency_formats = tcx.dependency_formats(());
    let Some(dependency_format) = dependency_formats.get(&rustc_structures::CrateType::Executable)
    else {
        let no_alloc = rustc_symbol_mangling::mangle_internal_symbol(
            tcx,
            allocator::NO_ALLOC_SHIM_IS_UNSTABLE,
        );
        return json!({
            "target":target_facts(tcx),
            "no_alloc_shim_symbol":compiler_fact(json!(no_alloc)),
            "exported_candidates":{"status":"unsupported",
                "reason":"source exported-symbol traversal requires executable dependency_formats",
                "local_evidence":records},
            "extern_statics":{"status":"unsupported",
                "reason":"source extern-static lookup requires the executable exported-symbol traversal",
                "declarations":[],"selected_exported":[]},
            "allocator_shims":allocator_shims(tcx),
        });
    };

    for (crate_num, linkage) in dependency_format.iter_enumerated() {
        if crate_num == LOCAL_CRATE || *linkage == DependencyLinkage::NotLinked {
            continue;
        }
        for &(symbol, export_info) in tcx.exported_non_generic_symbols(crate_num) {
            if let ExportedSymbol::NonGeneric(def) = symbol {
                if !tcx.is_foreign_item(def) {
                    // The source helper passes `used`, but lookup ignores it.
                    // Preserve it for schema transparency and future consumers.
                    if let Some(entry) = candidate(tcx, context, crate_num, def, iteration_index, export_info.used) {
                        records.push(entry);
                    }
                    iteration_index += 1;
                }
            }
        }
    }

    let no_alloc = rustc_symbol_mangling::mangle_internal_symbol(
        tcx,
        allocator::NO_ALLOC_SHIM_IS_UNSTABLE,
    );
    let declarations = demanded_extern_statics(tcx, context);
    let demanded_symbols = declarations.as_array().into_iter().flatten()
        .filter_map(|record| record.get("symbol").and_then(Value::as_str).map(str::to_owned))
        .collect::<Vec<_>>();
    let selected = selected_exports(tcx, context, &records, &demanded_symbols);
    // foreign_items.rs first runs its Miri shim and then resolves an exported
    // function by the exact foreign link name when that shim delegates. Keep
    // those source-demanded candidates under the same iterator order and
    // weak/duplicate policy as runtime lookup, and promote only the selected
    // candidate to MIR. A missing or ambiguous symbol remains a runtime source
    // error; it is never replaced by a guessed body.
    let mut demanded_foreign_functions = context.instance_ids.keys()
        .filter(|instance| matches!(instance.def, ty::InstanceKind::Item(_))
            && matches!(tcx.def_kind(instance.def_id()),
                rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn)
            && tcx.is_foreign_item(instance.def_id()))
        .map(|instance| tcx.symbol_name(*instance).name.to_string())
        .collect::<Vec<_>>();
    demanded_foreign_functions.sort();
    demanded_foreign_functions.dedup();
    let selected_fallbacks = selected_foreign_fallbacks(&records, &demanded_foreign_functions);
    let mut promote = Vec::new();
    if let Some(rows) = selected_fallbacks.as_array() {
        for row in rows {
            if row["status"] != "supported" { continue; }
            if !matches!(row["definition_kind"].as_str(), Some("function" | "associated_function")) { continue; }
            let symbol = row["symbol"].as_str().unwrap_or_default();
            if !demanded_foreign_functions.iter().any(|demanded| demanded == symbol) { continue; }
            let Some(id) = row["instance_id"].as_u64() else { continue; };
            if let Some((instance, _)) = context.instance_ids.iter().find(|(_, candidate_id)| **candidate_id == id) {
                promote.push(*instance);
            }
        }
    }
    promote.sort_by_key(|instance| context.instance_ids[instance]);
    promote.dedup();
    for instance in promote { context.register_instance(instance); }
    json!({
        "target":target_facts(tcx),
        "no_alloc_shim_symbol":compiler_fact(json!(no_alloc)),
        "exported_candidates":compiler_fact(json!(records)),
        "selected_foreign_fallbacks":compiler_fact(selected_fallbacks),
        "extern_statics":compiler_fact(json!({
            "declarations":declarations,
            "selected_exported":selected,
            "typing_env":"fully_monomorphized",
        })),
        "allocator_shims":allocator_shims(tcx),
    })
}
