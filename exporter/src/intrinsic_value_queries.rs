//! Source intrinsics.rs alloc_type_name and span_as_caller_location queries.
use super::*;
#[derive(serde::Serialize)]
pub(super) struct TypeName {
    #[serde(flatten)]
    value: pool_constant::Value,
    input_type: u64,
    result_type: u64,
    typing_env: &'static str,
}
#[derive(Clone, serde::Serialize)]
pub(super) struct CallerLocation {
    #[serde(flatten)]
    value: pool_constant::Value,
    span: u64,
    result_type: Option<u64>,
}
pub(super) fn discover_type_names<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut TypeNames<'tcx>,
) -> Result<(), String> {
    let mut requested = Vec::new();
    for instance in context.instance_events[state.events..].iter().copied() {
        if tcx.intrinsic(instance.def_id()).is_some()
            && tcx.item_name(instance.def_id()).as_str() == "type_name"
        {
            let input = instance.args.type_at(0);
            if state.completed.insert(input) { requested.push(input); }
        }
    }
    state.events = context.instance_events.len();
    let result_type = ty::Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.str_);
    let facts = requested
            .into_iter()
            .map(|input| {
                let value = if input.has_non_region_param()
                    || input.has_escaping_bound_vars()
                    || input.has_infer()
                    || input.has_placeholders()
                    || input.references_error()
                {
                    unavailable_compiler_fact("type_name requires monomorphic input")?
                } else {
                    let name = rustc_const_eval::util::type_name(tcx, input);
                    let bytes = name.into_bytes();
                    let meta = bytes.len() as u64;
                    let alloc_id = tcx.allocate_bytes_dedup(bytes, CTFE_ALLOC_SALT);
                    compiler_fact(const_value_json(
                        context,
                        tcx,
                        result_type,
                        rustc_middle::mir::ConstValue::Slice { alloc_id, meta },
                    )?)
                };
                Ok::<_, String>(TypeNameFact {
                    value,
                    input_type: type_json(context, tcx, input)?,
                    result_type: type_json(context, tcx, result_type)?,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
    state.facts.extend(facts);
    Ok(())
}
pub(super) fn collect_spans<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
) {
    let mut spans = vec![body.span, tcx.def_span(body.source.def_id())];
    for local in &body.local_decls {
        spans.push(local.source_info.span);
    }
    for scope in &body.source_scopes {
        spans.push(scope.span);
        if let Some((_, span)) = scope.inlined {
            spans.push(span);
        }
    }
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            spans.push(statement.source_info.span);
        }
        if let Some(term) = &block.terminator {
            spans.push(term.source_info.span);
            match &term.kind {
                rustc_middle::mir::TerminatorKind::Call { fn_span, .. }
                | rustc_middle::mir::TerminatorKind::TailCall { fn_span, .. } => {
                    spans.push(*fn_span)
                }
                _ => {}
            }
        }
    }
    for span in spans {
        if context.caller_location_span_set.insert(span) {
            context.caller_location_spans.push(span);
        }
    }
}
pub(super) fn discover_caller_locations<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<(), String> {
    // `span_as_caller_location` invokes a rustc hook rather than a memoized
    // query. Its provider allocates fresh CallerLocation memory on every
    // invocation, so revisiting already-seen spans in a closure round would
    // create unrelated compiler allocations. Cache by exact Span; distinct
    // spans remain distinct even when they map to identical source positions.
    if tcx
        .lang_items()
        .get(rustc_attr_ir::LangItem::PanicLocation)
        .is_none()
    {
        if context
            .instance_ids
            .keys()
            .any(|instance| instance.def.requires_caller_location(tcx))
        {
            return unavailable_compiler_fact("track_caller requires PanicLocation language item");
        }
        return Ok(());
    }
    let spans = context.caller_location_spans.clone();
    for span in spans.iter().copied() {
        if context.caller_location_constant_rows.contains_key(&span) {
            continue;
        }
        let value = if tcx
            .lang_items()
            .get(rustc_attr_ir::LangItem::PanicLocation)
            .is_some()
        {
            compiler_fact(const_value_json(
                context,
                tcx,
                tcx.caller_location_ty(),
                tcx.span_as_caller_location(span),
            )?)
        } else {
            unavailable_compiler_fact("caller location constant requires PanicLocation lang item")?
        };
        let span_id = span_json(context, tcx, span);
        let result_type = if tcx
            .lang_items()
            .get(rustc_attr_ir::LangItem::PanicLocation)
            .is_some()
        {
            Some(type_json(context, tcx, tcx.caller_location_ty())?)
        } else {
            None
        };
        context.caller_location_constant_rows.insert(
            span,
            CallerLocationFact {
                value,
                span: span_id,
                result_type,
            },
        );
    }
    Ok(())
}

pub(super) struct TypeNameFact {
    value: pool_constant::Value,
    input_type: u64,
    result_type: u64,
}
#[derive(Default)]
pub(super) struct TypeNames<'tcx> {
    events: usize,
    completed: HashSet<ty::Ty<'tcx>>,
    facts: Vec<TypeNameFact>,
}
pub(super) fn finish_type_names(mut state: TypeNames<'_>) -> Vec<TypeName> {
    state.facts.sort_by_key(|fact| fact.input_type);
    state.facts.into_iter().map(|fact| TypeName {
        value: fact.value,
        input_type: fact.input_type,
        result_type: fact.result_type,
        typing_env: "fully_monomorphized",
    }).collect()
}

#[derive(Clone)]
pub(super) struct CallerLocationFact {
    value: pool_constant::Value,
    span: u64,
    result_type: Option<u64>,
}
pub(super) fn finish_caller_locations(tcx: TyCtxt<'_>, context: &ExportContext<'_>) -> Vec<CallerLocation> {
    if tcx.lang_items().get(rustc_attr_ir::LangItem::PanicLocation).is_none() {
        return Vec::new();
    }
    // Preserve source span discovery order; distinct spans stay distinct even
    // when the compiler reports the same source location.
    context.caller_location_spans.iter().map(|span| {
        let fact = &context.caller_location_constant_rows[span];
        CallerLocation {
            value: fact.value.clone(),
            span: fact.span,
            result_type: fact.result_type,
        }
    }).collect()
}
