//! Exact interpret/cast.rs compiler queries. Constructor requests are collected
//! from actual MIR casts; resolved instances enter the ordinary shared graph.
use super::*;
fn optional_instance(value: Option<Value>) -> Value {
    // This tag preserves the genuine optional answer when query keys are
    // attached. Instance identities, when present, remain ordinary Nat refs.
    match value {
        Some(mut instance) => {
            instance["resolution_kind"] = json!("instance");
            instance
        }
        None => json!({"resolution_kind": "none"}),
    }
}
fn instance<'tcx>(
    _tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    value: ty::Instance<'tcx>,
    source_cast: bool,
) -> Result<Value, String> {
    if source_cast {
        context.fn_pointer_targets.insert(value);
    }
    let id = context.register_instance(value);
    Ok::<_, String>(
        json!({"instance_id":id}),
    )
}
fn closed(input:ty::Ty<'_>)->bool {
    !input.has_non_region_param() && !input.has_escaping_bound_vars() && !input.has_infer() && !input.has_placeholders() && !input.references_error()
}
pub(super) fn export<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Value, String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut records = Vec::new();
    let mut types = context
        .type_ids
        .iter()
        .filter(|(input, _)| {
            matches!(input.kind(), ty::FnDef(..) | ty::Closure(..))
                && (closed(**input) || context.fn_pointer_cast_inputs.contains(input))
        })
        .map(|(input, id)| (*id, *input))
        .collect::<Vec<_>>();
    types.sort_by_key(|(id, _)| *id);
    for (_, input) in types {
        let (kind, no_bound) = match input.kind() {
            ty::FnDef(_, args) => ("resolve_fn_ptr", args.no_bound_vars().is_some()),
            ty::Closure(..) => ("resolve_closure_fn_once", true),
            _ => unreachable!(),
        };
        if !closed(input) {
            export_failure::<()>("cast resolution", "requires normalized monomorphic input")?;
        }
        let normal = tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(input))
            .map_err(|error| format!("cast input normalization failed: {error:?}"))?;
        let mut result = match *normal.kind() {
            ty::FnDef(def, args) => match args.no_bound_vars() {
                Some(args) => {
                    // resolve_for_fn_ptr internally collapses try_resolve's
                    // Err into None. Preserve a genuine Ok(None), which the
                    // interpreter maps to TooGeneric, but abort query errors.
                    let _ = ty::Instance::try_resolve(tcx, env, def, args).map_err(|error| {
                        format!("function-pointer resolution failed: {error:?}")
                    })?;
                    compiler_fact(optional_instance(
                        ty::Instance::resolve_for_fn_ptr(tcx, env, def, args)
                            .map(|resolved| {
                                instance(
                                    tcx,
                                    context,
                                    resolved,
                                    context.fn_pointer_cast_inputs.contains(&input),
                                )
                            })
                            .transpose()?,
                    ))
                }
                None => {
                    unavailable_compiler_fact("source FnDef args.no_bound_vars assertion failed")?
                }
            },
            ty::Closure(def, args) => compiler_fact(instance(
                tcx,
                context,
                ty::Instance::resolve_closure(tcx, def, args, ty::ClosureKind::FnOnce),
                context.fn_pointer_cast_inputs.contains(&input),
            )?),
            _ => unavailable_compiler_fact("normalization changed function/closure query kind")?,
        };
        result["query_kind"] = json!(kind);
        result["typing_env"] = json!("fully_monomorphized");
        result["input_type"] = type_json(context, tcx, input)?;
        result["args_no_bound_vars"] = json!(no_bound);
        records.push(result);
    }
    let mut pairs = context
        .cast_unsize_requests
        .iter()
        .copied()
        .collect::<Vec<_>>();
    pairs.sort_by_key(|(source, target)| (context.type_id(*source), context.type_id(*target)));
    for (source, target) in pairs {
        if !closed(source) || !closed(target) {
            export_failure::<()>("lockstep tails", "requires monomorphic source and target")?;
        }
        let (a, b) = tcx.struct_lockstep_tails_for_codegen(source, target, env);
        let mut result = compiler_fact(
            json!({"source_tail":type_json(context,tcx,a)?,"target_tail":type_json(context,tcx,b)?}),
        );
        if matches!(a.kind(), ty::Dynamic(..)) && matches!(b.kind(), ty::Dynamic(..)) {
            let slot = tcx.supertrait_vtable_slot((a, b));
            records.push(json!({"query_kind":"supertrait_slot","typing_env":"fully_monomorphized","input_source":type_json(context,tcx,a)?,"input_target":type_json(context,tcx,b)?,"value":slot}));
        }
        result["query_kind"] = json!("lockstep_tails");
        result["typing_env"] = json!("fully_monomorphized");
        result["input_source"] = type_json(context, tcx, source)?;
        result["input_target"] = type_json(context, tcx, target)?;
        records.push(result);
    }
    let mut boxes = context
        .cast_box_requests
        .iter()
        .copied()
        .collect::<Vec<_>>();
    boxes.sort_by_key(|input| context.type_id(*input));
    for input in boxes {
        let mut result = if tcx.lang_items().owned_box().is_some() {
            json!({"type": type_json(context, tcx, ty::Ty::new_box(tcx, input))?})
        } else {
            unavailable_compiler_fact("Box constructor requires owned_box lang item")?
        };
        result["query_kind"] = json!("box_type");
        result["typing_env"] = json!("fully_monomorphized");
        result["input_type"] = type_json(context, tcx, input)?;
        records.push(result);
    }
    Ok::<_, String>(Value::Array(records))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn optional_instance_survives_query_key_fields() {
        for input in [None, Some(json!({"instance_id": 7}))] {
            let mut record = optional_instance(input.clone());
            record["query_kind"] = json!("resolve_fn_ptr");
            record["typing_env"] = json!("fully_monomorphized");
            record["input_type"] = json!(3);
            assert!(record.get("value").is_none());
            if let Some(instance) = input {
                assert_eq!(record["resolution_kind"], "instance");
                assert_eq!(record["instance_id"], instance["instance_id"]);
            } else {
                assert_eq!(record["resolution_kind"], "none");
                assert!(record.get("instance_id").is_none());
            }
        }
    }
}
