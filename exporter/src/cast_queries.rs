//! Exact interpret/cast.rs compiler queries. Constructor requests are collected
//! from actual MIR casts; resolved instances enter the ordinary shared graph.
use super::*;
#[derive(serde::Serialize)]
#[serde(untagged)]
pub(super) enum Query {
    ResolveFnPtr {
        query_kind: QueryKind,
        typing_env: &'static str,
        input_type: u64,
        args_no_bound_vars: bool,
        #[serde(flatten)]
        resolution: OptionalInstance,
    },
    ResolveClosureFnOnce {
        query_kind: QueryKind,
        typing_env: &'static str,
        input_type: u64,
        args_no_bound_vars: bool,
        instance_id: u64,
    },
    SupertraitSlot {
        query_kind: QueryKind,
        typing_env: &'static str,
        input_source: u64,
        input_target: u64,
        value: Option<usize>,
    },
    LockstepTails {
        query_kind: QueryKind,
        typing_env: &'static str,
        input_source: u64,
        input_target: u64,
        source_tail: u64,
        target_tail: u64,
    },
    BoxType {
        query_kind: QueryKind,
        typing_env: &'static str,
        input_type: u64,
        #[serde(rename = "type")]
        ty: u64,
    },
}
#[derive(Clone, Copy, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum QueryKind {
    ResolveFnPtr,
    ResolveClosureFnOnce,
    SupertraitSlot,
    LockstepTails,
    BoxType,
}
#[derive(serde::Serialize)]
#[serde(tag = "resolution_kind", rename_all = "snake_case")]
pub(super) enum OptionalInstance {
    Instance { instance_id: u64 },
    None,
}
fn instance<'tcx>(
    context: &mut ExportContext<'tcx>,
    value: ty::Instance<'tcx>,
    source_cast: bool,
) -> u64 {
    if source_cast {
        context.fn_pointer_targets.insert(value);
    }
    context.register_instance(value)
}
fn closed(input: ty::Ty<'_>) -> bool {
    !input.has_non_region_param()
        && !input.has_escaping_bound_vars()
        && !input.has_infer()
        && !input.has_placeholders()
        && !input.references_error()
}
pub(super) fn export<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Vec<Query>, String> {
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
            ty::FnDef(_, args) => (QueryKind::ResolveFnPtr, args.no_bound_vars().is_some()),
            ty::Closure(..) => (QueryKind::ResolveClosureFnOnce, true),
            _ => unreachable!(),
        };
        if !closed(input) {
            export_failure::<()>("cast resolution", "requires normalized monomorphic input")?;
        }
        let normal = tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(input))
            .map_err(|error| format!("cast input normalization failed: {error:?}"))?;
        let typing_env = "fully_monomorphized";
        let result = match *normal.kind() {
            ty::FnDef(def, args) => {
                let args = match args.no_bound_vars() {
                    Some(args) => args,
                    None => {
                        return unavailable_compiler_fact(
                            "source FnDef args.no_bound_vars assertion failed",
                        );
                    }
                };
                let _ = ty::Instance::try_resolve(tcx, env, def, args)
                    .map_err(|error| format!("function-pointer resolution failed: {error:?}"))?;
                let source_cast = context.fn_pointer_cast_inputs.contains(&input);
                let resolution = match ty::Instance::resolve_for_fn_ptr(tcx, env, def, args) {
                    Some(resolved) => OptionalInstance::Instance {
                        instance_id: instance(context, resolved, source_cast),
                    },
                    None => OptionalInstance::None,
                };
                Query::ResolveFnPtr {
                    query_kind: kind,
                    typing_env,
                    input_type: type_json(context, tcx, input)?,
                    args_no_bound_vars: no_bound,
                    resolution,
                }
            }
            ty::Closure(def, args) => {
                let source_cast = context.fn_pointer_cast_inputs.contains(&input);
                let instance_id = instance(
                    context,
                    ty::Instance::resolve_closure(tcx, def, args, ty::ClosureKind::FnOnce),
                    source_cast,
                );
                Query::ResolveClosureFnOnce {
                    query_kind: kind,
                    typing_env,
                    input_type: type_json(context, tcx, input)?,
                    args_no_bound_vars: no_bound,
                    instance_id,
                }
            }
            _ => {
                return export_failure(
                    "cast resolution",
                    "normalization changed function/closure query kind",
                );
            }
        };
        records.push(result);
    }
    let pairs = context
        .cast_unsize_requests
        .iter()
        .copied()
        .collect::<Vec<_>>();
    for (source, target) in pairs {
        if !closed(source) || !closed(target) {
            export_failure::<()>("lockstep tails", "requires monomorphic source and target")?;
        }
        let (a, b) = tcx.struct_lockstep_tails_for_codegen(source, target, env);
        let source_tail = type_json(context, tcx, a)?;
        let target_tail = type_json(context, tcx, b)?;
        if matches!(a.kind(), ty::Dynamic(..)) && matches!(b.kind(), ty::Dynamic(..)) {
            records.push(Query::SupertraitSlot {
                query_kind: QueryKind::SupertraitSlot,
                typing_env: "fully_monomorphized",
                input_source: type_json(context, tcx, a)?,
                input_target: type_json(context, tcx, b)?,
                value: tcx.supertrait_vtable_slot((a, b)),
            });
        }
        records.push(Query::LockstepTails {
            query_kind: QueryKind::LockstepTails,
            typing_env: "fully_monomorphized",
            input_source: type_json(context, tcx, source)?,
            input_target: type_json(context, tcx, target)?,
            source_tail,
            target_tail,
        });
    }
    let boxes = context
        .cast_box_requests
        .iter()
        .copied()
        .collect::<Vec<_>>();
    for input in boxes {
        let ty = if tcx.lang_items().owned_box().is_some() {
            type_json(context, tcx, ty::Ty::new_box(tcx, input))?
        } else {
            return export_failure(
                "cast box type",
                "Box constructor requires owned_box lang item",
            );
        };
        records.push(Query::BoxType {
            query_kind: QueryKind::BoxType,
            typing_env: "fully_monomorphized",
            input_type: type_json(context, tcx, input)?,
            ty,
        });
    }
    Ok(records)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn optional_instance_survives_query_key_fields() {
        for resolution in [
            OptionalInstance::None,
            OptionalInstance::Instance { instance_id: 7 },
        ] {
            let record = serde_json::to_value(Query::ResolveFnPtr {
                query_kind: QueryKind::ResolveFnPtr,
                typing_env: "fully_monomorphized",
                input_type: 3,
                args_no_bound_vars: true,
                resolution,
            })
            .unwrap();
            assert!(record.get("value").is_none());
            assert_eq!(record["query_kind"], "resolve_fn_ptr");
            if record["resolution_kind"] == "instance" {
                assert_eq!(record["instance_id"], 7);
            } else {
                assert_eq!(record["resolution_kind"], "none");
                assert!(record.get("instance_id").is_none());
            }
        }
    }
}
