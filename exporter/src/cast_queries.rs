//! Exact interpret/cast.rs compiler queries. Constructor requests are collected
//! from actual MIR casts; resolved instances enter the ordinary shared graph.
use super::*;
#[derive(Clone, serde::Serialize)]
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
#[derive(Clone, serde::Serialize)]
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
// Compiler answers retained without constructing the public query rows.
pub(super) enum Fact {
    ResolveFnPtr { input_type: u64, args_no_bound_vars: bool, resolution: Option<u64> },
    ResolveClosureFnOnce { input_type: u64, args_no_bound_vars: bool, instance_id: u64 },
    SupertraitSlot { input_source: u64, input_target: u64, value: Option<usize> },
    LockstepTails { input_source: u64, input_target: u64, source_tail: u64, target_tail: u64 },
    BoxType { input_type: u64, ty: u64 },
}
pub(super) fn finish(facts: Vec<Fact>) -> Vec<Query> {
    facts.into_iter().map(|fact| match fact {
        Fact::ResolveFnPtr { input_type, args_no_bound_vars, resolution } => Query::ResolveFnPtr {
            query_kind: QueryKind::ResolveFnPtr, typing_env: "fully_monomorphized",
            input_type, args_no_bound_vars,
            resolution: match resolution {
                Some(instance_id) => OptionalInstance::Instance { instance_id },
                None => OptionalInstance::None,
            },
        },
        Fact::ResolveClosureFnOnce { input_type, args_no_bound_vars, instance_id } => Query::ResolveClosureFnOnce {
            query_kind: QueryKind::ResolveClosureFnOnce, typing_env: "fully_monomorphized",
            input_type, args_no_bound_vars, instance_id,
        },
        Fact::SupertraitSlot { input_source, input_target, value } => Query::SupertraitSlot {
            query_kind: QueryKind::SupertraitSlot, typing_env: "fully_monomorphized", input_source, input_target, value,
        },
        Fact::LockstepTails { input_source, input_target, source_tail, target_tail } => Query::LockstepTails {
            query_kind: QueryKind::LockstepTails, typing_env: "fully_monomorphized", input_source, input_target, source_tail, target_tail,
        },
        Fact::BoxType { input_type, ty } => Query::BoxType {
            query_kind: QueryKind::BoxType, typing_env: "fully_monomorphized", input_type, ty,
        },
    }).collect()
}
pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<(), String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut state = std::mem::take(&mut context.cast_state);
    let mut records = Vec::new();
    // These are actual MIR ReifyFnPointer/ClosureFnPointer requests, not the
    // universe of retained FnDef headers. A late request is processed even when
    // its type belonged to a prefix scanned in an earlier discovery wave.
    let cast_end = context.fn_pointer_cast_inputs.len();
    let inputs = (state.inputs..cast_end)
        .map(|index| *context.fn_pointer_cast_inputs.get_index(index).unwrap())
        .collect::<Vec<_>>();
    for input in inputs {
        let no_bound = match input.kind() {
            ty::FnDef(_, args) => args.no_bound_vars().is_some(),
            ty::Closure(..) => true,
            _ => return export_failure("cast resolution", "actual request is not a function or closure"),
        };
        if !closed(input) {
            export_failure::<()>("cast resolution", "requires normalized monomorphic input")?;
        }
        let normal = tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(input))
            .map_err(|error| format!("cast input normalization failed: {error:?}"))?;
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
                let preliminary = ty::Instance::try_resolve(tcx, env, def, args)
                    .map_err(|error| format!("function-pointer resolution failed: {error:?}"))?;
                // Pinned instance.rs::resolve_for_fn_ptr's KCFI fallback asks
                // is_dyn_compatible(assoc.container_id), but assoc.rs defines
                // container_id of a TraitImpl member as its impl, not its trait.
                // That compiler query panics. Preserve an explicit residual for
                // actual requests that reach that branch, rather than invoking
                // it or fabricating a successful/negative resolution.
                if tcx.sess.is_sanitizer_kcfi_enabled()
                    && tcx.opt_associated_item(def).is_some_and(|item|
                        matches!(item.container, ty::AssocContainer::TraitImpl(Ok(_))))
                    && preliminary.is_some_and(|resolved| {
                        !matches!(resolved.def, ty::InstanceKind::Item(_)
                            if resolved.def.requires_caller_location(tcx))
                        && !matches!(resolved.def, ty::InstanceKind::Virtual(..))
                        && !tcx.is_closure_like(resolved.def_id())
                    })
                {
                    return export_failure("function-pointer resolution",
                        "pinned KCFI trait-impl function-pointer fallback queries dyn compatibility of an impl");
                }
                let source_cast = true;
                let resolution = match ty::Instance::resolve_for_fn_ptr(tcx, env, def, args) {
                    Some(resolved) => {
                        state.resolutions.insert(input, resolved);
                        Some(instance(context, resolved, source_cast))
                    },
                    None => None,
                };
                Fact::ResolveFnPtr {
                    input_type: type_json(context, tcx, input)?,
                    args_no_bound_vars: no_bound,
                    resolution,
                }
            }
            ty::Closure(def, args) => {
                let source_cast = true;
                let resolved = ty::Instance::resolve_closure(tcx, def, args, ty::ClosureKind::FnOnce);
                state.resolutions.insert(input, resolved);
                let instance_id = instance(context, resolved, source_cast);
                Fact::ResolveClosureFnOnce {
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
    state.inputs = cast_end;
    let pairs = context.cast_unsize_requests.suffix(state.pairs).to_vec();
    state.pairs = context.cast_unsize_requests.len();
    for (source, target) in pairs {
        if !closed(source) || !closed(target) {
            export_failure::<()>("lockstep tails", "requires monomorphic source and target")?;
        }
        let (a, b) = tcx.struct_lockstep_tails_for_codegen(source, target, env);
        let source_tail = type_json(context, tcx, a)?;
        let target_tail = type_json(context, tcx, b)?;
        if matches!(a.kind(), ty::Dynamic(..)) && matches!(b.kind(), ty::Dynamic(..)) {
            records.push(Fact::SupertraitSlot {
                input_source: type_json(context, tcx, a)?,
                input_target: type_json(context, tcx, b)?,
                value: tcx.supertrait_vtable_slot((a, b)),
            });
        }
        records.push(Fact::LockstepTails {
            input_source: type_json(context, tcx, source)?,
            input_target: type_json(context, tcx, target)?,
            source_tail,
            target_tail,
        });
    }
    let boxes = context.cast_box_requests.suffix(state.boxes).to_vec();
    state.boxes = context.cast_box_requests.len();
    for input in boxes {
        let ty = if tcx.lang_items().owned_box().is_some() {
            type_json(context, tcx, ty::Ty::new_box(tcx, input))?
        } else {
            return export_failure(
                "cast box type",
                "Box constructor requires owned_box lang item",
            );
        };
        records.push(Fact::BoxType {
            input_type: type_json(context, tcx, input)?,
            ty,
        });
    }
    state.rows.extend(records);
    context.cast_state = state;
    Ok(())
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
