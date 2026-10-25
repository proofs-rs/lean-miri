//! Exact interpret/cast.rs compiler queries. Constructor requests are collected
//! from actual MIR casts; resolved instances enter the ordinary shared graph.
use super::*;
fn instance<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>,value:ty::Instance<'tcx>,source_cast:bool)->Value {
    if source_cast { context.fn_pointer_targets.insert(value); }
    let id=context.register_instance(value);
    json!({"instance_id":id,"instance_kind":instance_kind_json(context,tcx,value.def),"generic_args":generic_args_json(context,tcx,value.args)})
}
fn closed(input:ty::Ty<'_>)->bool {
    !input.has_non_region_param() && !input.has_escaping_bound_vars() && !input.has_infer() && !input.has_placeholders() && !input.references_error()
}
pub(super) fn export<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Value {
    let env=ty::TypingEnv::fully_monomorphized();
    let mut records=Vec::new();
    let mut types=context.type_ids.iter().filter(|(input,_)|matches!(input.kind(),ty::FnDef(..)|ty::Closure(..))).map(|(input,id)|(*id,*input)).collect::<Vec<_>>();
    types.sort_by_key(|(id,_)|*id);
    for (_,input) in types {
        let (kind,no_bound)=match input.kind(){
            ty::FnDef(_,args)=>("resolve_fn_ptr",args.no_bound_vars().is_some()),
            ty::Closure(..)=>("resolve_closure_fn_once",true),_=>unreachable!(),
        };
        let mut result=unavailable_compiler_fact("cast resolution requires normalized monomorphic input");
        if closed(input) {
            if let Ok(normal)=tcx.try_normalize_erasing_regions(env,ty::Unnormalized::new_wip(input)) {
                result=match *normal.kind(){
                    ty::FnDef(def,args)=>match args.no_bound_vars(){
                        Some(args)=>compiler_fact(ty::Instance::resolve_for_fn_ptr(tcx,env,def,args).map(|resolved|instance(tcx,context,resolved,context.fn_pointer_cast_inputs.contains(&input))).unwrap_or(Value::Null)),
                        None=>unavailable_compiler_fact("source FnDef args.no_bound_vars assertion failed"),
                    },
                    ty::Closure(def,args)=>compiler_fact(instance(tcx,context,ty::Instance::resolve_closure(tcx,def,args,ty::ClosureKind::FnOnce),context.fn_pointer_cast_inputs.contains(&input))),
                    _=>unavailable_compiler_fact("normalization changed function/closure query kind"),
                };
            }
        }
        result["query_kind"]=json!(kind);result["typing_env"]=json!("fully_monomorphized");
        result["input_type"]=type_json(context,tcx,input);result["args_no_bound_vars"]=json!(no_bound);
        records.push(result);
    }
    let mut pairs=context.cast_unsize_requests.iter().copied().collect::<Vec<_>>();
    pairs.sort_by_key(|(source,target)|(context.type_id(*source),context.type_id(*target)));
    for (source,target) in pairs {
        let mut result=unavailable_compiler_fact("lockstep tails require normalized monomorphic source and target");
        if closed(source) && closed(target) {
            let (a,b)=tcx.struct_lockstep_tails_for_codegen(source,target,env);
            result=compiler_fact(json!({"source_tail":type_json(context,tcx,a),"target_tail":type_json(context,tcx,b)}));
            if matches!(a.kind(),ty::Dynamic(..)) && matches!(b.kind(),ty::Dynamic(..)) {
                let slot=tcx.supertrait_vtable_slot((a,b));
                records.push(json!({"query_kind":"supertrait_slot","typing_env":"fully_monomorphized","input_source":type_json(context,tcx,a),"input_target":type_json(context,tcx,b),"status":"supported","value":slot}));
            }
        }
        result["query_kind"]=json!("lockstep_tails");result["typing_env"]=json!("fully_monomorphized");
        result["input_source"]=type_json(context,tcx,source);result["input_target"]=type_json(context,tcx,target);records.push(result);
    }
    let mut boxes=context.cast_box_requests.iter().copied().collect::<Vec<_>>();
    boxes.sort_by_key(|input|context.type_id(*input));
    for input in boxes {
        let mut result=if tcx.lang_items().owned_box().is_some(){compiler_fact(type_json(context,tcx,ty::Ty::new_box(tcx,input)))}else{unavailable_compiler_fact("Box constructor requires owned_box lang item")};
        result["query_kind"]=json!("box_type");result["typing_env"]=json!("fully_monomorphized");result["input_type"]=type_json(context,tcx,input);records.push(result);
    }
    Value::Array(records)
}
