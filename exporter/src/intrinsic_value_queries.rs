//! Source intrinsics.rs alloc_type_name and span_as_caller_location queries.
use super::*;
pub(super) fn type_names<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Value {
    let mut requested=context.instance_ids.keys().filter_map(|instance|{
        (tcx.intrinsic(instance.def_id()).is_some() && tcx.item_name(instance.def_id()).as_str()=="type_name")
            .then(||instance.args.type_at(0))
    }).collect::<Vec<_>>();
    requested.sort_by_key(|ty|context.type_id(*ty));requested.dedup();
    let result_type=ty::Ty::new_imm_ref(tcx,tcx.lifetimes.re_erased,tcx.types.str_);
    Value::Array(requested.into_iter().map(|input|{
        let mut result=if input.has_non_region_param() || input.has_escaping_bound_vars() || input.has_infer() || input.has_placeholders() || input.references_error(){
            unavailable_compiler_fact("type_name requires monomorphic input")
        }else{
            let name=rustc_const_eval::util::type_name(tcx,input);
            let bytes=name.into_bytes();let meta=bytes.len() as u64;
            let alloc_id=tcx.allocate_bytes_dedup(bytes,CTFE_ALLOC_SALT);
            compiler_fact(const_value_json(context,tcx,result_type,rustc_middle::mir::ConstValue::Slice{alloc_id,meta}))
        };
        result["input_type"]=type_json(context,tcx,input);result["result_type"]=type_json(context,tcx,result_type);
        result["typing_env"]=json!("fully_monomorphized");result
    }).collect())
}
pub(super) fn collect_spans<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>,body:&rustc_middle::mir::Body<'tcx>) {
    let mut spans=vec![body.span,tcx.def_span(body.source.def_id())];
    for local in &body.local_decls{spans.push(local.source_info.span);}
    for scope in &body.source_scopes{
        spans.push(scope.span);if let Some((_,span))=scope.inlined{spans.push(span);}
    }
    for block in body.basic_blocks.iter(){
        for statement in &block.statements{spans.push(statement.source_info.span);}
        if let Some(term)=&block.terminator{
            spans.push(term.source_info.span);
            match &term.kind{rustc_middle::mir::TerminatorKind::Call{fn_span,..}|rustc_middle::mir::TerminatorKind::TailCall{fn_span,..}=>spans.push(*fn_span),_=>{}}
        }
    }
    for span in spans {if context.caller_location_span_set.insert(span){context.caller_location_spans.push(span);}}
}
pub(super) fn caller_locations<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Value {
    // `span_as_caller_location` invokes a rustc hook rather than a memoized
    // query. Its provider allocates fresh CallerLocation memory on every
    // invocation, so revisiting already-seen spans in a closure round would
    // create unrelated compiler allocations. Cache by exact Span; distinct
    // spans remain distinct even when they map to identical source positions.
    let spans=context.caller_location_spans.clone();
    for span in spans.iter().copied() {
        if context.caller_location_constant_rows.contains_key(&span) { continue; }
        let mut result=if tcx.lang_items().get(rustc_attr_ir::LangItem::PanicLocation).is_some(){
            compiler_fact(const_value_json(context,tcx,tcx.caller_location_ty(),tcx.span_as_caller_location(span)))
        }else{unavailable_compiler_fact("caller location constant requires PanicLocation lang item")};
        result["span"]=span_json(context,tcx,span);
        result["result_type"]=if tcx.lang_items().get(rustc_attr_ir::LangItem::PanicLocation).is_some(){type_json(context,tcx,tcx.caller_location_ty())}else{Value::Null};
        context.caller_location_constant_rows.insert(span,result);
    }
    // Preserve source span discovery order on every returned catalog snapshot.
    Value::Array(spans.iter().map(|span|context.caller_location_constant_rows[span].clone()).collect())
}
