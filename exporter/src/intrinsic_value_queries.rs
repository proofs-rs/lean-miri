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
// CallerLocation source values are templates, not guest pointers. The runtime
// creates a fresh root at each intrinsic invocation. Keep one exact compiler
// template per filename and parameterize only the two u32 fields written by
// rustc_const_eval::util::caller_location::alloc_caller_location.
fn caller_location_recipe<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>,
    span: rustc_span::Span) -> Value {
    let topmost = span.ctxt().outer_expn().expansion_cause().unwrap_or(span);
    let position = tcx.sess.source_map().lookup_char_pos(topmost.lo());
    let filename = position.file.name
        .display(rustc_span::RemapPathScopeComponents::MACRO).to_string_lossy().into_owned();
    let template = match context.caller_location_templates.get(&filename) {
        Some(value) => value.clone(),
        None => {
            let value = tcx.const_caller_location(rustc_span::Symbol::intern(&filename), 0, 0);
            let value = const_value_json(context, tcx, tcx.caller_location_ty(), value);
            context.caller_location_templates.insert(filename, value.clone());
            value
        }
    };
    let details = tcx.sess.opts.unstable_opts.location_detail;
    // Match span_as_caller_location casts and the provider's redaction policy.
    let line = if details.line { position.line as u32 } else { 0 };
    let column = if details.column { position.col_display as u32 + 1 } else { 0 };
    json!({"status":"supported", "recipe_schema":"caller_location_template_v1",
        "template_value":template, "line_u32":line, "column_u32":column})
}

pub(super) fn caller_locations<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Value {
    let spans=context.caller_location_spans.clone();
    for span in spans.iter().copied() {
        if context.caller_location_constant_rows.contains_key(&span) { continue; }
        let mut result=if tcx.lang_items().get(rustc_attr_ir::LangItem::PanicLocation).is_none(){
            unavailable_compiler_fact("caller location constant requires PanicLocation lang item")
        } else if cfg!(feature="full-caller-locations") {
            compiler_fact(const_value_json(context,tcx,tcx.caller_location_ty(),tcx.span_as_caller_location(span)))
        } else {
            caller_location_recipe(tcx,context,span)
        };
        result["span"]=span_json(context,tcx,span);
        result["result_type"]=if tcx.lang_items().get(rustc_attr_ir::LangItem::PanicLocation).is_some(){type_json(context,tcx,tcx.caller_location_ty())}else{Value::Null};
        context.caller_location_constant_rows.insert(span,result);
    }
    Value::Array(spans.iter().map(|span|context.caller_location_constant_rows[span].clone()).collect())
}
