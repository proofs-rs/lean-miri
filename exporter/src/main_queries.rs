//! eval.rs::call_main compiler queries. This module is wired before reachable
//! instance traversal so lang_start and its actual MIR enter the same graph.
use super::*;
use rustc_hir::def_id::DefId;
use rustc_session::config::EntryFnType;
fn entry<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>,def:DefId)->Value {
    let args=ty::GenericArgs::identity_for_item(tcx,def);
    let parameters=args.iter().map(|arg| match arg.kind(){
        ty::GenericArgKind::Lifetime(_)=>"lifetime",
        ty::GenericArgKind::Type(_)=>"type_parameter",
        ty::GenericArgKind::Const(_)=>"const_parameter",
    }).collect::<Vec<_>>();
    let signature=if args.has_non_region_param(){
        unavailable_compiler_fact("source Instance::mono entry rejects type/const parameters")
    }else{
        let instance=ty::Instance::mono(tcx,def);
        let signature=instance.ty(tcx,ty::TypingEnv::fully_monomorphized()).fn_sig(tcx);
        let result=signature.skip_binder().output();
        let fn_pointer=ty::Ty::new_fn_ptr(tcx,signature);
        let selected_entry=tcx.entry_fn(()).map(|(entry,_)|entry)==Some(def);
        let start=if !selected_entry {
            Value::Null // Explicitly absent: no source lang_start request for this entry.
        }else if let Some(start)=tcx.lang_items().start_fn(){
            let args=tcx.mk_args(&[result.into()]);
            if result.has_escaping_bound_vars(){
                unavailable_compiler_fact("source main return type retains bound variables")
            }else{match ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),start,args){
                Ok(Some(instance))=>{
                    let id=context.register_instance(instance);
                    // eval.rs::call_main passes a function pointer, argc,
                    // argv, and sigpipe to this exact monomorphized start
                    // function through helpers.rs::call_function. Preserve
                    // its FnDef type in the compiler function-fact domain so
                    // compiler_function_facts_json can emit the matching
                    // dummy-caller signature ABI query. Registering only the
                    // Instance omits this source function type from that
                    // catalog, leaving call_main's exact FnAbi request
                    // unsupported even though rustc can answer it.
                    let function_type=instance.ty(tcx,ty::TypingEnv::fully_monomorphized());
                    let function_type=type_json(context,tcx,function_type);
                    json!({"status":"supported","value":{"instance_id":id,
                        "function_type":function_type,
                        "instance_kind":instance_kind_json(context,tcx,instance.def),
                        "generic_args":generic_args_json(context,tcx,instance.args)}})
                }
                Ok(None)=>compiler_fact(Value::Null),
                Err(error)=>json!({"status":"unsupported","reason":"lang_start instance resolution failed","error_debug":format!("{error:?}")}),
            }}
        }else{compiler_fact(Value::Null)};
        compiler_fact(json!({"compiler_selected_entry":selected_entry,"has_bound_variables":!signature.bound_vars().is_empty(),
            "output_has_bound_variables":result.has_escaping_bound_vars(),
            "return_type":type_json(context,tcx,result),"function_pointer_type":type_json(context,tcx,fn_pointer),
            "start_resolution":start}))
    };
    json!({"definition":def_json(def),"generic_parameters":parameters,"signature_query":signature})
}
pub(super) fn export<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>,roots:&[DefId])->Value {
    // eval.rs::call_main constructs `FnVal::Instance(entry_instance)` before
    // invoking lang_start. That conversion asks Miri's compiler interface for
    // the entry Instance's function-pointer allocation even though no MIR
    // contains a ReifyFnPointer cast for it. Include the exact selected entry
    // in the same prepared raw-world key domain as explicit function-pointer
    // demands. Instance::mono is the source entry construction used by the
    // pinned startup path and preserves rustc's actual entry identity.
    if let Some((definition, _)) = tcx.entry_fn(()) {
        let instance = ty::Instance::mono(tcx, definition);
        context.register_instance(instance);
        context.fn_pointer_targets.insert(instance);
    }
    let entries=roots.iter().filter(|def|matches!(tcx.def_kind(**def),rustc_hir::def::DefKind::Fn|rustc_hir::def::DefKind::AssocFn))
        .map(|def|entry(tcx,context,*def)).collect::<Vec<_>>();
    let compiler_entry_type=tcx.entry_fn(()).map(|(definition,entry_type)|match entry_type{
        EntryFnType::Main{sigpipe}=>json!({"definition":def_json(definition),"kind":"rustc_main","sigpipe":sigpipe}),
    });
    json!({"typing_env":"fully_monomorphized","start_lang_item":tcx.lang_items().start_fn().map(def_json),
        "compiler_entry":tcx.entry_fn(()).map(|(entry,_)|def_json(entry)),
        "compiler_entry_type":compiler_fact(compiler_entry_type.unwrap_or(Value::Null)),"entries":entries,
        "link_sections":link_sections(tcx,context)})
}

// helpers.rs::iter_exported_symbols and lookup_link_section. Keep exact source
// traversal order and used bits; static initializer effects execute later in
// actual global memory, not during a diagnostic-name lookup.
fn link_sections<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Value {
    use rustc_hir::def_id::LOCAL_CRATE;
    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags as F;
    use rustc_middle::middle::dependency_format::Linkage;
    use rustc_middle::middle::exported_symbols::ExportedSymbol;
    let mut symbols=Vec::new();
    for def in tcx.hir_crate_items(()).definitions(){
        if !tcx.def_kind(def).has_codegen_attrs() || tcx.is_foreign_item(def){continue}
        let attrs=tcx.codegen_fn_attrs(def);
        let used=attrs.flags.contains(F::USED_COMPILER)||attrs.flags.contains(F::USED_LINKER);
        if used||attrs.contains_extern_indicator(){symbols.push((def.to_def_id(),used));}
    }
    let formats=tcx.dependency_formats(());
    let complete=if let Some(format)=formats.get(&rustc_structures::CrateType::Executable){
        for (krate,linkage) in format.iter_enumerated(){
            if krate==LOCAL_CRATE || *linkage==Linkage::NotLinked{continue}
            for &(symbol,info) in tcx.exported_non_generic_symbols(krate){
                if let ExportedSymbol::NonGeneric(def)=symbol {
                    if !tcx.is_foreign_item(def){symbols.push((def,info.used));}
                }
            }
        }
        true
    }else{false};
    let mut entries=Vec::new();
    for (def,used) in symbols {
        if !used{continue}
        let Some(section)=tcx.codegen_fn_attrs(def).link_section else{continue};
        let query=if tcx.is_static(def){
            let instance=ty::Instance::mono(tcx,def);
            let ty=instance.ty(tcx,ty::TypingEnv::fully_monomorphized());
            compiler_fact(json!({"type":type_json(context,tcx,ty),
                "allocation":allocation_ref(context,tcx,tcx.reserve_and_set_static_alloc(def))}))
        }else{unavailable_compiler_fact("source link-section eval_global requires a function-pointer or function-pointer-array static")};
        entries.push(json!({"section":section.as_str(),"definition":def_json(def),"span":span_json(context,tcx,tcx.def_span(def)),"global_query":query}));
    }
    if complete {compiler_fact(json!(entries))}
    else{json!({"status":"unsupported","reason":"source exported-symbol traversal requires executable dependency_formats","local_evidence":entries})}
}
