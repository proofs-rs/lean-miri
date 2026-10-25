//! Exact TyAbiInterface::{ty_and_layout_field,ty_and_layout_for_variant}
//! in rustc_middle/ty/layout.rs. Preserve query layouts, not layout-equivalent
//! type guesses; coroutine tags and uninhabited variants need these layouts.
use super::*;
fn parent<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>,
    cx:&ty::layout::LayoutCx<'tcx>,layout:rustc_abi::TyAndLayout<'tcx,ty::Ty<'tcx>>,
    variant:Option<usize>)->Value {
    // `TyAndLayout::field` has a source-defined `str` special case that
    // returns `u8` even though `str`'s layout has zero ordinary fields. Keep
    // that exact query result available to the importer without inventing a
    // field count or enumerating a synthetic array.
    let query_count=if matches!(layout.ty.kind(),ty::Str){1}else{layout.fields.count()};
    let fields=(0..query_count).map(|index|{
        let field=layout.field(cx,index);
        json!({"index":index,"type":type_json(context,tcx,field.ty),"layout":layout_value_json(context,tcx,field)})
    }).collect::<Vec<_>>();
    json!({"variant":variant,"layout":layout_value_json(context,tcx,layout),"fields":fields})
}
pub(super) fn export<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>,input:ty::Ty<'tcx>)->Value {
    if !matches!(input.kind(),ty::Closure(..)|ty::CoroutineClosure(..)|ty::Coroutine(..)|ty::RawPtr(..)|ty::Ref(..)|ty::Adt(..)|ty::Pat(..)|ty::Str) {
        return compiler_fact(Value::Null);
    }
    if input.has_non_region_param() || input.has_escaping_bound_vars() || input.has_infer() || input.has_placeholders(){
        return unavailable_compiler_fact("projection queries require a complete monomorphic parent type");
    }
    let env=ty::TypingEnv::fully_monomorphized();
    let layout=match tcx.layout_of(env.as_query_input(input)){
        Ok(layout)=>layout,
        Err(error)=>return json!({"status":"unsupported","reason":"projection parent layout unavailable","error_debug":format!("{error:?}")}),
    };
    let cx=ty::layout::LayoutCx::new(tcx,env);
    let mut records=vec![parent(tcx,context,&cx,layout,None)];
    let count=match input.kind(){
        ty::Adt(def,_)=>def.variants().len(),
        ty::Coroutine(..)=>match &layout.variants{rustc_abi::Variants::Multiple{variants,..}=>variants.len(),_=>0},
        _=>0,
    };
    for index in 0..count {
        let selected=layout.for_variant(&cx,rustc_abi::VariantIdx::from_usize(index));
        records.push(parent(tcx,context,&cx,selected,Some(index)));
    }
    compiler_fact(json!({"typing_env":"fully_monomorphized","parents":records}))
}
