//! Finite source for helpers.rs::iter_exported_symbols/lookup_link_section.
//! No static initializer, Instance::mono, allocation or symbol winner is queried.
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::{middle::{codegen_fn_attrs::CodegenFnAttrFlags as F,
    dependency_format::Linkage, exported_symbols::ExportedSymbol}, ty::TyCtxt};
use serde_json::{json, Value};
use rustc_span::Pos;

fn raw_definition(definition: DefId) -> Value {
    json!({"crate_index":definition.krate.as_u32(),"definition_index":definition.index.as_u32()})
}

// Shallow declarations only: GenericArgs::for_item used by Instance::mono
// concatenates these owners and erases lifetime slots. No predicates, types,
// instance constructor or MIR query is needed to retain that source structure.
fn generic_layers(tcx: TyCtxt<'_>, definition: DefId) -> Vec<Value> {
    let mut owners = Vec::new();
    let mut current = Some(definition);
    while let Some(owner) = current {
        let generics = tcx.generics_of(owner);
        owners.push(json!({"owner":raw_definition(owner),
            "parent":generics.parent.map(raw_definition),"parent_count":generics.parent_count,
            "parameters":generics.own_params.iter().map(|parameter|json!({
                "index":parameter.index,"definition":raw_definition(parameter.def_id),
                "kind":match parameter.kind {
                    rustc_middle::ty::GenericParamDefKind::Lifetime=>"region",
                    rustc_middle::ty::GenericParamDefKind::Type{..}=>"type",
                    rustc_middle::ty::GenericParamDefKind::Const{..}=>"const",
                }})).collect::<Vec<_>>()}));
        current = generics.parent;
    }
    owners.reverse();
    owners
}

fn item(tcx: TyCtxt<'_>, definition: DefId) -> Value {
    let attrs = tcx.codegen_fn_attrs(definition);
    let span = tcx.def_span(definition);
    let start = tcx.sess.source_map().lookup_char_pos(span.lo());
    let end = tcx.sess.source_map().lookup_char_pos(span.hi());
    let explicit = attrs.symbol_name.is_some() || attrs.flags.contains(F::NO_MANGLE)
        || attrs.flags.contains(F::RUSTC_STD_INTERNAL_SYMBOL);
    let proc_macro_declarations = definition.as_local().is_some_and(|local|
        tcx.proc_macro_decls_static(()) == Some(local));
    json!({"crate_index":definition.krate.as_u32(),"definition_index":definition.index.as_u32(),
        "definition_kind":format!("{:?}",tcx.def_kind(definition)),
        "definition_path":tcx.def_path_str(definition),
        "symbol_kind":match tcx.def_kind(definition) {
            rustc_hir::def::DefKind::Fn=>"function",
            rustc_hir::def::DefKind::AssocFn=>"associated_function",
            rustc_hir::def::DefKind::Static{..}=>"static",_=>"other"},
        "symbol_name":attrs.symbol_name.map(|s|s.as_str().to_owned()),
        "item_name":tcx.opt_item_name(definition).map(|s|s.as_str().to_owned()),
        "no_mangle":attrs.flags.contains(F::NO_MANGLE),
        "std_internal_symbol":attrs.flags.contains(F::RUSTC_STD_INTERNAL_SYMBOL),
        "symbol_linkage":attrs.linkage.map(|linkage|format!("{linkage:?}")),
        "proc_macro_declarations":proc_macro_declarations,
        "generic_layers":if explicit {Some(generic_layers(tcx,definition))} else {None},
        "source_span":{"is_dummy":span.is_dummy(),"file":format!("{:?}",start.file.name),
            "start":{"line":start.line,"column":start.col.to_usize()},
            "end":{"line":end.line,"column":end.col.to_usize()}},
        "used_compiler":attrs.flags.contains(F::USED_COMPILER),
        "used_linker":attrs.flags.contains(F::USED_LINKER),
        "extern_indicator":attrs.contains_extern_indicator(),
        "link_section":attrs.link_section.map(|s|s.as_str().to_owned()),
        "source_span_key":{"lo":span.lo().0,"hi":span.hi().0,
            "ctxt":format!("{:?}",span.ctxt()),
            "parent_local_definition":span.parent().map(|d|d.local_def_index.as_u32())}})
}

pub(super) fn export(tcx: TyCtxt<'_>) -> Value {
    let locals = tcx.hir_crate_items(()).definitions().filter(|d|
        tcx.def_kind(d.to_def_id()).has_codegen_attrs() && !tcx.is_foreign_item(d.to_def_id()))
        .map(|d|item(tcx,d.to_def_id())).collect::<Vec<_>>();
    let formats = tcx.dependency_formats(());
    let dependencies = formats.get(&rustc_structures::CrateType::Executable).map(|format|
        format.iter_enumerated().map(|(krate, linkage)| {
            let exports = if krate == LOCAL_CRATE || *linkage == Linkage::NotLinked { vec![] }
                else { tcx.exported_non_generic_symbols(krate).iter().map(|(symbol,info)|match symbol {
                    ExportedSymbol::NonGeneric(definition) => {
                        let foreign = tcx.is_foreign_item(*definition);
                        json!({"kind":"non_generic","used":info.used,"is_foreign":foreign,
                            "item":if foreign {Value::Null} else {item(tcx,*definition)}})
                    },
                    _ => json!({"kind":"other"}),
                }).collect::<Vec<_>>() };
            json!({"crate_index":krate.as_u32(),"crate_name":tcx.crate_name(krate).as_str(),
                "compiler_builtins":tcx.is_compiler_builtins(krate),
                "linkage":format!("{linkage:?}"),"exports":exports})
        }).collect::<Vec<_>>());
    json!({"local_crate":LOCAL_CRATE.as_u32(),"local_crate_name":tcx.crate_name(LOCAL_CRATE).as_str(),
        "local_compiler_builtins":tcx.is_compiler_builtins(LOCAL_CRATE),"local_items":locals,"executable_dependencies":dependencies})
}
