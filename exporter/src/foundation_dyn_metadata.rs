//! Generic source declarations used to derive dyn-pointer representation.
//! No layout, trait-selection, vtable or allocation query answer is captured.
use super::*;

fn repr(tcx: TyCtxt<'_>, adt: ty::AdtDef<'_>) -> Value {
    let _ = tcx;
    json!(super::super::repr_options_json(&adt.repr()))
}

pub(super) fn capture<'tcx>(tcx: TyCtxt<'tcx>, material: &mut Material<'tcx>) -> Result<Value> {
    let Some(metadata) = tcx.lang_items().metadata_type() else {
        return Ok(json!({"mode":"metadata_lang_item_absent","metadata_type":null}));
    };
    let metadata_parent = tcx.parent(metadata);
    if !tcx.is_lang_item(metadata_parent,rustc_attr_ir::LangItem::PointeeTrait) {
        return unsupported("metadata associated item parent",metadata_parent);
    }
    let dyn_def = tcx.lang_items().dyn_metadata().ok_or("foundation: DynMetadata lang item absent")?;
    let dyn_ty = tcx.type_of(dyn_def).instantiate_identity().skip_norm_wip();
    let ty::Adt(dyn_adt,dyn_args) = *dyn_ty.kind() else { return unsupported("DynMetadata declaration",dyn_ty); };
    if dyn_adt.variants().len()!=1 || dyn_adt.non_enum_variant().fields.len()!=2 {
        return unsupported("DynMetadata fields",dyn_ty);
    }
    let fields = &dyn_adt.non_enum_variant().fields;
    let nonnull_ty = fields.iter().next().ok_or("foundation: vtable field absent")?.ty(tcx,dyn_args).skip_normalization();
    let phantom_ty = fields.iter().nth(1).ok_or("foundation: phantom field absent")?.ty(tcx,dyn_args).skip_normalization();
    let ty::Adt(nonnull,nonnull_args) = *nonnull_ty.kind() else { return unsupported("DynMetadata vtable field",nonnull_ty); };
    let ty::Adt(phantom,phantom_args) = *phantom_ty.kind() else { return unsupported("DynMetadata phantom field",phantom_ty); };
    if !tcx.is_lang_item(nonnull.did(),rustc_attr_ir::LangItem::NonNull) ||
        !tcx.is_lang_item(phantom.did(),rustc_attr_ir::LangItem::PhantomData) {
        return unsupported("DynMetadata field lang items",dyn_ty);
    }
    if nonnull.variants().len()!=1 || nonnull.non_enum_variant().fields.len()!=1 ||
        phantom.variants().len()!=1 || !phantom.non_enum_variant().fields.is_empty() {
        return unsupported("metadata wrapper fields",dyn_ty);
    }
    let pointer_ty = nonnull.non_enum_variant().fields.iter().next().ok_or("foundation: vtable field absent")?.ty(tcx,nonnull_args).skip_normalization();
    let ty::Pat(base,pattern) = *pointer_ty.kind() else { return unsupported("NonNull field pattern",pointer_ty); };
    if !matches!(*pattern,ty::PatternKind::NotNull) { return unsupported("NonNull pattern",pattern); }
    let ty::RawPtr(foreign,mutability) = *base.kind() else { return unsupported("NonNull field pointer",base); };
    let ty::Foreign(foreign_def) = *foreign.kind() else { return unsupported("vtable pointee",foreign); };
    let phantom_arg = phantom_args.type_at(0);
    let ty::Param(param) = *phantom_arg.kind() else { return unsupported("DynMetadata phantom parameter",phantom_arg); };
    Ok(json!({"mode":"lang_item_declarations","metadata_type":material.definition(tcx,metadata),
        "pointee_trait":material.definition(tcx,metadata_parent),"metadata_parent":material.definition(tcx,metadata_parent),
        "pointee_parameter_count":tcx.generics_of(metadata_parent).count(),"metadata_parameter_count":tcx.generics_of(metadata).count(),
        "dyn_metadata":{"definition":material.definition(tcx,dyn_def),"repr":repr(tcx,dyn_adt),"field_count":fields.len(),"parameter_count":dyn_args.len(),
            "vtable_field":0,"phantom_field":1},
        "non_null":{"definition":material.definition(tcx,nonnull.did()),"lang_item":"non_null","repr":repr(tcx,nonnull),
            "field_count":1,"argument_count":nonnull_args.len(),"field":{"kind":"pattern","pattern":"not_null","base_kind":"raw_pointer",
                "mutable":mutability.is_mut(),"pointee_kind":"foreign","pointee_definition":material.definition(tcx,foreign_def)}},
        "phantom_data":{"definition":material.definition(tcx,phantom.did()),"lang_item":"phantom_data","repr":repr(tcx,phantom),
            "field_count":0,"argument_count":phantom_args.len(),"argument":{"kind":"param","index":param.index}}}))
}
