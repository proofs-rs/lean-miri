//! Enum declaration material only. Logical discriminant expressions are source
//! identities; no compiler layout, niche, or evaluated discriminant query occurs.
use super::*;

impl<'tcx> Material<'tcx> {
    pub(super) fn enum_definition(&mut self, tcx: TyCtxt<'tcx>, adt: ty::AdtDef<'tcx>) -> Result<()> {
        if !adt.is_enum() { return unsupported("enum declaration kind", adt.did()); }
        let definition = self.definition(tcx,adt.did());
        if self.definitions[definition].get("adt").is_some() { return Ok(()); }
        // Recursive field types may refer back to this declaration. The marker
        // never survives a successful completed material traversal.
        self.definitions[definition]["adt"] = json!({"pending":true});
        let identity = ty::GenericArgs::identity_for_item(tcx,adt.did());
        let environment = self.environment(tcx,adt.did())?;
        let variants = adt.variants().iter().enumerate().map(|(index,variant)| {
            let discriminant = match variant.discr {
                ty::VariantDiscr::Relative(distance) => json!({"kind":"relative","distance":distance}),
                ty::VariantDiscr::Explicit(did) => json!({"kind":"explicit","definition":self.definition(tcx,did)}),
            };
            let constructor = match (variant.ctor_def_id(),variant.ctor_kind()) {
                (None,None) => None,
                (Some(did),Some(kind)) => Some(json!({"definition":self.definition(tcx,did),
                    "kind":match kind {rustc_hir::def::CtorKind::Fn=>"function",rustc_hir::def::CtorKind::Const=>"constant"}})),
                other => return unsupported("enum constructor identity",other),
            };
            let fields = variant.fields.iter().enumerate().map(|(index,field)| Ok(json!({
                "index":index,"definition":self.definition(tcx,field.did),"name":field.name.as_str(),
                "type":self.ty(tcx,field.ty(tcx,identity).skip_normalization())?,
            }))).collect::<Result<Vec<_>>>()?;
            Ok(json!({"index":index,"definition":self.definition(tcx,variant.def_id),"name":variant.name.as_str(),
                "constructor":constructor,"fields_non_exhaustive":variant.is_field_list_non_exhaustive(),
                "discriminant":discriminant,"fields":fields}))
        }).collect::<Result<Vec<_>>>()?;
        self.definitions[definition]["adt"] = json!({"kind":"enum","environment":environment,
            "representation":super::super::repr_options_json(&adt.repr()),
            "variants_non_exhaustive":adt.is_variant_list_non_exhaustive(),"variants":variants});
        Ok(())
    }
}
