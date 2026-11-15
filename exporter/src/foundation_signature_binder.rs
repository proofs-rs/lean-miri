//! Source lifetime binders, without instantiating or erasing them in rustc.
//! Canonical/inference/early regions and bound type/const variables reject.
use super::*;

impl<'tcx> Material<'tcx> {
    pub(super) fn bound_region_source(&mut self, tcx: TyCtxt<'tcx>, kind: ty::BoundRegionKind<'tcx>) -> Result<Value> {
        Ok(match kind {
            ty::BoundRegionKind::Anon => json!({"kind":"anonymous"}),
            ty::BoundRegionKind::NamedForPrinting(name) => json!({"kind":"named_for_printing","name":name.as_str()}),
            ty::BoundRegionKind::Named(definition) => json!({"kind":"named","definition":self.definition(tcx,definition)}),
            ty::BoundRegionKind::ClosureEnv => json!({"kind":"closure_environment"}),
        })
    }

    pub(super) fn signature_region(&mut self, tcx: TyCtxt<'tcx>, region: ty::Region<'tcx>) -> Result<Value> {
        Ok(match region.kind() {
            ty::ReStatic => json!("static"),
            ty::ReErased => json!("erased"),
            ty::ReEarlyParam(parameter) => json!({"kind":"early_parameter","index":parameter.index}),
            ty::ReBound(ty::BoundVarIndexKind::Bound(depth), bound) => json!({
                "kind":"bound","debruijn":depth.as_u32(),"variable":bound.var.as_u32(),
                "region_kind":self.bound_region_source(tcx,bound.kind)?,
            }),
            other => return unsupported("signature region",other),
        })
    }

    pub(super) fn signature_binders(&mut self, tcx: TyCtxt<'tcx>, variables: &'tcx ty::List<ty::BoundVariableKind<'tcx>>) -> Result<Vec<Value>> {
        variables.iter().map(|kind| match kind {
            ty::BoundVariableKind::Region(region) => Ok(json!({"kind":"region","region_kind":self.bound_region_source(tcx,region)?})),
            other => unsupported("function signature bound variable",other),
        }).collect()
    }
}
