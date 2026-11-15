//! Generic parameter declarations. A captured default is a source type template,
//! never an instruction to supply a missing instance argument.
use super::*;

impl<'tcx> Material<'tcx> {
    pub(super) fn generic_parameter(&mut self, tcx: TyCtxt<'tcx>, parameter: &ty::GenericParamDef) -> Result<Value> {
        Ok(match parameter.kind {
            ty::GenericParamDefKind::Lifetime => json!({"kind":"region","index":parameter.index,"name":parameter.name.as_str(),
                "definition":self.definition(tcx,parameter.def_id),"has_default":false,"default":null}),
            ty::GenericParamDefKind::Type {has_default,..} => {
                let default = if has_default {
                    Some(self.ty(tcx,tcx.type_of(parameter.def_id).instantiate_identity().skip_normalization())?)
                } else { None };
                json!({"kind":"type","index":parameter.index,"name":parameter.name.as_str(),
                    "definition":self.definition(tcx,parameter.def_id),"has_default":has_default,"default":default})
            },
            ty::GenericParamDefKind::Const {has_default:false,..} => json!({
                "kind":"const","index":parameter.index,"name":parameter.name.as_str(),
                "definition":self.definition(tcx,parameter.def_id),"has_default":false,"default":null,
                "type":self.ty(tcx,tcx.type_of(parameter.def_id).instantiate_identity().skip_normalization())?,
            }),
            _ => return unsupported("generic parameter",parameter),
        })
    }
}
