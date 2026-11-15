//! Finite concrete source-key observations, evaluated by the producing compiler.
//! No codegen collection and no monomorphic combination enumeration. Allocation
//! identity must remain exactly unchanged: a dirty session cannot be rolled back.
use super::*;
#[cfg(feature = "allocation-identity-snapshot")]
use rustc_middle::ty::TypeVisitableExt;
impl<'tcx> Material<'tcx> {
    pub(super) fn constant_alias(&mut self, tcx: TyCtxt<'tcx>, original: ty::Const<'tcx>,
        rigidity: ty::IsRigid, alias: ty::AliasConst<'tcx>) -> Result<Value> {
        if let Some(reference) = self.constant_alias_ids.get(&original) {
            return Ok(json!({"kind":"alias","reference":reference}));
        }
        let (kind,definition) = match alias.kind {
            ty::AliasConstKind::Projection {def_id} => ("projection",def_id),
            ty::AliasConstKind::InherentSelf {def_id} => ("inherent_self",def_id),
            ty::AliasConstKind::InherentImpl {def_id} => ("inherent_impl",def_id),
            ty::AliasConstKind::Free {def_id} => ("free",def_id),
            ty::AliasConstKind::Anon {def_id} => ("anonymous",def_id),
        };
        let reference = self.constant_aliases.len();
        self.constant_alias_ids.insert(original,reference);
        self.constant_aliases.push(Value::Null);
        self.constant_aliases[reference] = json!({"kind":kind,
            "rigid":matches!(rigidity,ty::IsRigid::Yes),
            "definition":self.definition(tcx,definition),
            "type":self.ty(tcx,tcx.type_of(definition).instantiate(tcx,alias.args).skip_normalization())?,
            "arguments":self.args(tcx,alias.args)?});
        // These are precisely the families represented by UnevaluatedConst::shrink.
        // InherentSelf has a distinct resolution namespace and stays syntax only.
        if kind != "inherent_self" {
            let key = mir::UnevaluatedConst {def:definition,args:alias.args,promoted:None};
            if !self.observed_constants.contains(&key) { self.observed_constants.push(key); }
        }
        Ok(json!({"kind":"alias","reference":reference}))
    }

    #[cfg(not(feature = "allocation-identity-snapshot"))]
    pub(super) fn evaluated_const_values(&mut self, _: TyCtxt<'tcx>) -> Result<Value> {
        Ok(Value::Null)
    }
    #[cfg(feature = "allocation-identity-snapshot")]
    pub(super) fn evaluated_const_values(&mut self, tcx: TyCtxt<'tcx>) -> Result<Value> {
        let mut before = tcx.lean_miri_complete_allocation_identity_snapshot();
        let mut rows = Vec::new();
        let mut captured = Vec::new();
        for original in self.observed_constants.clone() {
            if original.promoted.is_some() || original.args.has_param()
                || original.args.has_bound_vars() || original.args.has_non_region_infer()
                || original.args.has_aliases() { continue; }
            let args = tcx.erase_and_anonymize_regions(original.args);
            let key = mir::UnevaluatedConst { def: original.def, args, promoted: original.promoted };
            if captured.contains(&key) { continue; }
            captured.push(key);
            let result_type = tcx.type_of(key.def).instantiate(tcx,args).skip_normalization();
            // Avoid speculative aggregate/pointer CTFE. More result domains need
            // their own provenance-preserving transfer protocol.
            if !matches!(result_type.kind(), ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_))
                && !matches!(result_type.kind(), ty::Tuple(fields) if fields.is_empty()) { continue; }
            let result = tcx.const_eval_resolve(ty::TypingEnv::fully_monomorphized(),key,tcx.def_span(key.def));
            let value = match result {
                Ok(mir::ConstValue::Scalar(mir::interpret::Scalar::Int(value))) =>
                    json!({"kind":"scalar","bits":value.to_bits(value.size()).to_string(),"size_bytes":value.size().bytes()}),
                Ok(mir::ConstValue::ZeroSized) => json!({"kind":"zero_sized"}),
                Ok(other) => return unsupported("concrete constant witness value",other),
                Err(error) => return unsupported("concrete constant witness evaluation",error),
            };
            rows.push(json!({"definition":self.definition(tcx,key.def),"parameters":(0..tcx.generics_of(key.def).count()).map(|index| match tcx.generics_of(key.def).param_at(index,tcx).kind {ty::GenericParamDefKind::Lifetime => "lifetime", ty::GenericParamDefKind::Type {..} => "type", ty::GenericParamDefKind::Const {..} => "const"}).collect::<Vec<_>>(),"arguments":self.args(tcx,key.args)?,
                "promoted":key.promoted.map(|id|id.as_u32()),"type":self.ty(tcx,result_type)?,"value":value}));
        }
        let mut after = tcx.lean_miri_complete_allocation_identity_snapshot();
        before.1.sort_by_key(|(id,_)|id.0.get()); before.2.sort_by_key(|(_,salt,id)|(id.0.get(),*salt));
        after.1.sort_by_key(|(id,_)|id.0.get()); after.2.sort_by_key(|(_,salt,id)|(id.0.get(),*salt));
        if before != after { return Err("concrete constant evaluation changed allocation identity; refusing snapshot".into()); }
        Ok(json!({"rows":rows}))
    }
}
