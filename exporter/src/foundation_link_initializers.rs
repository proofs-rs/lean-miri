//! Static initializer MIR syntax only. No CTFE, function resolution, allocator
//! reservation, global image query, or invented raw allocation identity.
use super::*;
use rustc_hir::def_id::{CrateNum, DefIndex};

impl<'tcx> Material<'tcx> {
    fn link_initializer(&mut self, tcx: TyCtxt<'tcx>, definition: DefId) -> Result<Value> {
        if !matches!(tcx.def_kind(definition),rustc_hir::def::DefKind::Static {..}) {
            return Ok(json!({"status":"unsupported","reason":"link item is not a static"}));
        }
        let mutable = match tcx.def_kind(definition) {rustc_hir::def::DefKind::Static {mutability,..}=>mutability.is_mut(),_=>unreachable!()};
        let thread_local = tcx.is_thread_local_static(definition);
        // Pinned rustc_metadata::encoder::should_encode_mir excludes Static,
        // including under always_encode_mir. Its type is still real metadata;
        // do not force const_eval or fabricate an external initializer body.
        if !definition.is_local() {
            let ty = tcx.type_of(definition).instantiate_identity().skip_normalization();
            return Ok(json!({"status":"unsupported",
                "reason":"pinned metadata does not encode external static initializer MIR",
                "static_definition":self.definition(tcx,definition),"static_type":self.ty(tcx,ty)?,
                "static_mutable":mutable,"thread_local":thread_local,
                "allocation_identity_status":"not_observed_from_initializer_mir"}));
        }
        let body = tcx.mir_for_ctfe(definition);
        super::super::ensure_untainted_mir(body)?;
        if body.arg_count != 0 || body.basic_blocks.len() != 1 || body.local_decls.len() != 1 {
            return Ok(json!({"status":"unsupported","reason":"static initializer is not one scalar expression"}));
        }
        let block = &body.basic_blocks[mir::START_BLOCK];
        if block.is_cleanup || block.statements.len() != 1 || !matches!(block.terminator().kind,mir::TerminatorKind::Return) {
            return Ok(json!({"status":"unsupported","reason":"static initializer control flow unsupported"}));
        }
        let mir::StatementKind::Assign(assignment) = &block.statements[0].kind else {
            return Ok(json!({"status":"unsupported","reason":"static initializer assignment unavailable"}));
        };
        if assignment.0.local != mir::RETURN_PLACE || !assignment.0.projection.is_empty() {
            return Ok(json!({"status":"unsupported","reason":"static initializer writes another place"}));
        }
        let mir::Rvalue::Cast(mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::ReifyFnPointer(safety),origin),operand,target) = &assignment.1 else {
            return Ok(json!({"status":"unsupported","reason":"static initializer is not FnDef reification"}));
        };
        let ty::FnDef(function,arguments) = *operand.ty(body,tcx).kind() else {
            return Ok(json!({"status":"unsupported","reason":"static reification input is not FnDef"}));
        };
        if !arguments.bound_vars().is_empty() || !arguments.skip_binder().is_empty()
            || *target != body.return_ty() || !matches!(target.kind(),ty::FnPtr(..)) {
            return Ok(json!({"status":"unsupported","reason":"generic or mismatched function reification"}));
        }
        let function_header = self.function_header(tcx,function)?;
        Ok(json!({"status":"source","static_definition":self.definition(tcx,definition),
            "static_type":self.ty(tcx,body.return_ty())?,"static_mutable":mutable,"thread_local":thread_local,"required_consts":self.required_constants(tcx,body)?,
            "expression":{"kind":"reify_fn_pointer","operand":self.operand(tcx,operand)?,
                "target_type":self.ty(tcx,*target)?,"function_definition":self.definition(tcx,function),
                "safety":match safety {rustc_hir::Safety::Safe=>"safe",rustc_hir::Safety::Unsafe=>"unsafe"},
                "origin":match origin {mir::CoercionSource::AsCast=>"as_cast",mir::CoercionSource::Implicit=>"implicit"}},
            "function_header":function_header,
            "allocation_identity_status":"not_observed_from_initializer_mir"}))
    }
    pub(super) fn attach_link_initializers(&mut self, tcx: TyCtxt<'tcx>, material: &mut Value) -> Result<()> {
        fn attach<'tcx>(source: &mut Material<'tcx>, tcx: TyCtxt<'tcx>, item: &mut Value) -> Result<()> {
            if !item.get("link_section").is_some_and(|value|value.is_string()) { return Ok(()); }
            let crate_index = item["crate_index"].as_u64().ok_or("link item crate source absent")?;
            let definition_index = item["definition_index"].as_u64().ok_or("link item definition source absent")?;
            let definition = DefId {krate:CrateNum::from_u32(u32::try_from(crate_index).map_err(|_|"link crate index overflow")?),
                index:DefIndex::from_u32(u32::try_from(definition_index).map_err(|_|"link definition index overflow")?)};
            item["initializer_source"] = source.link_initializer(tcx,definition)?;
            Ok(())
        }
        for item in material["local_items"].as_array_mut().ok_or("local link items absent")? {attach(self,tcx,item)?;}
        if let Some(dependencies) = material["executable_dependencies"].as_array_mut() {
            for dependency in dependencies {
                for symbol in dependency["exports"].as_array_mut().ok_or("link dependency exports absent")? {
                    if symbol["kind"] == "non_generic" && symbol["is_foreign"] == false {
                        attach(self,tcx,&mut symbol["item"])?;
                    }
                }
            }
        }
        Ok(())
    }
}
