//! Finite closure source templates. No monomorphic instance, layout, vtable or
//! trait-call resolution answer is computed or serialized here.
use super::*;

impl<'tcx> Material<'tcx> {
    pub(super) fn closure_type(&mut self, tcx: TyCtxt<'tcx>, def: DefId,
        args: ty::GenericArgsRef<'tcx>) -> Result<Value> {
        let closure = args.as_closure();
        let generics = tcx.generics_of(def);
        let parent = generics.parent.ok_or("foundation: closure has no generic parent")?;
        if closure.parent_args().len() != generics.parent_count {
            return unsupported("closure inherited argument count", def);
        }
        Ok(json!({"kind":"closure","definition":self.definition(tcx,def),
            "arguments":self.args(tcx,args)?,
            "parent_definition":self.definition(tcx,parent),
            "parent_count":generics.parent_count,
            "kind_type":self.ty(tcx,closure.kind_ty())?,
            "signature_type":self.ty(tcx,closure.sig_as_fn_ptr_ty())?,
            "tupled_upvars_type":self.ty(tcx,closure.tupled_upvars_ty())?}))
    }

    pub(super) fn closure_template(&mut self, tcx: TyCtxt<'tcx>, def: DefId) -> Result<Value> {
        if tcx.def_kind(def) != rustc_hir::def::DefKind::Closure {
            return unsupported("closure template definition kind", def);
        }
        let source_ty = tcx.type_of(def).instantiate_identity().skip_normalization();
        let ty::Closure(source_def, args) = *source_ty.kind()
            else { return unsupported("closure source type", source_ty); };
        if source_def != def { return unsupported("closure source definition mismatch", source_def); }
        let closure = args.as_closure();
        let generics = tcx.generics_of(def);
        let parent = generics.parent.ok_or("foundation: closure template has no parent")?;
        let parent_environment = self.environment(tcx,parent)?;
        let parameters = generics.own_params.iter().map(|p| Ok(match p.kind {
            ty::GenericParamDefKind::Type {has_default:false,..} =>
                json!({"kind":"type","index":p.index,"name":p.name.as_str()}),
            _ => return unsupported("closure synthetic generic parameter",p),
        })).collect::<Result<Vec<_>>>()?;
        let predicates = tcx.clauses_of(def);
        if predicates.parent != Some(parent) || !predicates.clauses.is_empty() {
            return unsupported("closure own predicates",predicates);
        }
        let body = tcx.instance_mir(ty::InstanceKind::Item(def));
        super::super::ensure_untainted_mir(body)?;
        if body.source.instance != ty::InstanceKind::Item(def) || body.source.promoted.is_some()
            || body.coroutine.is_some() || !matches!(body.phase,mir::MirPhase::Runtime(_)) {
            return unsupported("closure MIR source",body.source);
        }
        if body.source_scopes.iter().any(|s|s.inlined.is_some() || s.inlined_parent_scope.is_some()) {
            return unsupported("closure inlined source scopes",def);
        }
        let promoted_count = tcx.promoted_mir(def).len();
        if promoted_count != 0 { return unsupported("closure promoted bodies",promoted_count); }
        let source_metadata = source_material::capture(tcx,body);
        let required_consts = self.required_constants(tcx,body)?;
        let locals = body.local_decls.iter().map(|l|self.ty(tcx,l.ty)).collect::<Result<Vec<_>>>()?;
        let blocks = body.basic_blocks.iter().map(|block| {
            let statements = block.statements.iter().map(|s|Ok(match &s.kind {
                mir::StatementKind::Assign(p) => json!({"kind":"assign","place":self.place(tcx,p.0)?,"value":self.rvalue(tcx,&p.1)?}),
                mir::StatementKind::StorageLive(local) => json!({"kind":"storage_live","local":local.as_u32()}),
                mir::StatementKind::StorageDead(local) => json!({"kind":"storage_dead","local":local.as_u32()}),
                mir::StatementKind::Nop => json!({"kind":"nop"}),
                other => return unsupported("closure statement",other),
            })).collect::<Result<Vec<_>>>()?;
            let terminator = match &block.terminator().kind {
                mir::TerminatorKind::Return => json!({"kind":"return"}),
                mir::TerminatorKind::UnwindResume => json!({"kind":"unwind_resume"}),
                mir::TerminatorKind::Unreachable => json!({"kind":"unreachable"}),
                mir::TerminatorKind::Goto {target,..} => json!({"kind":"goto","target":target.as_u32()}),
                mir::TerminatorKind::SwitchInt {discr,targets} => json!({"kind":"switch_int",
                    "operand":self.operand(tcx,discr)?,
                    "targets":targets.iter().map(|(value,target)|json!({"value":value.to_string(),"target":target.as_u32()})).collect::<Vec<_>>(),
                    "otherwise":targets.otherwise().as_u32()}),
                mir::TerminatorKind::Call {func,args,destination,target,unwind,call_source,..} => json!({
                    "kind":"call","function":self.operand(tcx,func)?,
                    "arguments":args.iter().map(|arg|self.operand(tcx,&arg.node)).collect::<Result<Vec<_>>>()?,
                    "destination":self.place(tcx,*destination)?,"target":target.map(|b|b.as_u32()),
                    "unwind":super::super::unwind_json(*unwind),"call_source":super::super::call_source_name(*call_source)}),
                other => return unsupported("closure terminator",other),
            };
            Ok(json!({"cleanup":block.is_cleanup,"statements":statements,"terminator":terminator}))
        }).collect::<Result<Vec<_>>>()?;
        Ok(json!({"definition":self.definition(tcx,def),
            "runtime_source":super::super::foundation_runtime_instances::item(tcx,def),"function_attributes":{
            "never_unwind":tcx.codegen_fn_attrs(def).flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::NEVER_UNWIND),
            "track_caller":tcx.codegen_fn_attrs(def).flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::TRACK_CALLER),
            "is_foreign":tcx.is_foreign_item(def),"is_drop_glue":tcx.is_lang_item(def,rustc_attr_ir::LangItem::DropGlue)
        },"track_caller":tcx.codegen_fn_attrs(def).flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::TRACK_CALLER),"source_type":self.ty(tcx,source_ty)?,
            "parent_definition":self.definition(tcx,parent),"parent_count":generics.parent_count,
            "parent_environment":parent_environment,"own_parameters":parameters,"own_clauses":[],
            "kind_type":self.ty(tcx,closure.kind_ty())?,"signature_type":self.ty(tcx,closure.sig_as_fn_ptr_ty())?,
            "tupled_upvars_type":self.ty(tcx,closure.tupled_upvars_ty())?,
            "argument_count":body.arg_count,"spread_argument":body.spread_arg.map(|l|l.as_u32()),
            "promoted_count":promoted_count,"required_consts":required_consts,
            "source_metadata":source_metadata,"locals":locals,"blocks":blocks}))
    }
}
