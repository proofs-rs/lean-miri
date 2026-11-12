//! Source-only ordinary direct callee material for the selected raw MIR family.
//! Instance graph and ABI construction remain explicit residual providers.
use rustc_middle::{mir,ty::{self,TyCtxt,TypeVisitableExt}};

pub fn callee<'tcx>(tcx:TyCtxt<'tcx>, operand:&mir::Operand<'tcx>)->Result<String,String> {
    let mir::Operand::Constant(operand)=operand else {
        return Err("direct source call requires a FnDef constant".into());
    };
    if !matches!(operand.const_,mir::Const::Val(mir::ConstValue::ZeroSized,_)) {
        return Err("direct source call requires a literal zero-sized function constant".into());
    }
    if operand.user_ty.is_some() {
        return Err("direct source call requires absent user type annotation".into());
    }
    function_type_material(tcx,operand.const_.ty())
}

pub fn function_type_material<'tcx>(tcx:TyCtxt<'tcx>, function_type:ty::Ty<'tcx>)->Result<String,String> {
    let ty::FnDef(def,args)=function_type.kind() else {
        return Err("direct source call excludes function pointers and virtual receivers".into());
    };
    if tcx.def_kind(*def)!=rustc_hir::def::DefKind::Fn || !args.bound_vars().is_empty() {
        return Err("direct source call supports only binder-free ordinary functions".into());
    }
    if tcx.trait_of_assoc(*def).is_some() || tcx.intrinsic(*def).is_some()
        || tcx.is_lang_item(*def,rustc_attr_ir::LangItem::DropGlue)
        || tcx.is_lang_item(*def,rustc_attr_ir::LangItem::AsyncDropInPlace)
        || tcx.is_async_drop_in_place_coroutine(*def)
        || tcx.is_foreign_item(*def)
        || tcx.codegen_fn_attrs(*def).symbol_name.is_some_and(|name|name.as_str().starts_with("llvm.")) {
        return Err("source callee requires intrinsic/drop/foreign/trait instance resolution".into());
    }
    if tcx.fn_sig(*def).instantiate_identity().skip_norm_wip().c_variadic() {
        return Err("ordinary source call requires a non-variadic declaration".into());
    }
    let args=args.skip_binder();
    if !args.iter().all(|arg|matches!(arg.kind(),ty::GenericArgKind::Type(_)))
        || !super::generic_mir::supported_arguments(args) {
        return Err("direct source call requires supported type-only generic arguments".into());
    }
    let arguments=args.iter().map(|arg|super::generic_material::argument(tcx,arg))
        .collect::<Result<Vec<_>,_>>()?.join(",");
    Ok(format!("{{\"definition\":{{\"crate\":{},\"index\":{}}},\"arguments\":[{arguments}]}}",
        def.krate.as_u32(),def.index.as_u32()))
}

/// Remaining material-graph dependency discovery. This does not instantiate an
/// enclosing or target MIR body and emits no call-site resolution answer. The
/// canonical per-instance graph/ABI material remains an explicit residual.
pub struct Dependency<'tcx> {
    pub function_type:ty::Ty<'tcx>,
    pub instance:ty::Instance<'tcx>,
}

pub fn dependencies<'tcx>(tcx:TyCtxt<'tcx>,body:&mir::Body<'tcx>,
    caller_args:ty::GenericArgsRef<'tcx>)->Result<Vec<Dependency<'tcx>>,String> {
    let mut dependencies=Vec::new();
    for block in body.basic_blocks.iter() {
        let mir::TerminatorKind::Call{func,..}=&block.terminator().kind else {continue};
        callee(tcx,func)?;
        let mir::Operand::Constant(constant)=func else {unreachable!()};
        let function_type=tcx.erase_and_anonymize_regions(
            ty::EarlyBinder::bind(tcx,constant.const_.ty()).instantiate(tcx,caller_args).skip_normalization());
        if function_type.has_non_region_param() || function_type.has_escaping_bound_vars()
            || function_type.has_infer() || function_type.has_placeholders() || function_type.references_error() {
            return Err("ordinary source-call dependency retains unresolved arguments".into());
        }
        function_type_material(tcx,function_type)?;
        let ty::FnDef(def,args)=function_type.kind() else {unreachable!()};
        dependencies.push(Dependency {function_type,instance:ty::Instance {
            def:ty::InstanceKind::Item(*def),args:args.skip_binder() }});
    }
    Ok(dependencies)
}
