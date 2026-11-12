//! Source-only ordinary direct callee material. Not selected by the production
//! body exporter until lazy instance/ABI/transfer providers support this family.
use rustc_middle::{mir,ty::{self,TyCtxt}};

pub fn callee<'tcx>(tcx:TyCtxt<'tcx>, operand:&mir::Operand<'tcx>)->Result<String,String> {
    let mir::Operand::Constant(operand)=operand else {
        return Err("direct source call requires a FnDef constant".into());
    };
    if operand.user_ty.is_some() {
        return Err("direct source call requires absent user type annotation".into());
    }
    function_type(tcx,operand.const_.ty())
}

pub fn function_type<'tcx>(tcx:TyCtxt<'tcx>, function_type:ty::Ty<'tcx>)->Result<String,String> {
    let ty::FnDef(def,args)=function_type.kind() else {
        return Err("direct source call excludes function pointers and virtual receivers".into());
    };
    if tcx.def_kind(*def)!=rustc_hir::def::DefKind::Fn || !args.bound_vars().is_empty() {
        return Err("direct source call supports only binder-free ordinary functions".into());
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
