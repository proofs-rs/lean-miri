//! Source-domain classification for allocation-free ValTree conversion.
//! This reads constructor/declaration syntax and raw target alignment only;
//! it never calls layout_of, Const::eval or valtree_to_const_val.
use rustc_middle::ty::{self, TyCtxt};

#[derive(Clone, Copy)]
enum Direct {
    ZeroSized,
    Scalar,
}

fn classify<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>, fuel: usize) -> Option<Direct> {
    if fuel == 0 { return None; }
    match ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => Some(Direct::Scalar),
        ty::FnDef(_, args) if args.bound_vars().is_empty() && args.skip_binder().is_empty() =>
            Some(Direct::ZeroSized),
        ty::Tuple(fields) => {
            let kinds = fields.iter().map(|field| classify(tcx, field, fuel - 1))
                .collect::<Option<Vec<_>>>()?;
            if kinds.iter().all(|kind| matches!(kind, Direct::ZeroSized)) {
                Some(Direct::ZeroSized)
            } else if kinds.len() == 1 && tcx.data_layout.aggregate_align.bytes() == 1 {
                Some(Direct::Scalar)
            } else { None }
        }
        ty::Array(element, count) => {
            let count = count.try_to_target_usize(tcx)?;
            if count == 0 || matches!(classify(tcx, *element, fuel - 1)?, Direct::ZeroSized) {
                Some(Direct::ZeroSized)
            } else { None }
        }
        ty::Adt(definition, arguments) if definition.is_struct() &&
            !definition.repr().simd() && !definition.repr().scalable() => {
            let kinds = definition.all_fields().map(|field| {
                let field = tcx.type_of(field.did).instantiate(tcx, *arguments).skip_norm_wip();
                classify(tcx, field, fuel - 1)
            }).collect::<Option<Vec<_>>>()?;
            if kinds.iter().all(|kind| matches!(kind, Direct::ZeroSized)) {
                Some(Direct::ZeroSized)
            } else if kinds.len() == 1 && !definition.repr().c() &&
                definition.repr().align.is_none() && definition.repr().pack.is_none() &&
                tcx.data_layout.aggregate_align.bytes() == 1 {
                Some(Direct::Scalar)
            } else { None }
        }
        _ => None,
    }
}

pub(super) fn eligible<'tcx>(tcx: TyCtxt<'tcx>, value: &rustc_middle::mir::Const<'tcx>) -> bool {
    let rustc_middle::mir::Const::Ty(declared, constant) = value else { return false; };
    let ty::ConstKind::Value(value) = constant.kind() else { return false; };
    *declared == value.ty && classify(tcx, value.ty, 256).is_some()
}
