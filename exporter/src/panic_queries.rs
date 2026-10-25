//! Exact panic language-item and Instance::mono generic-parameter queries.
use super::*;
// machine.rs::unwind_terminate selects one of these independently of MIR
// assert operands. Enqueue the actual mono helper before reachable traversal.
pub(super) fn register_termination_helpers<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>) {
    for item in [
        rustc_attr_ir::LangItem::Panic,
        rustc_attr_ir::LangItem::PanicNounwind,
        rustc_attr_ir::LangItem::PanicCannotUnwind,
        rustc_attr_ir::LangItem::PanicInCleanup,
    ] {
        if let Some(def)=tcx.lang_items().get(item) {
            if !ty::GenericArgs::identity_for_item(tcx,def).has_non_region_param() {
                let instance = ty::Instance::mono(tcx,def);
                context.register_instance(instance);
                let args = if matches!(item,
                    rustc_attr_ir::LangItem::Panic | rustc_attr_ir::LangItem::PanicNounwind) {
                    vec![ty::Ty::new_mut_ptr(tcx, tcx.types.str_)]
                } else {
                    Vec::new()
                };
                super::generated_call_queries::register_target_call(
                    context,
                    tcx,
                    instance,
                    args,
                    tcx.types.unit,
                    rustc_abi::ExternAbi::Rust,
                    ty::TypingEnv::fully_monomorphized(),
                );
            }
        }
    }
}
pub(super) fn export(tcx:TyCtxt<'_>)->Value {
    let items=[
        ("Panic",rustc_attr_ir::LangItem::Panic),
        ("PanicNounwind",rustc_attr_ir::LangItem::PanicNounwind),
        ("PanicCannotUnwind",rustc_attr_ir::LangItem::PanicCannotUnwind),
        ("PanicInCleanup",rustc_attr_ir::LangItem::PanicInCleanup),
        ("PanicBoundsCheck",rustc_attr_ir::LangItem::PanicBoundsCheck),
        ("PanicMisalignedPointerDereference",rustc_attr_ir::LangItem::PanicMisalignedPointerDereference),
        ("PanicAddOverflow",rustc_attr_ir::LangItem::PanicAddOverflow),
        ("PanicSubOverflow",rustc_attr_ir::LangItem::PanicSubOverflow),
        ("PanicMulOverflow",rustc_attr_ir::LangItem::PanicMulOverflow),
        ("PanicDivOverflow",rustc_attr_ir::LangItem::PanicDivOverflow),
        ("PanicRemOverflow",rustc_attr_ir::LangItem::PanicRemOverflow),
        ("PanicNegOverflow",rustc_attr_ir::LangItem::PanicNegOverflow),
        ("PanicShrOverflow",rustc_attr_ir::LangItem::PanicShrOverflow),
        ("PanicShlOverflow",rustc_attr_ir::LangItem::PanicShlOverflow),
        ("PanicDivZero",rustc_attr_ir::LangItem::PanicDivZero),
        ("PanicRemZero",rustc_attr_ir::LangItem::PanicRemZero),
        ("PanicNullPointerDereference",rustc_attr_ir::LangItem::PanicNullPointerDereference),
        ("PanicNullReferenceConstructed",rustc_attr_ir::LangItem::PanicNullReferenceConstructed),
        ("PanicInvalidEnumConstruction",rustc_attr_ir::LangItem::PanicInvalidEnumConstruction),
        ("PanicCoroutineResumed",rustc_attr_ir::LangItem::PanicCoroutineResumed),
        ("PanicAsyncFnResumed",rustc_attr_ir::LangItem::PanicAsyncFnResumed),
        ("PanicAsyncGenFnResumed",rustc_attr_ir::LangItem::PanicAsyncGenFnResumed),
        ("PanicGenFnNone",rustc_attr_ir::LangItem::PanicGenFnNone),
        ("PanicCoroutineResumedPanic",rustc_attr_ir::LangItem::PanicCoroutineResumedPanic),
        ("PanicAsyncFnResumedPanic",rustc_attr_ir::LangItem::PanicAsyncFnResumedPanic),
        ("PanicAsyncGenFnResumedPanic",rustc_attr_ir::LangItem::PanicAsyncGenFnResumedPanic),
        ("PanicGenFnNonePanic",rustc_attr_ir::LangItem::PanicGenFnNonePanic),
        ("PanicCoroutineResumedDrop",rustc_attr_ir::LangItem::PanicCoroutineResumedDrop),
        ("PanicAsyncFnResumedDrop",rustc_attr_ir::LangItem::PanicAsyncFnResumedDrop),
        ("PanicAsyncGenFnResumedDrop",rustc_attr_ir::LangItem::PanicAsyncGenFnResumedDrop),
        ("PanicGenFnNoneDrop",rustc_attr_ir::LangItem::PanicGenFnNoneDrop),
];
    Value::Array(items.into_iter().map(|(name,item)|{
        let definition=tcx.lang_items().get(item);
        let parameters=definition.map(|def|ty::GenericArgs::identity_for_item(tcx,def).iter().map(|arg|match arg.kind(){
            ty::GenericArgKind::Lifetime(_)=>"lifetime",ty::GenericArgKind::Type(_)=>"type_parameter",ty::GenericArgKind::Const(_)=>"const_parameter",
        }).collect::<Vec<_>>());
        json!({"lang_item":name,"status":"supported","definition":definition.map(def_json),"generic_parameters":parameters})
    }).collect())
}
pub(super) fn register_assert<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>,body:&rustc_middle::mir::Body<'tcx>,message:&rustc_middle::mir::AssertMessage<'tcx>) {
    use rustc_middle::mir::AssertKind;
    let definition=match message {
        AssertKind::BoundsCheck{..}=>tcx.lang_items().panic_bounds_check_fn(),
        AssertKind::MisalignedPointerDereference{..}=>tcx.lang_items().panic_misaligned_pointer_dereference_fn(),
        _=>tcx.lang_items().get(message.panic_function()),
    };
    if let Some(def)=definition {
        let args=ty::GenericArgs::identity_for_item(tcx,def);
        if !args.has_non_region_param(){
            let instance=ty::Instance::mono(tcx,def);
            context.register_instance(instance);
            let caller_args = match message {
                AssertKind::BoundsCheck { index, len } => vec![index.ty(body,tcx),len.ty(body,tcx)],
                AssertKind::MisalignedPointerDereference { required, found } =>
                    vec![required.ty(body,tcx),found.ty(body,tcx)],
                _ => Vec::new(),
            };
            super::generated_call_queries::register_target_call(
                context,
                tcx,
                instance,
                caller_args,
                tcx.types.unit,
                rustc_abi::ExternAbi::Rust,
                body.typing_env(tcx),
            );
        }
    }
}
