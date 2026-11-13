//! Exact raw symbolic identities for frozen GlobalAlloc keys and payloads.
//! No instance selection, normalization, body lookup or ABI query occurs here.
use rustc_middle::ty::{self,TyCtxt};
use rustc_hir::def_id::DefId;
use serde_json::{Value,json};
pub(super) struct Symbols<'tcx> { pub tcx:TyCtxt<'tcx> }
fn definition(def:DefId)->Value { json!({"crate":def.krate.as_u32(),"index":def.index.as_u32()}) }
fn parse(source:Result<String,String>)->Result<Value,String> {
    serde_json::from_str(&source?).map_err(|error|format!("invalid raw snapshot symbol material: {error}"))
}
impl<'tcx> super::ctfe_initial_global_payload::Symbols<'tcx> for Symbols<'tcx> {
    fn ty(&mut self,value:ty::Ty<'tcx>)->Result<Value,String> { parse(super::generic_material::type_tree(self.tcx,value)) }
    fn predicates(&mut self,values:&'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>)->Result<Value,String> {
        Ok(Value::Array(values.iter().map(|value|parse(super::generic_material::predicate_tree(self.tcx,value))).collect::<Result<_,_>>()?))
    }
    fn instance(&mut self,value:ty::Instance<'tcx>)->Result<Value,String> {
        use ty::{InstanceKind as I,ShimKind as S};
        let kind=match value.def {
            I::Item(def)=>json!({"kind":"item","definition":definition(def)}),
            I::Intrinsic(def)=>json!({"kind":"intrinsic","definition":definition(def)}),
            I::LlvmIntrinsic(def)=>json!({"kind":"llvm_intrinsic","definition":definition(def)}),
            I::Virtual(def,slot)=>json!({"kind":"virtual","definition":definition(def),"dispatch_slot":slot}),
            I::Shim(shim)=>json!({"kind":"shim","shim":match shim {
                S::VTable(def)=>json!({"kind":"vtable","definition":definition(def)}),
                S::Reify(def,reason)=>json!({"kind":"reify","definition":definition(def),"reason":reason.map(|reason|match reason {ty::ReifyReason::FnPtr=>"function_pointer",ty::ReifyReason::Vtable=>"vtable"})}),
                S::FnPtr(def,ty)=>json!({"kind":"function_pointer","definition":definition(def),"function_type":self.ty(ty)?}),
                S::ClosureOnce{call_once,closure,track_caller}=>json!({"kind":"closure_once","call_once_definition":definition(call_once),"closure_definition":definition(closure),"track_caller":track_caller}),
                S::ConstructCoroutineInClosure{coroutine_closure_def_id,receiver_by_ref}=>json!({"kind":"construct_coroutine_in_closure","definition":definition(coroutine_closure_def_id),"receiver_by_ref":receiver_by_ref}),
                S::ThreadLocal(def)=>json!({"kind":"thread_local","definition":definition(def)}),
                S::FutureDropPoll(def,proxy,implementation)=>json!({"kind":"future_drop_poll","definition":definition(def),"proxy_type":self.ty(proxy)?,"implementation_type":self.ty(implementation)?}),
                S::DropGlue(def,ty)=>json!({"kind":"drop_glue","definition":definition(def),"drop_type":ty.map(|ty|self.ty(ty)).transpose()?}),
                S::Clone(def,ty)=>json!({"kind":"clone","definition":definition(def),"clone_type":self.ty(ty)?}),
                S::FnPtrAsPtr(def,ty)=>json!({"kind":"function_pointer_as_pointer","definition":definition(def),"function_type":self.ty(ty)?}),
                S::FnPtrFromPtr(def,ty)=>json!({"kind":"function_pointer_from_pointer","definition":definition(def),"function_type":self.ty(ty)?}),
                S::AsyncDropGlueCtor(def,ty)=>json!({"kind":"async_drop_glue_constructor","definition":definition(def),"drop_type":self.ty(ty)?}),
                S::AsyncDropGlue(def,ty)=>json!({"kind":"async_drop_glue","definition":definition(def),"coroutine_type":self.ty(ty)?}),
            }}),
        };
        let arguments=value.args.iter().map(|argument|parse(super::generic_material::argument(self.tcx,argument))).collect::<Result<Vec<_>,_>>()?;
        Ok(json!({"kind":kind,"arguments":arguments}))
    }
}

/// Close physical source declaration references before the ordinary material
/// declaration worklist. No compiler global or resolved instance is looked up.
pub(super) fn definitions(value:&Value,out:&mut Vec<DefId>)->Result<(),String> {
    match value {
        Value::Object(fields)=> {
            if let (Some(crate_index),Some(index))=(fields.get("crate"),fields.get("index")) {
                let crate_index=crate_index.as_u64().and_then(|v|u32::try_from(v).ok()).ok_or("snapshot source crate ID is not u32")?;
                let index=index.as_u64().and_then(|v|u32::try_from(v).ok()).ok_or("snapshot source definition index is not u32")?;
                out.push(DefId {krate:rustc_hir::def_id::CrateNum::from_u32(crate_index),index:rustc_hir::def_id::DefIndex::from_u32(index)});
            }
            for child in fields.values() { definitions(child,out)?; }
        }
        Value::Array(values)=>for child in values {definitions(child,out)?;},
        _=>{},
    }
    Ok(())
}

/// Raw declaration material, separate from the Static dedup key. Effective
/// mutability and layout must be derived by the consuming World, never queried.
pub(super) fn static_source<'tcx>(tcx:TyCtxt<'tcx>,definition:DefId)->Result<Value,String> {
    let rustc_hir::def::DefKind::Static{nested,mutability,..}=tcx.def_kind(definition)
        else {return Err("frozen Static key does not name a static declaration".into())};
    let source_type=if nested {None} else {
        let value=tcx.type_of(definition).no_bound_vars().ok_or("static source type unexpectedly generic")?;
        Some(parse(super::generic_material::type_tree(tcx,value))?)
    };
    Ok(json!({"source_type":source_type,
        "declared_mutability":if mutability.is_mut(){"mutable"}else{"immutable"},
        "is_static":tcx.is_static(definition),"is_foreign_item":tcx.is_foreign_item(definition),
        "nested":nested,"thread_local":tcx.is_thread_local_static(definition),
        "explicit_align_bytes":tcx.codegen_fn_attrs(definition).alignment.map(|align|align.bytes())}))
}
