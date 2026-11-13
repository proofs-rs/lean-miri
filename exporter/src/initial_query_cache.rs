//! Exact initial selected-key cache state. No provider is invoked here.
use rustc_middle::{ty::{self,TyCtxt},query::{QueryCache,erase::restore_val},mir::{ConstValue,ConstAlloc,interpret::{GlobalId,ErrorHandled,Scalar}}};
use serde_json::{Value,json};
#[derive(Clone)]
pub(crate) enum Answer<'tcx> { Value(Result<ConstValue,ErrorHandled>), Allocation(Result<ConstAlloc<'tcx>,ErrorHandled>) }
#[derive(Clone)]
pub(crate) struct Entry<'tcx> { mode:&'static str, family:&'static str, answer:Option<Answer<'tcx>> }
pub(crate) struct Frozen<'tcx> { pub definition:rustc_hir::def_id::DefId, pub entries:Vec<Entry<'tcx>>, pub membership:Value }
pub(crate) fn capture<'tcx>(tcx:TyCtxt<'tcx>,definition:rustc_hir::def_id::DefId)->Frozen<'tcx> {
    let instance=ty::Instance{def:ty::InstanceKind::Item(definition),args:ty::List::empty()};
    let id=GlobalId{instance,promoted:None};let codegen=ty::TypingEnv::fully_monomorphized();
    let mut entries=Vec::new();
    for (mode,environment) in [("codegen",codegen),("post_analysis",ty::TypingEnv::new(codegen.param_env,ty::TypingMode::PostAnalysis))] {
        let key=environment.as_query_input(id);
        let value=tcx.query_system.query_vtables.eval_to_const_value_raw.cache.lookup(&key)
            .map(|cached| {let value:Result<ConstValue,ErrorHandled>=restore_val(cached.0);Answer::Value(value)});
        entries.push(Entry{mode,family:"value",answer:value});
        let allocation=tcx.query_system.query_vtables.eval_to_allocation_raw.cache.lookup(&key)
            .map(|cached| {let value:Result<ConstAlloc<'tcx>,ErrorHandled>=restore_val(cached.0);Answer::Allocation(value)});
        entries.push(Entry{mode,family:"allocation",answer:allocation});
    }
    Frozen{definition,entries,membership:crate::compiler_initial_snapshot::selected_query_cache(tcx,definition)}
}
pub(crate) fn serialize<'tcx>(tcx:TyCtxt<'tcx>,frozen:&Frozen<'tcx>)->Result<Value,String> {
    let definition=frozen.definition;
    if tcx.generics_of(definition).count()!=0 || !matches!(tcx.def_kind(definition),rustc_hir::def::DefKind::Const|rustc_hir::def::DefKind::AssocConst) {return Err("initial selected cache requires nongeneric Const/AssocConst".into())}
    let ty=tcx.type_of(definition).instantiate_identity().skip_norm_wip();
    if !matches!(ty.kind(),ty::Uint(ty::UintTy::U32)) {return Err("initial selected cache result domain is source u32 only".into())}
    let source_type=serde_json::from_str::<Value>(&crate::generic_material::type_tree(tcx,ty)?).map_err(|e|e.to_string())?;
    let entries=frozen.entries.iter().map(|entry| {
        let result=match &entry.answer {
            None=>Value::Null,
            Some(Answer::Value(Ok(ConstValue::Scalar(Scalar::Int(value))))) if value.size().bytes()==4 =>
                json!({"kind":"ok","value":{"kind":"scalar_int","bits_unsigned":value.to_bits_unchecked().to_string(),"size_bytes":4},"source_type":source_type.clone()}),
            Some(Answer::Allocation(Ok(value))) if matches!(value.ty.kind(),ty::Uint(ty::UintTy::U32))=>
                json!({"kind":"ok","allocation":{"source_alloc_id":value.alloc_id.0.get(),"source_type":serde_json::from_str::<Value>(&crate::generic_material::type_tree(tcx,value.ty)?).map_err(|e|e.to_string())?}}),
            Some(Answer::Value(Err(_)))|Some(Answer::Allocation(Err(_)))=>return Err("initial cached compiler diagnostic is outside selected-u32 import scope; entry is not dropped".to_string()),
            _=>return Err("initial cached result is outside source-u32 scalar/allocation scope; entry is not dropped".to_string()),
        };
        Ok(json!({"key":{"family":entry.family,"typing_env":{"mode":entry.mode,"param_env":[]},"instance":{"kind":{"kind":"item","definition":{"crate":definition.krate.as_u32(),"index":definition.index.as_u32()}},"arguments":[]},"promoted":null},"present":entry.answer.is_some(),"result":result}))
    }).collect::<Result<Vec<_>,String>>()?;
    Ok(json!({"schema":"selected_const_initial_query_cache_v1","phase":"before_export_queries","result_scope":"selected_u32_success_v1","source_definition":{"crate":definition.krate.as_u32(),"index":definition.index.as_u32()},"source_definition_kind":match tcx.def_kind(definition){rustc_hir::def::DefKind::Const=>"const",_=>"associated_const"},"source_type":source_type,"membership":frozen.membership,"slots":entries}))
}

/// Retain every typed key/result BEFORE any exporter acquisition. Later source
/// demands select from this frozen cache, never from a late TyCtxt cache peek.
/// VALTREE is retained for the independent raw type-constant source hook; the
/// current selected-u32 wire admits only VALUE/ALLOCATION, explicitly.
pub(crate) type Key<'tcx> = ty::PseudoCanonicalInput<'tcx,GlobalId<'tcx>>;
pub(crate) struct AllFrozen<'tcx> {
    pub values:Vec<(Key<'tcx>,rustc_middle::mir::interpret::EvalToConstValueResult<'tcx>)>,
    pub allocations:Vec<(Key<'tcx>,rustc_middle::mir::interpret::EvalToAllocationRawResult<'tcx>)>,
    pub valtrees:Vec<(Key<'tcx>,rustc_middle::mir::interpret::EvalToValTreeResult<'tcx>)>,
    incremental:bool,
    on_disk:bool,
}
impl<'tcx> AllFrozen<'tcx> {
    pub fn capture(tcx:TyCtxt<'tcx>)->Self {
        let mut values=Vec::new();
        let mut allocations=Vec::new();
        let mut valtrees=Vec::new();
        tcx.query_system.query_vtables.eval_to_const_value_raw.cache.for_each(&mut |key,value,_| {
            values.push((*key,restore_val(*value)));
        });
        tcx.query_system.query_vtables.eval_to_allocation_raw.cache.for_each(&mut |key,value,_| {
            allocations.push((*key,restore_val(*value)));
        });
        tcx.query_system.query_vtables.eval_to_valtree.cache.for_each(&mut |key,value,_| {
            valtrees.push((*key,restore_val(*value)));
        });
        Self {values,allocations,valtrees,incremental:tcx.sess.opts.incremental.is_some(),on_disk:tcx.query_system.on_disk_cache.is_some()}
    }
    pub fn counts(&self)->[usize;3] { [self.values.len(),self.allocations.len(),self.valtrees.len()] }
    pub fn has_external_cache(&self)->bool {self.incremental || self.on_disk}
    pub fn selected(&self,definition:rustc_hir::def_id::DefId)->Frozen<'tcx> {
        let global=GlobalId{instance:ty::Instance{def:ty::InstanceKind::Item(definition),args:ty::List::empty()},promoted:None};
        let codegen=ty::TypingEnv::fully_monomorphized();
        let mut entries=Vec::new();
        let mut flags=Vec::new();
        for (mode,environment) in [("codegen",codegen),("post_analysis",ty::TypingEnv::new(codegen.param_env,ty::TypingMode::PostAnalysis))] {
            let key=environment.as_query_input(global);
            let value=self.values.iter().find(|(actual,_)|*actual==key).map(|(_,value)|Answer::Value(*value));
            flags.push(value.is_some());entries.push(Entry{mode,family:"value",answer:value});
            let value=self.allocations.iter().find(|(actual,_)|*actual==key).map(|(_,value)|Answer::Allocation(*value));
            flags.push(value.is_some());entries.push(Entry{mode,family:"allocation",answer:value});
        }
        Frozen {definition,entries,membership:json!({"schema":"selected_ctfe_query_cache_v1","phase":"immediately_after_initial_freeze",
            "source_definition":{"crate":definition.krate.as_u32(),"index":definition.index.as_u32()},
            "arguments":[],"promoted":null,"param_env_count":codegen.param_env.caller_bounds().count(),
            "codegen_value_present":flags[0],"codegen_allocation_present":flags[1],
            "post_analysis_value_present":flags[2],"post_analysis_allocation_present":flags[3],
            "incremental_enabled":self.incremental,"on_disk_cache_enabled":self.on_disk})}
    }
}
