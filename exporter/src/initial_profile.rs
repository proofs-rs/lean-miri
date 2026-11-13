//! Complete initial allocations plus frozen typed query caches. Capture is the
//! first compiler operation after diagnostics; raw body/source acquisition and
//! ordinary exporter demands occur afterwards. All late effects are observations,
//! never merged into initial state or used to answer a frozen query-cache miss.
use rustc_middle::{ty::TyCtxt,mir::interpret::GlobalAlloc};
use rustc_hir::def_id::DefId;
use serde_json::{Value,json};
use crate::{ExportContext,initial_profile_config::Config,initial_query_cache as cache,
    compiler_initial_snapshot as snapshot,ctfe_initial_global_payload as payload,
    ctfe_initial_global_symbols as symbols};

pub(super) struct FrozenProfile<'tcx> {
    pub allocations:snapshot::Frozen<'tcx>,
    pub caches:cache::AllFrozen<'tcx>,
    selected:Vec<DefId>,
}
pub(super) fn capture<'tcx>(tcx:TyCtxt<'tcx>,config:Config)->Result<Option<FrozenProfile<'tcx>>,String> {
    if !config.enabled {return Ok(None)}
    let allocations=snapshot::capture(tcx)?;
    let caches=cache::AllFrozen::capture(tcx);
    if caches.has_external_cache() {return Err("initial query profile cannot import incremental/on-disk cache restoration".into())}
    let effects=snapshot::acquisition_effects(tcx,&allocations)?;
    if effects["unchanged"]!=json!(true) {return Err("initial typed-cache capture mutated allocation identity state".into())}
    eprintln!("LEAN_MIRI_INITIAL_PROFILE_FROZEN\t{}",json!({"phase":"before_export_queries","typed_cache_counts":caches.counts(),"allocation_capture_effects":effects}));
    // Resolving an explicitly selected source path happens AFTER the complete
    // freeze. Its cache result is nevertheless selected from `caches` above.
    let definitions=tcx.hir_crate_items(()).definitions().map(|id|id.to_def_id()).collect::<Vec<_>>();
    let mut selected=Vec::new();
    for path in config.selected_paths {
        let matches=definitions.iter().copied().filter(|id|tcx.def_path_str(*id)==path).collect::<Vec<_>>();
        let [definition]=matches.as_slice() else {return Err(format!("selected initial query-cache source is absent or ambiguous: {path}"))};
        selected.push(*definition);
    }
    Ok(Some(FrozenProfile {allocations,caches,selected}))
}
impl<'tcx> FrozenProfile<'tcx> {
    /// Seed declaration source references BEFORE the ordinary declaration
    /// worklist. This never registers runtime Item instances or FnAbi answers.
    pub fn source_snapshot(&self,tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Result<Value,String> {
        for definition in &self.selected {crate::def_json(context,*definition);}
        let mut encoder=symbols::Symbols{tcx};
        let bytes=tcx.data_layout.pointer_size().bytes();
        let little=tcx.data_layout.endian==rustc_abi::Endian::Little;
        let result=snapshot::serialize(tcx,&self.allocations,|value,role| {
            let mut result=payload::encode(value,&mut encoder,bytes,little)?;
            if matches!(role,snapshot::EncodeRole::GlobalPayload) {
                if let GlobalAlloc::Static(definition)=value {
                    result.as_object_mut().ok_or("static source payload is not an object")?
                        .insert("static_info".into(),symbols::static_source(tcx,*definition)?);
                }
            }
            Ok(result)
        })?;
        let mut definitions=Vec::new();symbols::definitions(&result,&mut definitions)?;
        for definition in definitions {crate::def_json(context,definition);}
        Ok(result)
    }
    /// Discover demands freely, but answer them only from the frozen cache.
    /// Unsupported selected result types/errors reject explicitly in serialize.
    pub fn selected_tables(&self,tcx:TyCtxt<'tcx>,context:&ExportContext<'tcx>)->Result<Vec<Value>,String> {
        let mut selected=self.selected.clone();
        selected.extend(context.initial_query_demands.iter().copied());
        selected.sort_by_key(|def|(def.krate.as_u32(),def.index.as_u32()));selected.dedup();
        selected.into_iter().map(|definition| {
            if context.definitions.get(&definition).is_none() {return Err("selected memo declaration was not retained in source scope".into())}
            cache::serialize(tcx,&self.caches.selected(definition))
        }).collect()
    }
    pub fn observe_after_export(&self,tcx:TyCtxt<'tcx>)->Result<(),String> {
        let effects=snapshot::acquisition_effects(tcx,&self.allocations)?;
        let late=cache::AllFrozen::capture(tcx);
        eprintln!("LEAN_MIRI_INITIAL_PROFILE_LATE_OBSERVATIONS\t{}",json!({
            "phase":"after_export_queries","initial_cache_counts":self.caches.counts(),
            "observed_late_cache_counts":late.counts(),"allocation_effects":effects,
            "policy":"observations_only_not_initial_state"}));
        Ok(())
    }
}
