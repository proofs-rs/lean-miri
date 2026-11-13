//! Complete, read-only allocation state captured before exporter query demands.
//!
//! This module requires the pinned compiler's audited snapshot accessor. It is
//! separate from allocator_world's prepared post-export sentinel/key-probe policy.
//! A serial compiler boundary is mandatory. Frozen payloads, including relocation
//! and initialization state, must be encoded directly; looking up a source ID in
//! the later TyCtxt would silently substitute a different allocation state.
use rustc_middle::{mir::interpret::{AllocId, GlobalAlloc}, ty::TyCtxt};
use serde_json::{Value, json};
use std::collections::{HashMap, HashSet};

const SCHEMA: &str = "rustc_initial_global_snapshot_v1";
const PHASE: &str = "before_export_queries";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Frozen<'tcx> {
    next: u64,
    globals: Vec<(AllocId, GlobalAlloc<'tcx>)>,
    dedup: Vec<(GlobalAlloc<'tcx>, usize, AllocId)>,
}

fn observe<'tcx>(tcx: TyCtxt<'tcx>) -> Result<Frozen<'tcx>, String> {
    if tcx.sess.opts.unstable_opts.threads.as_deref() != Some("1") {
        return Err("complete initial snapshot requires explicit -Zthreads=1 and a no-writer boundary".into());
    }
    let (next, mut globals, mut dedup) = tcx.lean_miri_complete_allocation_identity_snapshot();
    if next == 0 { return Err("complete allocation frontier is zero".into()); }
    let mut by_id = HashMap::new();
    for (id, value) in &globals {
        if id.0.get() >= next || by_id.insert(*id, value).is_some() {
            return Err("complete allocation globals contain an out-of-frontier or duplicate identity".into());
        }
    }
    let mut keys = HashSet::new();
    for (key, salt, id) in &dedup {
        if !keys.insert((key, *salt)) || by_id.get(id).copied() != Some(key) {
            return Err("complete allocation dedup key/salt has a duplicate or inconsistent global binding".into());
        }
    }
    // Ordering is a wire convention only; allocation identity and key equality
    // remain the compiler's actual typed values, never serializer graph IDs.
    globals.sort_by_key(|(id, _)| id.0.get());
    dedup.sort_by_key(|(_, salt, id)| (id.0.get(), *salt));
    Ok(Frozen { next, globals, dedup })
}

pub(super) fn capture<'tcx>(tcx: TyCtxt<'tcx>) -> Result<Frozen<'tcx>, String> {
    let frozen = observe(tcx)?;
    if frozen != observe(tcx)? {
        return Err("complete initial allocation snapshot changed across the serial capture boundary".into());
    }
    Ok(frozen)
}

fn effects<'tcx>(before: &Frozen<'tcx>, after: &Frozen<'tcx>) -> Value {
    let added_globals: Vec<_> = after.globals.iter()
        .filter(|(id, _)| !before.globals.iter().any(|(old, _)| old == id))
        .map(|(id, _)| id.0.get()).collect();
    let removed_globals: Vec<_> = before.globals.iter()
        .filter(|(id, _)| !after.globals.iter().any(|(new, _)| new == id))
        .map(|(id, _)| id.0.get()).collect();
    let changed_globals: Vec<_> = before.globals.iter()
        .filter(|(id, value)| after.globals.iter().any(|(new_id, new_value)| new_id == id && new_value != value))
        .map(|(id, _)| id.0.get()).collect();
    json!({"unchanged": before == after,
        "before_next_source_alloc_id": before.next, "after_next_source_alloc_id": after.next,
        "added_global_source_ids": added_globals, "removed_global_source_ids": removed_globals,
        "changed_global_source_ids": changed_globals,
        "before_dedup_count": before.dedup.len(), "after_dedup_count": after.dedup.len(),
        "dedup_changed": before.dedup != after.dedup})
}

/// Encode every frozen global and every actual typed dedup key. The callback
/// must encode the supplied value, retaining memory bytes/init/provenance/align/
/// mutability and symbolic function/static/vtable/type identities, or return an
/// explicit error. It must never reread a current global by ID or evaluate it.
/// Serialization effects are reported separately from the initial state.
#[derive(Clone,Copy)]
pub(super) enum EncodeRole { GlobalPayload, DedupKey }

pub(super) fn serialize<'tcx>(tcx: TyCtxt<'tcx>, frozen: &Frozen<'tcx>,
    mut encode: impl FnMut(&GlobalAlloc<'tcx>,EncodeRole) -> Result<Value, String>) -> Result<Value, String> {
    let before_serialization = observe(tcx)?;
    let globals: Vec<_> = frozen.globals.iter().map(|(id, value)|
        Ok(json!({"source_alloc_id": id.0.get(), "value": encode(value,EncodeRole::GlobalPayload)?})))
        .collect::<Result<_, String>>()?;
    let dedup: Vec<_> = frozen.dedup.iter().map(|(key, salt, id)|
        Ok(json!({"key": encode(key,EncodeRole::DedupKey)?, "salt": *salt as u64, "source_alloc_id": id.0.get()})))
        .collect::<Result<_, String>>()?;
    let after_serialization = observe(tcx)?;
    Ok(json!({"schema": SCHEMA, "phase": PHASE,
        "next_source_alloc_id": frozen.next,
        "global_count": globals.len(), "dedup_count": dedup.len(),
        "globals": globals, "dedup": dedup,
        "capture_to_serialization_effects": effects(frozen, &before_serialization),
        "serialization_effects": effects(&before_serialization, &after_serialization)}))
}

/// Isolated effects of a raw-body acquisition interval, never initial state.
pub(super) fn acquisition_effects<'tcx>(tcx:TyCtxt<'tcx>,before:&Frozen<'tcx>)->Result<Value,String> {
    Ok(effects(before,&observe(tcx)?))
}

/// Read-only query-cache membership; never requests, restores or evaluates a value.
pub(super) fn selected_query_cache<'tcx>(tcx:TyCtxt<'tcx>,definition:rustc_hir::def_id::DefId)->Value {
    use rustc_middle::{query::QueryCache,ty};
    let instance=ty::Instance{def:ty::InstanceKind::Item(definition),args:ty::List::empty()};
    let id=rustc_middle::mir::interpret::GlobalId{instance,promoted:None};
    let codegen=ty::TypingEnv::fully_monomorphized();
    let post=ty::TypingEnv::new(codegen.param_env,ty::TypingMode::PostAnalysis);
    let codegen_key=codegen.as_query_input(id);
    let post_key=post.as_query_input(id);
    json!({"schema":"selected_ctfe_query_cache_v1","phase":"immediately_after_initial_freeze",
        "source_definition":{"crate":definition.krate.as_u32(),"index":definition.index.as_u32()},
        "arguments":[],"promoted":null,"param_env_count":codegen.param_env.caller_bounds().count(),
        "codegen_value_present":tcx.query_system.query_vtables.eval_to_const_value_raw.cache.lookup(&codegen_key).is_some(),
        "codegen_allocation_present":tcx.query_system.query_vtables.eval_to_allocation_raw.cache.lookup(&codegen_key).is_some(),
        "post_analysis_value_present":tcx.query_system.query_vtables.eval_to_const_value_raw.cache.lookup(&post_key).is_some(),
        "post_analysis_allocation_present":tcx.query_system.query_vtables.eval_to_allocation_raw.cache.lookup(&post_key).is_some(),
        "incremental_enabled":tcx.sess.opts.incremental.is_some(),
        "on_disk_cache_enabled":tcx.query_system.on_disk_cache.is_some()})
}
pub(super) fn require_fresh_query_cache(observation:&Value)->Result<(),String> {
    for key in ["codegen_value_present","codegen_allocation_present","post_analysis_value_present","post_analysis_allocation_present","incremental_enabled","on_disk_cache_enabled"] {
        if observation.get(key).and_then(Value::as_bool)!=Some(false) {
            return Err(format!("raw CTFE fresh-query scope unsupported: {observation}"));
        }
    }
    Ok(())
}
