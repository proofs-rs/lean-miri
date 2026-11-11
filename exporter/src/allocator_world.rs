//! Opt-in snapshot of the pinned compiler's prepared allocation world.
//!
//! The snapshot is deliberately taken after the ordinary exporter query
//! closure. It records source AllocIds independently of serialization-local
//! graph IDs and closes the exact immutable byte-key domain used by
//! `allocate_bytes_dedup`.
use super::*;
use rustc_middle::mir::interpret::{AllocId, AllocRange, GlobalAlloc};
use std::num::NonZeroU64;

#[derive(Clone, serde::Serialize)]
pub(super) struct DedupKey {
    key_kind: &'static str,
    key_allocation_id: u64,
    salts: Vec<u64>,
}
#[derive(serde::Serialize)]
pub(super) struct Frontier {
    pub last_reserved_source_alloc_id: u64,
    final_sentinel_source_alloc_id: u64,
    next_source_alloc_id: u64,
}
#[derive(serde::Serialize)]
pub(super) struct World {
    schema: &'static str,
    profile: &'static str,
    pub frontier: Frontier,
    global_pool_complete_through: u64,
    raw_pool: Vec<Option<PoolRow>>,
    dedup_catalog: Vec<DedupKey>,
    complete_key_families: [&'static str; 1],
    non_exhaustive_key_families: [&'static str; 5],
}
#[derive(serde::Serialize)]
struct PoolRow {
    kind: &'static str,
    status: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    memory_mutability: Option<&'static str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    memory_align_bytes: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    memory_all_bytes_initialized: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    memory_has_provenance: Option<bool>,
}
impl PoolRow {
    fn new(kind: &'static str, status: &'static str) -> Self {
        Self {
            kind,
            status,
            memory_mutability: None,
            memory_align_bytes: None,
            memory_all_bytes_initialized: None,
            memory_has_provenance: None,
        }
    }
}

struct ByteKey {
    representative: AllocId,
    bytes: Vec<u8>,
    allocations: Vec<AllocId>,
}

/// Exact dedup key identities selected by the exporter's ordinary
/// compiler-demand closure. Probes run inside that closure because
/// serializing an allocation or vtable can discover further demands.
pub(super) struct SelectedKeyProbes<'tcx> {
    function_cursor: usize,
    allocation_cursor: usize,
    vtable_cursor: usize,
    instance_event_cursor: usize,
    pending_statics: Vec<(AllocId, rustc_hir::def_id::DefId)>,
    functions: HashSet<ty::Instance<'tcx>>,
    vtables: HashSet<(
        ty::Ty<'tcx>,
        &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    )>,
    statics: HashSet<rustc_hir::def_id::DefId>,
    type_ids: HashSet<ty::Ty<'tcx>>,
    rows: Vec<DedupKey>,
}

impl<'tcx> SelectedKeyProbes<'tcx> {
    pub(super) fn new() -> Self {
        Self {
            function_cursor: 0,
            allocation_cursor: 0,
            vtable_cursor: 0,
            instance_event_cursor: 0,
            pending_statics: Vec::new(),
            functions: HashSet::new(),
            vtables: HashSet::new(),
            statics: HashSet::new(),
            type_ids: HashSet::new(),
            rows: Vec::new(),
        }
    }

    /// Probe only currently selected, typed source keys. A miss-created map
    /// entry is present in the frozen post-export TCX and therefore seeds a
    /// future runtime hit just like a preexisting map entry.
    pub(super) fn probe_round(
        &mut self,
        tcx: TyCtxt<'tcx>,
        context: &mut ExportContext<'tcx>,
    ) -> Result<(), String> {
        let functions = context
            .fn_pointer_targets
            .suffix(self.function_cursor)
            .to_vec();
        self.function_cursor = context.fn_pointer_targets.len();
        let allocation_end = context.allocation_ids.len();
        let mut new_vtables = Vec::new();
        let mut new_type_ids = Vec::new();
        for index in self.allocation_cursor..allocation_end {
            let alloc = *context.allocation_ids.key(index).unwrap();
            match tcx.try_get_global_alloc(alloc) {
                Some(GlobalAlloc::VTable(input, predicates)) => {
                    new_vtables.push((input, predicates))
                }
                Some(GlobalAlloc::Static(def)) => self.pending_statics.push((alloc, def)),
                Some(GlobalAlloc::TypeId { ty }) => new_type_ids.push(ty),
                _ => {}
            }
        }
        self.allocation_cursor = allocation_end;
        for instance in functions {
            if self.functions.contains(&instance) {
                continue;
            }
            context.register_instance(instance);
            let mut salts = Vec::with_capacity(32);
            let mut key_graph_id = None;
            for salt in 0..32usize {
                let selected = tcx.reserve_and_set_fn_alloc(instance, salt);
                allocation_ref(context, tcx, selected)?;
                let graph_id = supported_global_graph_id(context, selected, "function")?;
                if salt == 0 {
                    key_graph_id = Some(graph_id);
                }
                salts.push(graph_id);
            }
            let key_allocation_id =
                key_graph_id.ok_or_else(|| "function dedup probe omitted salt zero".to_owned())?;
            self.rows.push(DedupKey {
                key_kind: "function",
                key_allocation_id,
                salts,
            });
            self.functions.insert(instance);
        }

        new_vtables.extend(
            context
                .vtable_query_requests
                .suffix(self.vtable_cursor)
                .iter()
                .copied(),
        );
        self.vtable_cursor = context.vtable_query_requests.len();
        let vtables = new_vtables
            .into_iter()
            .map(|key| tcx.erase_and_anonymize_regions(key))
            .collect::<HashSet<_>>();
        let mut vtables =
            vtables
                .into_iter()
                .filter(|(ty, predicates)| !ty.has_param() && !predicates.has_param())
                .filter(|key| !self.vtables.contains(key))
                .map(|(ty, predicates)| -> Result<_, String> {
                    let type_id = *context.type_ids.get(&ty).ok_or_else(|| {
                        "selected vtable key lacks its closed-query type identity".to_owned()
                    })?;
                    let predicate_ids =
                        predicates
                            .iter()
                            .map(|predicate| {
                                context.predicate_ids.get(&predicate).copied().ok_or_else(|| {
                            "selected vtable key lacks its closed-query predicate identity"
                                .to_owned()
                        })
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                    Ok(((type_id, predicate_ids), (ty, predicates)))
                })
                .collect::<Result<Vec<_>, _>>()?;
        vtables.sort_by(|left, right| left.0.cmp(&right.0));
        for ((_, _), (ty, predicates)) in vtables {
            let mut salts = Vec::with_capacity(32);
            let mut key_graph_id = None;
            for salt in 0..32usize {
                let selected = tcx.reserve_and_set_vtable_alloc(ty, predicates, salt);
                allocation_ref(context, tcx, selected)?;
                let graph_id = supported_global_graph_id(context, selected, "vtable")?;
                if salt == 0 {
                    key_graph_id = Some(graph_id);
                }
                salts.push(graph_id);
            }
            let key_allocation_id =
                key_graph_id.ok_or_else(|| "vtable dedup probe omitted salt zero".to_owned())?;
            self.rows.push(DedupKey {
                key_kind: "vtable",
                key_allocation_id,
                salts,
            });
            self.vtables.insert((ty, predicates));
        }

        // Static identities are selected only from exact source AllocIds
        // already present in the ordinary serialized allocation closure.
        // Do not infer static demands from initializer memory or claim the
        // family is exhaustive.
        let mut static_candidates = std::mem::take(&mut self.pending_statics);
        static_candidates.sort_by_key(|(id, _)| raw_id(*id));
        for (observed_id, def) in static_candidates {
            if self.statics.contains(&def) {
                continue;
            }
            let observed_graph_id = context.allocation_ids.get(&observed_id).copied();
            let observed_node =
                observed_graph_id.and_then(|graph_id| context.allocation_ids.definition(graph_id));
            if observed_node.map_or(true, |node| {
                node.kind() != "static" || node.source_alloc_id != raw_id(observed_id)
            }) {
                self.pending_statics.push((observed_id, def));
                continue;
            }

            let selected = tcx.reserve_and_set_static_alloc(def);
            let source_id = raw_id(selected);
            allocation_ref(context, tcx, selected)?;
            let graph_id = supported_global_graph_id(context, selected, "static")?;
            let node = context
                .allocation_ids
                .definition(graph_id)
                .ok_or_else(|| "selected static allocation has no graph node".to_owned())?;
            if node.kind() != "static"
                || node.source_alloc_id != source_id
                || tcx.try_get_global_alloc(selected) != Some(GlobalAlloc::Static(def))
            {
                return Err("selected static key does not match its exact DefId allocation".into());
            }
            self.rows.push(DedupKey {
                key_kind: "static",
                key_allocation_id: graph_id,
                salts: vec![graph_id],
            });
            self.statics.insert(def);
        }

        // TypeId is keyed by the exact Ty at salt zero. A direct `type_id`
        // intrinsic call is a source demand; arbitrary serialized types and
        // `type_id_eq` reads are not. Already-observed TypeId allocations are
        // also exact selected keys.
        let mut type_id_candidates = new_type_ids;
        let event_end = context.instance_events.len();
        for event in self.instance_event_cursor..event_end {
            let instance = context.instance_events[event];
            if context.metadata_only_instances.contains(&instance) {
                continue;
            }
            let ty::InstanceKind::Intrinsic(def) = instance.def else {
                continue;
            };
            let Some(intrinsic) = tcx.intrinsic(def) else {
                continue;
            };
            if intrinsic.name.as_str() == "type_id" {
                type_id_candidates.push(instance.args.type_at(0));
            }
        }
        self.instance_event_cursor = event_end;
        // Pool iteration follows discovery order. Deduplicate without reserving
        // type identities merely to sort candidate keys: only accepted probes
        // serialize their actual TypeId allocation and discover its type.
        let mut seen_candidates = HashSet::new();
        type_id_candidates.retain(|ty| seen_candidates.insert(*ty));
        for ty in type_id_candidates {
            if self.type_ids.contains(&ty) {
                continue;
            }
            if ty.has_erasable_regions()
                || ty.has_non_region_param()
                || ty.has_escaping_bound_vars()
                || ty.has_infer()
                || ty.has_placeholders()
                || ty.references_error()
            {
                // The interpreter's write_type_id requires erasable regions
                // to have been removed and a closed input before it reserves
                // the exact Ty key.
                continue;
            }

            let selected = tcx.reserve_and_set_type_id_alloc(ty);
            let source_id = raw_id(selected);
            allocation_ref(context, tcx, selected)?;
            let graph_id = supported_global_graph_id(context, selected, "type_id")?;
            let node = context
                .allocation_ids
                .definition(graph_id)
                .ok_or_else(|| "selected TypeId allocation has no graph node".to_owned())?;
            if node.kind() != "type_id"
                || node.source_alloc_id != source_id
                || tcx.try_get_global_alloc(selected) != Some(GlobalAlloc::TypeId { ty })
            {
                return Err("selected TypeId key does not match its exact Ty allocation".into());
            }
            self.rows.push(DedupKey {
                key_kind: "type_id",
                key_allocation_id: graph_id,
                salts: vec![graph_id],
            });
            self.type_ids.insert(ty);
        }
        Ok(())
    }
}

pub(super) fn raw_id(id: AllocId) -> u64 {
    id.0.get()
}

fn alloc_id(raw: u64) -> Result<AllocId, String> {
    NonZeroU64::new(raw)
        .map(AllocId)
        .ok_or_else(|| "rustc exposed allocation ID zero".to_owned())
}

struct ByteProjection {
    eligibility: String,
    mutability: &'static str,
    align_bytes: u64,
    all_bytes_initialized: bool,
    has_provenance: bool,
    bytes: Option<Vec<u8>>,
}

fn byte_image(memory: rustc_middle::mir::interpret::ConstAllocation<'_>) -> ByteProjection {
    let allocation = memory.inner();
    let mutability = if allocation.mutability == rustc_ast::Mutability::Not {
        "immutable"
    } else {
        "mutable"
    };
    let align_bytes = allocation.align.bytes();
    let has_provenance = allocation.provenance().ptrs().iter().next().is_some();
    let range = AllocRange::from(rustc_abi::Size::ZERO..allocation.size());
    let all_bytes_initialized = allocation
        .init_mask()
        .range_as_init_chunks(range)
        .all(|chunk| chunk.is_init());
    let eligibility = if mutability != "immutable" {
        "ineligible_mutable"
    } else if align_bytes != 1 {
        "ineligible_alignment"
    } else if has_provenance {
        "ineligible_provenance"
    } else if !all_bytes_initialized {
        "ineligible_uninitialized"
    } else {
        "eligible"
    };
    let bytes = (eligibility == "eligible").then(|| {
        allocation
            .inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len())
            .to_vec()
    });
    ByteProjection {
        eligibility: eligibility.to_owned(),
        mutability,
        align_bytes,
        all_bytes_initialized,
        has_provenance,
        bytes,
    }
}

fn scan_byte_keys<'tcx>(
    tcx: TyCtxt<'tcx>,
    through: u64,
) -> Result<BTreeMap<String, ByteKey>, String> {
    let mut keys = BTreeMap::new();
    for raw in 1..=through {
        let id = alloc_id(raw)?;
        let Some(GlobalAlloc::Memory(memory)) = tcx.try_get_global_alloc(id) else {
            continue;
        };
        let projection = byte_image(memory);
        if projection.eligibility == "eligible" {
            let bytes = projection.bytes.expect("eligible byte image has contents");
            keys.entry(bytes_hex(&bytes))
                .and_modify(|key: &mut ByteKey| key.allocations.push(id))
                .or_insert(ByteKey {
                    representative: id,
                    bytes,
                    allocations: vec![id],
                });
        }
    }
    Ok(keys)
}

fn supported_memory_graph_id<'tcx>(
    context: &ExportContext<'tcx>,
    id: AllocId,
) -> Result<u64, String> {
    let graph_id = context.allocation_ids.get(&id).copied().ok_or_else(|| {
        format!(
            "eligible byte allocation {} has no graph identity",
            raw_id(id)
        )
    })?;
    let node = context
        .allocation_ids
        .definition(graph_id)
        .ok_or_else(|| format!("eligible byte allocation {} has no graph node", raw_id(id)))?;
    if node.kind() != "memory" || node.source_alloc_id != raw_id(id) {
        return Err(format!(
            "eligible byte allocation {} is not a supported source-linked memory node",
            raw_id(id)
        ));
    }
    Ok(graph_id)
}

fn supported_global_graph_id<'tcx>(
    context: &ExportContext<'tcx>,
    id: AllocId,
    expected_kind: &str,
) -> Result<u64, String> {
    let graph_id = context.allocation_ids.get(&id).copied().ok_or_else(|| {
        format!(
            "selected {expected_kind} allocation {} has no graph identity",
            raw_id(id)
        )
    })?;
    let node = context.allocation_ids.definition(graph_id).ok_or_else(|| {
        format!(
            "selected {expected_kind} allocation {} has no graph node",
            raw_id(id)
        )
    })?;
    if node.kind() != expected_kind || node.source_alloc_id != raw_id(id) {
        return Err(format!(
            "selected {expected_kind} allocation {} is not a supported source-linked node",
            raw_id(id)
        ));
    }
    Ok(graph_id)
}

fn kind_name(global: &GlobalAlloc<'_>) -> &'static str {
    match global {
        GlobalAlloc::Memory(_) => "memory",
        GlobalAlloc::Function { .. } => "function",
        GlobalAlloc::VTable(..) => "vtable",
        GlobalAlloc::Static(..) => "static",
        GlobalAlloc::TypeId { .. } => "type_id",
    }
}

fn pool_row<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &ExportContext<'tcx>,
    id: AllocId,
    sentinel: bool,
) -> Result<Option<PoolRow>, String> {
    let raw = raw_id(id);
    if sentinel || tcx.try_get_global_alloc(id).is_none() {
        if !sentinel
            && context
                .allocation_ids
                .get(&id)
                .and_then(|graph_id| context.allocation_ids.definition(*graph_id))
                .is_some_and(|node| node.source_alloc_id == raw)
        {
            return Err(format!(
                "source AllocId {raw} is dangling but has a linked allocation node"
            ));
        }
        return Ok(Some(PoolRow::new("dangling", "dangling")));
    }
    let global = tcx
        .try_get_global_alloc(id)
        .expect("checked present allocation remains present");
    let kind = kind_name(&global);
    let candidate_graph_id = context.allocation_ids.get(&id).copied();
    let supported_graph_id = if let Some(graph_id) = candidate_graph_id {
        let node = context.allocation_ids.definition(graph_id).ok_or_else(|| {
            format!("allocation node {graph_id} for source AllocId {raw} is absent")
        })?;
        if node.kind() != kind || node.source_alloc_id != raw {
            return Err(format!(
                "allocation node {graph_id} disagrees with source AllocId {raw} ({kind})"
            ));
        }
        Some(graph_id)
    } else {
        // An unrequested compiler global still reserves its raw identity; it is
        // not an imported semantic allocation or a failed serialization.
        None
    };
    if supported_graph_id.is_some() {
        return Ok(None);
    }
    let mut row = PoolRow::new(kind, "opaque");
    if let GlobalAlloc::Memory(memory) = global {
        let projection = byte_image(memory);
        // These are direct rustc allocation facts; the Lean decoder applies
        // the closed eligibility predicate rather than trusting a producer
        // supplied eligibility bit.
        row.memory_mutability = Some(projection.mutability);
        row.memory_align_bytes = Some(projection.align_bytes);
        row.memory_all_bytes_initialized = Some(projection.all_bytes_initialized);
        row.memory_has_provenance = Some(projection.has_provenance);
    }
    Ok(Some(row))
}

/// Capture the post-export TCX continuation. Probe-created mappings are
/// present in this prepared world and therefore become runtime hits.
pub(super) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    selected_keys: SelectedKeyProbes<'tcx>,
) -> Result<World, String> {
    let mut catalog = BTreeMap::<String, DedupKey>::new();
    loop {
        // A temporary reserved ID bounds a read-only enumeration of the
        // current pool. AllocMap IDs are monotone and never reused.
        let snapshot = tcx.reserve_alloc_id();
        let keys = scan_byte_keys(tcx, raw_id(snapshot))?;
        for key in keys.values() {
            for id in &key.allocations {
                allocation_ref(context, tcx, *id)?;
                supported_memory_graph_id(context, *id)?;
            }
        }
        let unseen = keys
            .into_iter()
            .filter(|(hex, _)| !catalog.contains_key(hex))
            .collect::<Vec<_>>();
        for (hex, key) in unseen {
            allocation_ref(context, tcx, key.representative)?;
            let key_graph_id = supported_memory_graph_id(context, key.representative)?;
            let mut salts = Vec::with_capacity(32);
            for salt in 0..32usize {
                let selected = tcx.allocate_bytes_dedup(&key.bytes, salt);
                allocation_ref(context, tcx, selected)?;
                let allocation_id = supported_memory_graph_id(context, selected)?;
                salts.push(allocation_id);
            }
            catalog.insert(
                hex,
                DedupKey {
                    key_kind: "byte_memory",
                    key_allocation_id: key_graph_id,
                    salts,
                },
            );
        }
        // Serialization may itself expose compiler globals. Re-scan after
        // materializing every eligible memory row and every probe result; the
        // next loop closes any newly visible byte image. The temporary
        // sentinel is retained as a real dangling source ID in the prefix.
        let check = tcx.reserve_alloc_id();
        let check_keys = scan_byte_keys(tcx, raw_id(check))?;
        let all_keys_catalogued = check_keys.keys().all(|hex| catalog.contains_key(hex));
        let all_images_serialized = check_keys.values().all(|key| {
            key.allocations
                .iter()
                .all(|id| supported_memory_graph_id(context, *id).is_ok())
        });
        if all_keys_catalogued && all_images_serialized {
            break;
        }
    }

    // The final reserved ID is the prepared world's last source allocation.
    // All compiler-global-producing probes and allocation serialization have
    // completed before this point.
    let final_sentinel = tcx.reserve_alloc_id();
    let frontier = raw_id(final_sentinel);
    let next = frontier
        .checked_add(1)
        .ok_or_else(|| "prepared allocator-world frontier cannot be incremented".to_owned())?;
    let final_keys = scan_byte_keys(tcx, frontier)?;
    if final_keys.keys().any(|hex| !catalog.contains_key(hex)) {
        return Err("byte-memory key appeared after allocator-world closure".into());
    }
    if final_keys.values().any(|key| {
        key.allocations
            .iter()
            .any(|id| supported_memory_graph_id(context, *id).is_err())
    }) {
        return Err("eligible byte allocation was not serialized before final sentinel".into());
    }
    let capacity = usize::try_from(frontier)
        .map_err(|_| "prepared allocator-world pool exceeds addressable capacity".to_owned())?;
    let mut raw_pool = Vec::with_capacity(capacity);
    for raw in 1..=frontier {
        let id = alloc_id(raw)?;
        raw_pool.push(pool_row(tcx, context, id, raw == frontier)?);
    }
    Ok(World {
        schema: "rustc_alloc_id_world_v2",
        profile: "prepared_post_export",
        frontier: Frontier {
            last_reserved_source_alloc_id: frontier,
            final_sentinel_source_alloc_id: frontier,
            next_source_alloc_id: next,
        },
        global_pool_complete_through: frontier,
        raw_pool,
        dedup_catalog: catalog.into_values().chain(selected_keys.rows).collect(),
        complete_key_families: ["byte_memory"],
        non_exhaustive_key_families: [
            "function",
            "vtable",
            "static",
            "type_id",
            "memory_const_allocation",
        ],
    })
}
