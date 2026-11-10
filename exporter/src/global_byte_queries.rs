//! Exact salt lookup against the already exported compiler allocation graph.
//! Probes that allocate a new rustc global are not imported: runtime reservation
//! remains lazy and uses its canonical allocation supply.
use super::*;
#[derive(serde::Serialize)]
pub(super) struct Queries {
    salt_count: usize,
    str_type: u64,
    covered_allocation_ids: Vec<u64>,
    candidates: Vec<Candidate>,
}
#[derive(serde::Serialize)]
struct Candidate {
    bytes_hex: String,
    salts: Vec<Salt>,
}
#[derive(serde::Serialize)]
struct Salt {
    salt: usize,
    existing_allocation: Option<u64>,
}
pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut State,
) -> Result<(), String> {
    if state.str_type.is_none() {
        state.str_type = Some(type_json(context, tcx, tcx.types.str_)?);
    }
    // This producer never mutates allocation_ids. Inspect only the newly
    // discovered allocation suffix, retaining completed content probes.
    let original = &context.allocation_ids;
    // The hex key is the serialized content. Retain one source allocation as
    // the representative and re-borrow its bytes during the salt probes;
    // keeping a second Vec for every unique global needlessly duplicates all
    // immutable string bytes at once.
    let mut contents = BTreeMap::<String, AllocId>::new();
    for index in state.allocations..original.len() {
        let alloc = original.key(index).unwrap();
        let Some(GlobalAlloc::Memory(memory)) = tcx.try_get_global_alloc(*alloc) else {
            continue;
        };
        let allocation = memory.inner();
        if allocation.mutability != rustc_ast::Mutability::Not || allocation.align.bytes() != 1 {
            continue;
        }
        if allocation.provenance().ptrs().iter().next().is_some() {
            continue;
        }
        let range = rustc_middle::mir::interpret::AllocRange::from(
            rustc_abi::Size::ZERO..allocation.size(),
        );
        if !allocation
            .init_mask()
            .range_as_init_chunks(range)
            .all(|chunk| chunk.is_init())
        {
            continue;
        }
        let bytes = allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
        let key = bytes_hex(bytes);
        if !state.candidates.contains_key(&key) {
            contents.entry(key).or_insert(*alloc);
        }
    }
    state.allocations = original.len();
    let candidates = contents
        .into_iter()
        .map(|(hex, representative)| {
            let Some(GlobalAlloc::Memory(memory)) = tcx.try_get_global_alloc(representative) else {
                unreachable!("global-byte representative must remain allocated")
            };
            let allocation = memory.inner();
            let bytes =
                allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
            let salts = (0..32usize)
                .map(|salt| {
                    // The rustc API accepts `Into<Cow<[u8]>>`; borrowing avoids a
                    // full byte-vector clone for every salt without changing probes.
                    tcx.allocate_bytes_dedup(bytes, salt)
                })
                .collect::<Vec<_>>();
            (hex, salts)
        })
        .collect::<Vec<_>>();
    // No allocation_ref call here: the covered graph is unchanged by probing.
    state.candidates.extend(candidates);
    Ok(())
}

// A salt probe may reserve a compiler allocation before another producer
// discovers it. Resolve graph membership only against the completed pool.
#[derive(Default)]
pub(super) struct State {
    allocations: usize,
    str_type: Option<u64>,
    candidates: BTreeMap<String, Vec<AllocId>>,
}
pub(super) fn finish(facts: State, context: &ExportContext<'_>) -> Queries {
    let mut covered = context.allocation_ids.values().copied().collect::<Vec<_>>();
    covered.sort_unstable();
    Queries {
        salt_count: 32,
        str_type: facts.str_type.expect("global-byte discovery initialized str"),
        covered_allocation_ids: covered,
        candidates: facts.candidates.into_iter().map(|(bytes_hex, selected)| Candidate {
            bytes_hex,
            salts: selected.into_iter().enumerate().map(|(salt, selected)| Salt {
                salt,
                existing_allocation: context.allocation_ids.get(&selected).copied(),
            }).collect(),
        }).collect(),
    }
}
