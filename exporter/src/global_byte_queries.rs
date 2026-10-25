//! Exact salt lookup against the already exported compiler allocation graph.
//! Probes that allocate a new rustc global are not imported: runtime reservation
//! remains lazy and uses its canonical allocation supply.
use super::*;
pub(super) fn export<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Value {
    let str_type=type_json(context,tcx,tcx.types.str_);
    // `type_json` above may extend type metadata, but this producer never
    // mutates allocation_ids. Borrow the completed allocation map instead of
    // cloning the full catalog on every fixpoint round.
    let original=&context.allocation_ids;
    let mut covered=original.values().copied().collect::<Vec<_>>();
    covered.sort_unstable();
    // The hex key is the serialized content. Retain one source allocation as
    // the representative and re-borrow its bytes during the salt probes;
    // keeping a second Vec for every unique global needlessly duplicates all
    // immutable string bytes at once.
    let mut contents=BTreeMap::<String,AllocId>::new();
    for alloc in original.keys() {
        let Some(GlobalAlloc::Memory(memory))=tcx.try_get_global_alloc(*alloc) else {continue};
        let allocation=memory.inner();
        if allocation.mutability!=rustc_ast::Mutability::Not || allocation.align.bytes()!=1 {continue}
        if allocation.provenance().ptrs().iter().next().is_some() {continue}
        let range=rustc_middle::mir::interpret::AllocRange::from(rustc_abi::Size::ZERO..allocation.size());
        if !allocation.init_mask().range_as_init_chunks(range).all(|chunk|chunk.is_init()) {continue}
        let bytes=allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
        contents.entry(bytes_hex(bytes)).or_insert(*alloc);
    }
    let candidates=contents.into_iter().map(|(hex,representative)|{
        let Some(GlobalAlloc::Memory(memory))=tcx.try_get_global_alloc(representative) else {
            unreachable!("global-byte representative must remain allocated")
        };
        let allocation=memory.inner();
        let bytes=allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
        let salts=(0..32usize).map(|salt|{
            // The rustc API accepts `Into<Cow<[u8]>>`; borrowing avoids a
            // full byte-vector clone for every salt without changing probes.
            let selected=tcx.allocate_bytes_dedup(bytes,salt);
            json!({"salt":salt,"existing_allocation":original.get(&selected).map(|id|json!({"allocation_id":id}))})
        }).collect::<Vec<_>>();
        json!({"bytes_hex":hex,"salts":salts})
    }).collect::<Vec<_>>();
    // No allocation_ref call here: the covered graph is unchanged by probing.
    json!({"status":"supported","salt_count":32,"str_type":str_type,
        "covered_allocation_ids":covered,"candidates":candidates})
}
