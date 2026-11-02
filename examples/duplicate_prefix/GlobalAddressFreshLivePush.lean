import duplicate_prefix.GlobalAddressInsertedMemoryResources
namespace DuplicatePrefix.GlobalAddressFreshLivePush
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- A reserve-derived absent physical identifier makes the production
allocateConfigured push exactly the private lifecycle insertLive operation.
Inverse-map freshness alone does not establish this physical absence. -/
theorem exact_insert {K} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (absent : memory.live.find? (fun row=>row.1==id)=none) :
    {memory with live:=memory.live.push (id,entry)}=source_range_insert_live memory id entry := by
  have filtered : memory.live.filter (fun row=>row.1 != id)=memory.live := by
    apply Array.filter_eq_self.mpr
    intro row member
    have different:=Array.find?_eq_none.mp absent row member
    simpa using different
  unfold_internal ".MemoryState.insertLive"
  rw [filtered]

/-- Production fresh push preserves the full existing address resources. Both
reserve-derived physical absence and inverse identity freshness are explicit
source conditions; the successor resource is derived. -/
theorem resources {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State memory addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (absent : memory.live.find? (fun row=>row.1==id)=none)
    (fresh : id∉addresses.intToPtrMap.toList.map InverseAddressEntry.allocId) :
    GlobalAddressReuseResources.State {memory with live:=memory.live.push (id,entry)} addresses generation sizes := by
  rw [exact_insert memory id entry absent]
  exact GlobalAddressInsertedMemoryResources.insert memory addresses generation sizes initial id entry fresh
end DuplicatePrefix.GlobalAddressFreshLivePush
