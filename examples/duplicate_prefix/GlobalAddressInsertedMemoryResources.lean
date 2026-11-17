import duplicate_prefix.GlobalAddressReuseHistory
namespace DuplicatePrefix.GlobalAddressInsertedMemoryResources
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual local insertion preserves every previous live identifier, including
an identifier that is replaced and nonlocal function/global metadata. -/
theorem live {K} (memory : MemoryState Provenance BorrowTree K)
    (id query : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (initial : memory.isAllocLive query=true) :
    (source_range_insert_live memory id entry).isAllocLive query=true := by
  by_cases same : query=id
  · subst query
    have present:=MemoryCopyBridge.live_any_of_present (source_range_insert_live memory id entry) id entry
      (MemoryCopyBridge.live_lookup_replaced memory id entry)
    simp only [MemoryState.isAllocLive,present,Bool.true_or]
  · unfold_internal ".MemoryState.insertLive"
    simp only [MemoryState.isAllocLive,Bool.or_eq_true,Array.any_eq_true'] at initial ⊢
    rcases initial with ((localLive | extra) | vaList) | global
    · obtain ⟨old,member,equal⟩:=localLive
      apply Or.inl;apply Or.inl;apply Or.inl
      refine ⟨old,Array.mem_push_of_mem (id,entry) (Array.mem_filter.mpr ⟨member,?_⟩),equal⟩
      have eq : old.1=query := by simpa using equal
      simpa only [eq,bne_iff_ne] using same
    · exact Or.inl (Or.inl (Or.inr extra))
    · exact Or.inl (Or.inr vaList)
    · exact Or.inr global

/-- Fresh physical allocation insertion transports the complete address-history
resource bundle before its address is assigned. No successful allocator hook,
Placement, or final resource is assumed. This lemma concerns the actual
insertLive operation; reserveID and init/root hooks remain separate. -/
theorem insert {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId → Size)
    (initial : GlobalAddressReuseResources.State memory addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (fresh : id∉addresses.intToPtrMap.toList.map InverseAddressEntry.allocId) :
    GlobalAddressReuseResources.State (source_range_insert_live memory id entry) addresses generation sizes := by
  refine ⟨⟨⟨?_,initial.resources.recurring.ordered,initial.resources.recurring.unique⟩,
    initial.resources.apart,?_⟩,initial.generationEq,initial.managed,initial.cursor,
    initial.frontier,initial.holes,initial.bounded,initial.pairwise⟩
  · exact ⟨fun row member=>live memory id row.allocId entry (initial.resources.recurring.live.1 row member),
      fun query member=>live memory id query entry (initial.resources.recurring.live.2 query member)⟩
  · intro row member
    apply GlobalAddressLiveSizeFormation.insert_other memory id row.allocId entry
    · intro same
      apply fresh
      apply List.mem_map.mpr
      exact ⟨row,by simpa using member,same⟩
    · exact initial.resources.rows row member
end DuplicatePrefix.GlobalAddressInsertedMemoryResources
