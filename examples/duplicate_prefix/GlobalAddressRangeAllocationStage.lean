import duplicate_prefix.GlobalAddressRangeResources
namespace DuplicatePrefix.GlobalAddressRangeAllocationStage
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressLiveSizeFormation GlobalAddressRangeResources GlobalAddressManagedBumpFormation GlobalAddressBumpRangeFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem insert_live {K} (memory : MemoryState Provenance BorrowTree K) (id query : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (live : memory.isAllocLive query = true) :
    (source_range_insert_live memory id entry).isAllocLive query = true := by
  unfold_internal ".MemoryState.insertLive"
  simp only [MemoryState.isAllocLive,Bool.or_eq_true,Array.any_eq_true'] at live ⊢
  by_cases same : query=id
  · subst query
    exact Or.inl (Or.inl (Or.inl ⟨(id,entry),Array.mem_push.mpr (Or.inr rfl),by simp⟩))
  · rcases live with ((localLive | extra) | vaList) | global
    · obtain ⟨row,member,equal⟩ := localLive
      apply Or.inl;apply Or.inl;apply Or.inl
      refine ⟨row,Array.mem_push.mpr (Or.inl (Array.mem_filter.mpr ⟨member,?_⟩)),equal⟩
      have rowEq : row.1=query := by simpa using equal
      simpa only [rowEq,bne_iff_ne] using same
    · exact Or.inl (Or.inl (Or.inr extra))
    · exact Or.inl (Or.inr vaList)
    · exact Or.inr global

/-- The actual private insertLive stage used by source insertAllocation keeps
all cached ranges and supplier resources for a fresh allocation identity. The
new allocation's future address is not yet cached by this stage. -/
theorem inserted {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (initial : State memory addresses sizes) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (fresh : id ∉ addresses.intToPtrMap.toList.map InverseAddressEntry.allocId) :
    State (source_range_insert_live memory id entry) addresses sizes := by
  refine ⟨⟨?_,initial.recurring.ordered,initial.recurring.unique⟩,initial.apart,?_⟩
  · constructor
    · intro row member
      exact insert_live memory id row.allocId entry (initial.recurring.live.1 row member)
    · intro query member
      exact insert_live memory id query entry (initial.recurring.live.2 query member)
  · intro row member
    apply insert_other memory id row.allocId entry
    · intro same
      exact fresh (List.mem_map.mpr ⟨row,Array.mem_toList_iff.mpr member,same⟩)
    · exact initial.rows row member

/-- The committed allocation insertion followed by actual managed root-address
assignment derives the cached range geometry and metadata needed by empty-slice
classification. Reserved-ID/storage/extra initialization are earlier source
stages, not claimed by this component. -/
theorem insert_and_assign {K} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState) (sizes : AllocId → Size)
    (initial : State memory addresses sizes) (frontier : Frontier addresses.intToPtrMap sizes generation.generator)
    (managed : addresses.addressMode = .managed) (generationEq : addresses.generation = some generation)
    (cursor : generation.generator.nextBaseAddr ≠ 0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (sizeEq : sizes id = entry.allocation.byteSize)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (fresh : id ∉ addresses.intToPtrMap.toList.map InverseAddressEntry.allocId)
    (kind : AddressMemoryKind) (thread : AddressThreadId) (slack : Fin 16)
    (allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true)
    (room : Room generation.generator entry.allocation.byteSize slack) :
    let committed := source_range_insert_live memory id entry
    let output := addresses.addrFromAllocId id (some (info entry.allocation.byteSize kind thread)) (choices slack)
    output.outcome = .ok (.ready (base generation.generator slack)) ∧
      State committed output.state sizes ∧
      Frontier output.state.intToPtrMap sizes (next generation.generator entry.allocation.byteSize slack) := by
  apply GlobalAddressRangeResources.managed_bump (source_range_insert_live memory id entry) addresses generation sizes
    (inserted memory addresses sizes initial id entry fresh) frontier managed generationEq cursor id entry
    (MemoryCopyBridge.live_lookup_replaced memory id entry) sizeEq uncached fresh kind thread slack allowed room
end DuplicatePrefix.GlobalAddressRangeAllocationStage
