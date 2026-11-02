import duplicate_prefix.GlobalAddressBaseCacheFormation
import duplicate_prefix.OrdinaryPointerCacheBoundary

namespace DuplicatePrefix.OrdinaryAddressCacheFormation
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual address registration creates the exact base lookup consumed by the
call-time adapter. This holds even if later inverse-map insertion fails; that
failure is NOT classified as successful execution. No final lookup or operation
success is assumed. Existing insertion normalization is reused. -/
theorem registered_base (addresses : GlobalAddressState) (id : AllocId) (base : UInt64)
    (fresh : addresses.baseAddr.find? (fun row => row.allocId == id) = none) :
    (addresses.cacheAddress id base).state.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩ := by
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.insertBase"
  simp only [fresh, Option.map_none]
  split
  · exact GlobalAddressBaseCacheFormation.base_insert_same _ _ _
  · split
    · split <;> exact GlobalAddressBaseCacheFormation.base_insert_same _ _ _
    · split <;> exact GlobalAddressBaseCacheFormation.base_insert_same _ _ _

/-- Registration always leaves a base row for its allocation. On a duplicate
registration it retains the old coherent row and still reports its actual
error; this assertion does not promote that error to a successful call. Raw
find semantics supplies identity coherence, so no global uniqueness premise
is needed merely to establish this selected lookup. -/
theorem registration_has_base (addresses : GlobalAddressState) (id : AllocId) (base : UInt64) :
    ∃ known, (addresses.cacheAddress id base).state.baseAddr.find?
      (fun row => row.allocId == id) = some ⟨id, known⟩ := by
  cases found : addresses.baseAddr.find? (fun row => row.allocId == id) with
  | none => exact ⟨base, registered_base addresses id base found⟩
  | some row =>
    have identity : row.allocId = id := by
      have selected := Array.find?_some found
      simpa using selected
    have shape : row = (⟨id, row.address⟩ : BaseAddressEntry) := by
      cases row
      simp_all
    refine ⟨row.address, ?_⟩
    unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [found, Option.map_some]
    exact found.trans (congrArg some shape)

/-- Cache membership for a freshly registered concrete pointer follows from
registration data. The actual fixed resolver then normalizes its offset.
Neither heap liveness nor ownership follows from address registration. -/
theorem registered_resolution (addresses : GlobalAddressState) (id : AllocId)
    (base offset : UInt64) (tag : BorTag) (accessSize : Int64)
    (lookup : AddressLookupHooks)
    (fresh : addresses.baseAddr.find? (fun row => row.allocId == id) = none) :
    (addresses.cacheAddress id base).state.ptrGetAlloc
      (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset)))
      accessSize lookup ⟨Size.ofBytes 8⟩ = .ok (some (id, Size.ofBytes offset)) :=
  MemoryCopyBridge.ptr_get_alloc_cached _ id tag base offset accessSize lookup _ rfl
    (registered_base addresses id base fresh)

/-- A real managed allocation-address operation derives both successful
assignment AND the adapter's cachedBase field from raw geometry and resource
premises. The existing allocator theorem supplies success; it is not a premise.
This selected no-reuse branch admits arbitrary legal slack and alignment.
It does not establish coverage of every allocator choice or all machine WF. -/
theorem live_managed_no_reuse_assignment {K : Type}
    (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (sizes : AllocId → Size)
    (apart : WildcardEmptyFamilyFormation.Apart addresses.intToPtrMap sizes)
    (frontier : GlobalAddressBumpRangeFormation.Frontier addresses.intToPtrMap sizes generation.generator)
    (managed : addresses.addressMode = .managed) (generationEq : addresses.generation = some generation)
    (cursor : generation.generator.nextBaseAddr ≠ 0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (live : memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (sizeEq : sizes id = entry.allocation.byteSize)
    (valid : entry.allocation.align.pow2 ≤ 29)
    (fresh : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (kind : AddressMemoryKind) (thread : AddressThreadId) (slack : Fin 16)
    (allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true)
    (room : GlobalAddressAlignedBumpFormation.Room generation.generator entry.allocation.byteSize entry.allocation.align slack) :
    let result := addresses.addrFromAllocId id
      (some (GlobalAddressAlignedManagedFormation.info entry.allocation.byteSize entry.allocation.align kind thread))
      (GlobalAddressAlignedManagedFormation.choices slack)
    let base := GlobalAddressAlignedBumpFormation.base generation.generator entry.allocation.align slack
    memory.getAllocInfo id = .ok
      ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩ ∧
      result.outcome = .ok (.ready base) ∧
      result.state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩ := by
  dsimp only
  have source := (GlobalAddressAlignedManagedFormation.source addresses generation sizes apart frontier
    managed generationEq cursor id entry.allocation.byteSize sizeEq entry.allocation.align valid fresh kind thread slack allowed room).1
  refine ⟨MemoryCopyBridge.live_alloc_info memory id entry live, ?_, ?_⟩
  · rw [source]
  · rw [source]
    exact registered_base _ id _ fresh

end DuplicatePrefix.OrdinaryAddressCacheFormation
