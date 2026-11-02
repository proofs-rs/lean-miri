import duplicate_prefix.GlobalAddressReuseHistory
import duplicate_prefix.WildcardUnexposedPredecessorAddress
namespace DuplicatePrefix.WildcardEmptyHistoryClassification
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- A raw unresolved source family includes both legacy ordered misses and
unexposed immediate predecessors. The latter still supply actual size metadata. -/
def Unresolved {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (address : UInt64) : Prop :=
  WildcardOrderedMissAddress.Miss addresses address ∨ WildcardUnexposedPredecessorAddress.Geometry memory addresses address

def Cases {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (address : UInt64) (sizes : AllocId → Size) : Prop :=
  Unresolved memory addresses address ∨
    (∃ id base,addresses.exposed.contains id=true ∧
      WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id (sizes id)) ∨
    WildcardMetadataGap.Geometry addresses.intToPtrMap address memory

theorem row_supplier {K} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (size : Size)
    (row : GlobalAddressLiveSizeFormation.Row memory id size) : GlobalAddressLiveErrorExclusion.Supplier memory id := by
  cases row with
  | localRow entry present => exact .localRow entry present
  | globalRow descriptor absent noFunction noVaList present kind => exact .globalRow descriptor absent noFunction noVaList present

/-- Raw recurring resources exhaust every address into unresolved, exposed
exact/interior hit, or metadata-backed gap. The former separate unexposed
interior case becomes a genuine unresolved source branch. -/
theorem state_classify {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId → Size)
    (initial : GlobalAddressReuseResources.State memory addresses generation sizes) (address : UInt64) :
    Cases memory addresses address sizes := by
  have metadata:=GlobalAddressRangeResources.sizeRows memory addresses sizes initial.resources
  rcases WildcardEmptyFamilyFormation.classify memory addresses address sizes initial.resources.recurring.ordered initial.resources.apart metadata with
    miss | hit | gap | ⟨position,row,unexposed,partition,present,inside⟩
  · exact Or.inl (Or.inl miss)
  · exact Or.inr (Or.inl hit)
  · exact Or.inr (Or.inr gap)
  · exact Or.inl (Or.inr ⟨position,row,sizes row.allocId,partition,present,metadata row (Array.mem_of_getElem? present),unexposed⟩)

/-- Actual initialization and arbitrary finite source address histories form
all classification premises internally. No final Apart, order, size supplier,
Cut, family choice, or successful resolver operation is an input. -/
theorem history_classify {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressReuseHistory.History sizes memory addresses) (address : UInt64) :
    Cases memory addresses address sizes := by
  obtain ⟨generation,initial⟩:=GlobalAddressReuseHistory.invariant sizes history
  exact state_classify memory addresses generation sizes initial address

theorem unresolved_allocation {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (address : UInt64) (mode : addresses.provenanceMode≠.strict) (raw : Unresolved memory addresses address) :
    addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory)=.ok none := by
  rcases raw with miss | predecessor
  · exact WildcardOrderedMissAddress.allocation_miss addresses address (GlobalAddressLiveErrorExclusion.lookup memory) mode miss
  · exact WildcardUnexposedPredecessorAddress.allocation_miss memory addresses address mode predecessor

theorem unresolved_typed {K U : Type} (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode≠.strict)
    (raw : Unresolved before.machine.memory before.machine.user.addresses address) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before=.ok none before := by
  rcases raw with miss | predecessor
  · exact WildcardOrderedMissAddress.resolve_miss pointers before address mode miss
  · exact WildcardUnexposedPredecessorAddress.resolve_miss pointers before address mode predecessor

/-- Every nonstrict zero-byte source allocation lookup completes from a raw
address history; the actual metadata precedence and liveness are derived from
that history, independently of which geometric case the search selects. -/
theorem history_total {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressReuseHistory.History sizes memory addresses) (address : UInt64)
    (mode : addresses.provenanceMode≠.strict) :
    ∃ result,addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory)=.ok result := by
  obtain ⟨generation,initial⟩:=GlobalAddressReuseHistory.invariant sizes history
  apply WildcardEmptyCoherentResolution.total memory addresses address initial.resources.recurring mode
  intro row member
  exact row_supplier memory row.allocId (sizes row.allocId) (initial.resources.rows row member)

/-- Exhaustive mode split preserves the source strict-mode error as an error.
No strict failure is counted as a completed or safe whole-program invocation. -/
theorem history_modes {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressReuseHistory.History sizes memory addresses) (address : UInt64) :
    (addresses.provenanceMode=.strict ∧ addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory)=.error .strictAddressLookup) ∨
    (addresses.provenanceMode≠.strict ∧ Cases memory addresses address sizes ∧
      ∃ result,addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory)=.ok result) := by
  by_cases mode : addresses.provenanceMode=.strict
  · exact Or.inl ⟨mode,by
      unfold GlobalAddressState.allocIdFromAddr
      simp only [mode,beq_self_eq_true,ite_true] <;> rfl⟩
  · exact Or.inr ⟨mode,history_classify sizes history address,history_total sizes history address mode⟩
end DuplicatePrefix.WildcardEmptyHistoryClassification
