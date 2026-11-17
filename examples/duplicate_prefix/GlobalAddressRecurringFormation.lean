import duplicate_prefix.GlobalAddressExposureFormation

namespace DuplicatePrefix.GlobalAddressRecurringFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressFreeHistoryFormation GlobalAddressMemoryFreeFormation GlobalAddressExposureFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Recurring physical address certificate. Every field describes memory or
stored address rows; no field assumes operation success. -/
structure State {Prov Extra K : Type} (memory : MemoryState Prov Extra K) (addresses : GlobalAddressState) : Prop where
  live : LiveRows addresses (fun id => memory.isAllocLive id = true)
  ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap
  unique : (addresses.intToPtrMap.toList.map InverseAddressEntry.allocId).Nodup

theorem expose {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState) (initial : State memory addresses)
    (provenance : Provenance) (tracker : Bool) (hook : Option (Except String Unit)) :
    let status := match provenance with | .wildcard => none | .concrete id _ => some (memory.isAllocLive id)
    State memory (addresses.exposeProvenance provenance status tracker hook).state := by
  refine ⟨expose_coherent memory addresses initial.live provenance tracker hook,?_,?_⟩
  · rw [expose_inverse];exact initial.ordered
  · rw [expose_inverse];exact initial.unique

/-- Fresh live allocation metadata and a raw address partition produce actual
successful cache insertion and the recurring physical certificate. -/
theorem cache {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState) (initial : State memory addresses)
    (id : AllocId) (live : memory.isAllocLive id = true) (address : UInt64)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (fresh : id ∉ addresses.intToPtrMap.toList.map InverseAddressEntry.allocId)
    (nonzero : address ≠ 0) (cut : Nat)
    (geometry : WildcardInteriorHitAddress.Cut addresses.intToPtrMap address cut) :
    (addresses.cacheAddress id address).outcome = .ok () ∧
    State memory (addresses.cacheAddress id address).state := by
  have completed := cache_ordered_completed addresses id address uncached nonzero cut geometry initial.ordered
  exact ⟨completed.1,cache_coherent memory addresses initial.live id live address,
    completed.2,cache_unique addresses id address initial.unique fresh⟩

private theorem erase_ordered (entries : Array InverseAddressEntry)
    (position : Nat) (valid : position < entries.size)
    (ordered : WildcardInteriorHitAddress.Ordered entries) :
    WildcardInteriorHitAddress.Ordered (entries.eraseIdx position valid) := by
  intro left right less rightValid
  have size : (entries.eraseIdx position valid).size = entries.size-1 := Array.size_eraseIdx position valid
  have leftValid : left < (entries.eraseIdx position valid).size := by omega
  rw [Array.getElem_eraseIdx valid leftValid,Array.getElem_eraseIdx valid rightValid]
  split <;> split
  all_goals apply ordered <;> omega

/-- Real memory removal and address free preserve the recurring certificate
against the successor memory, even when reuse insertion later reports error. -/
theorem free {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState) (initial : State memory addresses)
    (id : AllocId) (base : UInt64) (position : Nat) (valid : position < addresses.intToPtrMap.size)
    (row : addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (cached : addresses.baseAddr.find? (fun entry => entry.allocId == id) = some ⟨id,base⟩)
    (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    State (source_memory_remove_live memory id).1
      (addresses.freeAllocId id size align kind thread reuseChoice clock).state := by
  have injective : ∀ i (hi : i < addresses.intToPtrMap.size) j (hj : j < addresses.intToPtrMap.size),
      addresses.intToPtrMap[i].allocId = addresses.intToPtrMap[j].allocId → i = j := by
    intro i hi j hj same
    apply initial.unique.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
    simpa using same
  have frame := free_erases addresses id base position valid initial.ordered row cached size align kind thread reuseChoice clock
  refine ⟨remove_and_free_coherent memory addresses initial.live id base position valid initial.ordered row cached injective
    size align kind thread reuseChoice clock,?_,?_⟩
  · rw [frame.1]
    exact erase_ordered addresses.intToPtrMap position valid initial.ordered
  · rw [frame.1,Array.toList_eraseIdx]
    exact ((List.eraseIdx_sublist addresses.intToPtrMap.toList position).map InverseAddressEntry.allocId).nodup initial.unique
/-- Real address initialization forms every recurring invariant internally. -/
theorem new {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (provenanceMode : ProvenanceMode) (mode : AddressSpaceMode) (start stop : UInt64)
    (config : AddressReuseConfig)
    (reuse : (Float.le 0.0 config.addressReuseRate && Float.le config.addressReuseRate 1.0) = true)
    (cross : (Float.le 0.0 config.addressReuseCrossThreadRate && Float.le config.addressReuseCrossThreadRate 1.0) = true) :
    ∃ addresses, GlobalAddressState.new provenanceMode mode start stop config = .ok addresses ∧
      State memory addresses := by
  unfold GlobalAddressState.new ReusePool.new
  unfold_internal ".ReusePool.validRate"
  simp only [reuse,cross,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  cases mode <;>
    refine ⟨_,rfl,empty_vectors memory _ rfl rfl,?_,by simp⟩
  all_goals intro left right less valid;simp at valid

end DuplicatePrefix.GlobalAddressRecurringFormation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GlobalAddressRecurringFormation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved recurring address formation dependency {dependency}"
