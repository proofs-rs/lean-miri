import duplicate_prefix.GlobalAddressFreeHistoryFormation

namespace DuplicatePrefix.GlobalAddressMemoryFreeFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressFreeHistoryFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab in
elab "source_memory_remove_live" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".MemoryState.removeLive" then some name else none
  let [name] := names | throwError "expected original memory removeLive"
  Lean.Meta.mkConstWithFreshMVarLevels name

/-- The actual private removeLive used by deallocatePtrWith preserves every
other live identifier, including nonlocal metadata suppliers. -/
theorem remove_preserves_other {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (id query : AllocId) (different : query ≠ id) (live : memory.isAllocLive query = true) :
    (source_memory_remove_live memory id).1.isAllocLive query = true := by
  unfold_internal ".MemoryState.removeLive"
  simp only [MemoryState.isAllocLive,Bool.or_eq_true,Array.any_eq_true'] at live ⊢
  rcases live with ((localLive | extra) | vaList) | global
  · obtain ⟨entry,member,same⟩ := localLive
    apply Or.inl;apply Or.inl;apply Or.inl
    refine ⟨entry,Array.mem_filter.mpr ⟨member,?_⟩,same⟩
    have equal : entry.1 = query := by simpa using same
    simpa only [equal,bne_iff_ne] using different
  · exact Or.inl (Or.inl (Or.inr extra))
  · exact Or.inl (Or.inr vaList)
  · exact Or.inr global

/-- Coherence is formed without assumptions for empty address vectors,
regardless of the current memory allocation domain. -/
theorem empty_vectors {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState) (inverse : addresses.intToPtrMap = #[])
    (exposed : addresses.exposed = #[]) :
    LiveRows addresses (fun id => memory.isAllocLive id = true) := by
  constructor <;> simp [inverse,exposed]

/-- Join the actual source live-map removal with actual address free. Initial
lookup geometry and uniqueness form output coherence against the *new* memory
state, not a retained artificial live domain. Reuse errors remain errors. -/
theorem remove_and_free_coherent {Prov Extra K : Type}
    (memory : MemoryState Prov Extra K) (addresses : GlobalAddressState)
    (initial : LiveRows addresses (fun id => memory.isAllocLive id = true))
    (id : AllocId) (base : UInt64) (position : Nat) (valid : position < addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap)
    (row : addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (cached : addresses.baseAddr.find? (fun entry => entry.allocId == id) = some ⟨id,base⟩)
    (unique : ∀ i (hi : i < addresses.intToPtrMap.size) j (hj : j < addresses.intToPtrMap.size),
      addresses.intToPtrMap[i].allocId = addresses.intToPtrMap[j].allocId → i = j)
    (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    LiveRows (addresses.freeAllocId id size align kind thread reuseChoice clock).state
      (fun query => (source_memory_remove_live memory id).1.isAllocLive query = true) := by
  have next := free_shrinks_live addresses (fun query => memory.isAllocLive query = true) initial
    id base position valid ordered row cached unique size align kind thread reuseChoice clock
  constructor
  · intro entry member
    have facts := next.1 entry member
    exact remove_preserves_other memory id entry.allocId facts.2 facts.1
  · intro tag member
    have facts := next.2 tag member
    exact remove_preserves_other memory id tag facts.2 facts.1
/-- Actual address-state initialization forms memory coherence and completes
from raw valid probability bounds in every address mode. -/
theorem new_coherent {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (provenanceMode : ProvenanceMode) (mode : AddressSpaceMode) (start stop : UInt64)
    (config : AddressReuseConfig)
    (reuse : (Float.le 0.0 config.addressReuseRate && Float.le config.addressReuseRate 1.0) = true)
    (cross : (Float.le 0.0 config.addressReuseCrossThreadRate && Float.le config.addressReuseCrossThreadRate 1.0) = true) :
    ∃ addresses, GlobalAddressState.new provenanceMode mode start stop config = .ok addresses ∧
      LiveRows addresses (fun id => memory.isAllocLive id = true) := by
  unfold GlobalAddressState.new ReusePool.new
  unfold_internal ".ReusePool.validRate"
  simp only [reuse,cross,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  cases mode <;>
    exact ⟨_,rfl,empty_vectors memory _ rfl rfl⟩

end DuplicatePrefix.GlobalAddressMemoryFreeFormation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GlobalAddressMemoryFreeFormation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved memory-free formation dependency {dependency}"
