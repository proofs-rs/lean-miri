import duplicate_prefix.GlobalAddressRecurringFormation

namespace DuplicatePrefix.GlobalAddressLiveErrorExclusion
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The actual fixed-memory wildcard callback; sizes use real getAllocInfo and
liveness uses real isAllocLive, exactly as PointerMachine.ptrGetAlloc. -/
def lookup {Prov Extra K : Type} (memory : MemoryState Prov Extra K) : AddressLookupHooks :=
  { sizeOf := fun id => (memory.getAllocInfo id).toOption.map (·.size)
    isLive := fun id => some (memory.isAllocLive id) }

/-- A coherent exposed set excludes the actual stale/dead inverse-index error
for every address and access size. Other resolver outcomes retain their meaning. -/
theorem no_dead_index {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState) (initial : GlobalAddressRecurringFormation.State memory addresses)
    (address : UInt64) (size : Int64) (id : AllocId) :
    addresses.allocIdFromAddr address size (lookup memory) ≠ .error (.deadAllocationInAddressIndex id) := by
  have exposedLive : ∀ query, addresses.exposed.contains query = true → memory.isAllocLive query = true := by
    intro query member
    exact initial.live.2 query (Array.contains_iff_mem.mp member)
  unfold GlobalAddressState.allocIdFromAddr
  dsimp only [lookup]
  split
  · change Except.error AddressStateError.strictAddressLookup ≠ Except.error (AddressStateError.deadAllocationInAddressIndex id)
    intro equal;cases equal
  · unfold_global_data ".GlobalAddressState.inverseSearch"
    let sought := if size.toInt < 0 then if address == 0 then 0 else address-1 else address
    generalize search : miss_source_inverse_search addresses.intToPtrMap sought = result
    rcases result with ⟨position,found⟩
    cases found <;> simp only [bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,MonadExcept.throw]
    all_goals repeat' (split <;> try simp_all [throwThe,MonadExceptOf.throw])
/-- Raw metadata suppliers in the source lookup precedence. No constructor
assumes a successful getAllocInfo call or any memory operation. -/
inductive Supplier {Prov Extra K : Type} (memory : MemoryState Prov Extra K) (id : AllocId) : Prop where
  | localRow (entry : LocalAllocation Prov Extra K)
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
  | functionRow (absent : memory.live.find? (fun row => row.1 == id) = none)
      (present : memory.hasFunctionPointer id = true)
  | vaListRow (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false) (present : memory.hasVaListId id = true)
  | globalRow (descriptor : GlobalAllocation)
      (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false) (noVaList : memory.hasVaListId id = false)
      (present : memory.findGlobal? id = some descriptor)

/-- Raw live suppliers form successful nondead metadata through the real
getAllocInfo code. Lazy globals need no initializer for this metadata query. -/
theorem metadata_of_supplier {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (id : AllocId) (supplier : Supplier memory id) :
    ∃ info, memory.getAllocInfo id = .ok info ∧ info.kind ≠ .dead := by
  cases supplier with
  | localRow entry present =>
    simp only [MemoryState.getAllocInfo,present]
    exact ⟨_,rfl,by intro impossible;cases impossible⟩
  | functionRow absent present =>
    simp only [MemoryState.getAllocInfo,absent,present,↓reduceIte]
    exact ⟨_,rfl,by intro impossible;cases impossible⟩
  | vaListRow absent noFunction present =>
    unfold MemoryState.hasVaListId at present
    simp only [MemoryState.getAllocInfo,absent,noFunction,present,Bool.false_eq_true,↓reduceIte]
    exact ⟨_,rfl,by intro impossible;cases impossible⟩
  | globalRow descriptor absent noFunction noVaList present =>
    unfold MemoryState.hasVaListId at noVaList
    simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,present,Bool.false_eq_true,↓reduceIte]
    cases descriptor.kind <;> exact ⟨_,rfl,by intro impossible;cases impossible⟩

/-- Every actual inverse/exposed row receives real nondead metadata from its
raw supplier and precedence conditions; coherence independently excludes the
resolver's stale-index error for all addresses and access sizes. -/
theorem rows_metadata {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState)
    (inverse : ∀ row ∈ addresses.intToPtrMap, Supplier memory row.allocId)
    (exposed : ∀ id ∈ addresses.exposed, Supplier memory id) :
    (∀ row ∈ addresses.intToPtrMap, ∃ info, memory.getAllocInfo row.allocId = .ok info ∧ info.kind ≠ .dead) ∧
    (∀ id ∈ addresses.exposed, ∃ info, memory.getAllocInfo id = .ok info ∧ info.kind ≠ .dead) := by
  exact ⟨fun row member => metadata_of_supplier memory row.allocId (inverse row member),
    fun id member => metadata_of_supplier memory id (exposed id member)⟩

end DuplicatePrefix.GlobalAddressLiveErrorExclusion

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GlobalAddressLiveErrorExclusion." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved live error exclusion dependency {dependency}"
