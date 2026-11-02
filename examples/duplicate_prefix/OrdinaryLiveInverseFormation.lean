import duplicate_prefix.OrdinaryAddressCachePreservation
import duplicate_prefix.GlobalAddressLocalRowFormation
namespace DuplicatePrefix.OrdinaryLiveInverseFormation
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Reverse cache coherence for nonzero bases of actual local live rows.
Dead cache rows and live allocations whose address has not been acquired are
unrestricted. This is a representation predicate, not ordinary reference
validity or an exhaustive machine-history invariant. -/
def LiveInverse {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) : Prop :=
  ∀ row ∈ addresses.baseAddr, row.address ≠ 0 →
    (∃ entry, memory.live.find? (fun allocation => allocation.1 == row.allocId) = some (row.allocId,entry)) →
    (⟨row.address,row.allocId⟩ : InverseAddressEntry) ∈ addresses.intToPtrMap

theorem empty {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (noBases : addresses.baseAddr = #[]) : LiveInverse memory addresses := by
  intro row member
  rw [noBases] at member
  simp only [Array.not_mem_empty] at member

/-- Every successful actual address-state initialization starts with the
relation; an initialization error is kept as an error. -/
theorem initialized {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (mode : ProvenanceMode) (space : AddressSpaceMode) (start stop : UInt64) (config : AddressReuseConfig) :
    match GlobalAddressState.new mode space start stop config with
    | .ok addresses => LiveInverse memory addresses
    | .error _ => True := by
  cases space <;> cases pool : ReusePool.new config <;>
    simp [GlobalAddressState.new,pool,LiveInverse,Except.mapError,bind,Except.bind,pure,Except.pure,Functor.map]

private theorem insert {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (initial : LiveInverse memory addresses) (id : AllocId) (base : UInt64) (index : Nat) (valid : index ≤ addresses.intToPtrMap.size) :
    LiveInverse memory {addresses with
      baseAddr := ((addresses.baseAddr.filter (fun row => row.allocId != id)).push (BaseAddressEntry.mk id base))
      intToPtrMap := addresses.intToPtrMap.insertIdx index (InverseAddressEntry.mk base id) valid} := by
  intro row member nonzero live
  change (⟨row.address,row.allocId⟩ : InverseAddressEntry) ∈ addresses.intToPtrMap.insertIdx index ⟨base,id⟩ valid
  rcases Array.mem_push.mp member with old | same
  · exact Array.mem_insertIdx.mpr (Or.inr (initial row (Array.mem_filter.mp old).1 nonzero live))
  · subst row
    exact Array.mem_insertIdx.mpr (Or.inl rfl)

private theorem zero {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (initial : LiveInverse memory addresses) (id : AllocId) :
    LiveInverse memory {addresses with baseAddr := (addresses.baseAddr.filter (fun row => row.allocId != id)).push ⟨id,0⟩} := by
  intro row member nonzero live
  rcases Array.mem_push.mp member with old | same
  · exact initial row (Array.mem_filter.mp old).1 nonzero live
  · subst row
    exact False.elim (nonzero rfl)

/-- Actual cache registration establishes reverse coherence on its normal
outcome. Partial error states have no asserted invariant or safety guarantee. -/
theorem cache {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (initial : LiveInverse memory addresses) (id : AllocId) (base : UInt64) :
    match (addresses.cacheAddress id base).outcome with
    | .ok _ => LiveInverse memory (addresses.cacheAddress id base).state
    | .error _ => True := by
  have normal : ∀ value, (addresses.cacheAddress id base).outcome = .ok value →
      LiveInverse memory (addresses.cacheAddress id base).state := by
    intro value ran
    unfold GlobalAddressState.cacheAddress at ran ⊢
    unfold_internal ".GlobalAddressState.insertBase"
    dsimp only [Id.run,bind,pure] at ran ⊢
    split at *
    · cases ran
    · split at *
      · have baseZero : base = 0 := by simpa using (show (base == 0) = true from by assumption)
        subst base
        exact zero memory addresses initial id
      · split at *
        · split at * <;> cases ran
        · split at *
          · simp_all only [↓reduceIte]
            exact insert memory addresses initial id base _ _
          · cases ran
  cases ran : (addresses.cacheAddress id base).outcome with
  | error error => trivial
  | ok value => exact normal value ran

/-- Exposure changes neither cache nor inverse rows, on either outcome. -/
theorem expose {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (initial : LiveInverse memory addresses) (provenance : Provenance) (live : Option Bool) (tracking : Bool)
    (hook : Option (Except String Unit)) : LiveInverse memory (addresses.exposeProvenance provenance live tracking hook).state := by
  have inverse := GlobalAddressExposureFormation.expose_inverse addresses provenance live tracking hook
  have bases : (addresses.exposeProvenance provenance live tracking hook).state.baseAddr = addresses.baseAddr := by
    cases provenance <;> unfold GlobalAddressState.exposeProvenance
    all_goals dsimp only [Id.run,bind,pure]
    all_goals repeat' first | split | rfl
  intro row member nonzero present
  rw [bases] at member
  rw [inverse]
  exact initial row member nonzero present

/-- Source address GC removes base rows and retains inverse rows. This local
pruning theorem keeps memory fixed; it is not a whole-machine GC theorem. -/
theorem prune {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (initial : LiveInverse memory addresses) (ids : Array AllocId) :
    LiveInverse memory (addresses.removeUnreachableAllocs ids) := by
  intro row member nonzero live
  exact initial row (Array.mem_filter.mp member).1 nonzero live

/-- A new local row may not revive a stale cached allocation id. The required
raw id freshness is explicit; no allocator-reachability claim is made. -/
theorem insert_live {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (initial : LiveInverse memory addresses) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (fresh : id ∉ addresses.baseAddr.toList.map BaseAddressEntry.allocId) :
    LiveInverse (source_range_insert_live memory id entry) addresses := by
  intro row member nonzero live
  have different : row.allocId ≠ id := by
    intro equal
    exact fresh (List.mem_map.mpr ⟨row,by simpa using member,equal⟩)
  obtain ⟨old,found⟩ := live
  have before : memory.live.find? (fun allocation => allocation.1 == row.allocId) = some (row.allocId,old) := by
    rw [GlobalAddressLiveSizeFormation.insert_lookup_other memory id row.allocId entry different] at found
    exact found
  exact initial row member nonzero ⟨old,before⟩
private theorem erase_live {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (initial : LiveInverse memory addresses) (id : AllocId) (index : Nat) (valid : index < addresses.intToPtrMap.size)
    (selected : addresses.intToPtrMap[index].allocId = id) :
    LiveInverse (source_memory_remove_live memory id).1 {addresses with intToPtrMap := addresses.intToPtrMap.eraseIdx index valid} := by
  intro row member nonzero live
  obtain ⟨entry,found⟩ := live
  have different : row.allocId ≠ id := by
    intro equal
    have found : (source_memory_remove_live memory id).1.live.find? (fun allocation => allocation.1 == id) = some (id,entry) := by simpa only [equal] using found
    unfold_internal_at ".MemoryState.removeLive" at found
    dsimp only at found
    have impossible : (memory.live.filter (fun allocation => allocation.1 != id)).find? (fun allocation => allocation.1 == id) = none := by
      apply Array.find?_eq_none.mpr
      intro allocation included
      have different := (Array.mem_filter.mp included).2
      simpa using different
    rw [impossible] at found
    cases found
  have before : memory.live.find? (fun allocation => allocation.1 == row.allocId) = some (row.allocId,entry) := by
    unfold_internal_at ".MemoryState.removeLive" at found
    dsimp only at found
    rw [GlobalAddressLiveSizeFormation.filter_lookup memory id row.allocId different] at found
    exact found
  obtain ⟨position,bounded,equal⟩ := Array.mem_iff_getElem.mp (initial row member nonzero ⟨entry,before⟩)
  apply Array.mem_eraseIdx_iff_getElem.mpr
  refine ⟨position,bounded,?_,equal⟩
  intro same
  have identity := congrArg InverseAddressEntry.allocId equal
  have atRemoved : addresses.intToPtrMap[position].allocId = id := by simpa only [same] using selected
  exact different (identity.symm.trans atRemoved)

/-- A successful paired free/removeLive preserves reverse coherence for the
remaining local live allocations. Mismatch/pool errors make no invariant or
safety assertion about their partial state. -/
theorem free {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (initial : LiveInverse memory addresses) (id : AllocId) (size : Size) (align : Align)
    (kind : AddressMemoryKind) (thread : AddressThreadId) (choice : Bool) (clock : Unit → Miri.Concurrency.VClock) :
    match (addresses.freeAllocId id size align kind thread choice clock).outcome with
    | .ok _ => LiveInverse (source_memory_remove_live memory id).1 (addresses.freeAllocId id size align kind thread choice clock).state
    | .error _ => True := by
  have normal : ∀ value, (addresses.freeAllocId id size align kind thread choice clock).outcome = .ok value →
      LiveInverse (source_memory_remove_live memory id).1 (addresses.freeAllocId id size align kind thread choice clock).state := by
    intro value ran
    unfold GlobalAddressState.freeAllocId at ran ⊢
    dsimp only [Id.run,bind,pure] at ran ⊢
    split at *
    · split at *
      · cases ran
      · split at *
        · rename_i bounded
          split at *
          · cases ran
          · have selected : (addresses.intToPtrMap[(_ : Nat)]'bounded).allocId = id := by
              apply Classical.byContradiction
              intro different
              have bad : ((addresses.intToPtrMap[(_ : Nat)]'bounded).allocId != id) = true := by simpa using different
              contradiction
            have kept := erase_live memory addresses initial id _ bounded selected
            split at *
            · simp_all only
              exact kept
            · split at *
              · simp_all only
                exact kept
              · cases ran
        · cases ran
    · cases ran
  cases ran : (addresses.freeAllocId id size align kind thread choice clock).outcome with
  | error error => trivial
  | ok value => exact normal value ran

end
end DuplicatePrefix.OrdinaryLiveInverseFormation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.OrdinaryLiveInverseFormation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved live inverse formation dependency {dependency}"
