import duplicate_prefix.GlobalAddressMemoryFreeFormation
import duplicate_prefix.WildcardGapAddress

namespace DuplicatePrefix.GlobalAddressExposureFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressFreeHistoryFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Liveness supplied to actual exposure is read from the actual memory, so
exposure cannot add a nonlive id, including on tracker-hook error paths. -/
theorem expose_coherent {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState)
    (initial : LiveRows addresses (fun id => memory.isAllocLive id = true))
    (provenance : Provenance) (tracker : Bool) (hook : Option (Except String Unit)) :
    let status := match provenance with
      | .wildcard => none
      | .concrete id _ => some (memory.isAllocLive id)
    LiveRows (addresses.exposeProvenance provenance status tracker hook).state
      (fun id => memory.isAllocLive id = true) := by
  cases provenance with
  | wildcard => exact initial
  | concrete id tag =>
    unfold GlobalAddressState.exposeProvenance
    dsimp only
    split
    · exact initial
    · cases live : memory.isAllocLive id with
      | false => exact initial
      | true =>
        have grown : ∀ query ∈ (if addresses.exposed.contains id then addresses.exposed else addresses.exposed.push id),
            memory.isAllocLive query = true := by
          intro query member
          split at member
          · exact initial.2 query member
          · rcases Array.mem_push.mp member with old | same
            · exact initial.2 query old
            · simpa only [same] using live
        cases tracker with
        | false => exact ⟨initial.1,grown⟩
        | true =>
          cases hook with
          | none => exact ⟨initial.1,grown⟩
          | some value => cases value <;> exact ⟨initial.1,grown⟩

/-- Exposure retains the actual inverse vector exactly, so all its geometric
and allocation-identifier uniqueness invariants survive, even on hook errors. -/
theorem expose_inverse (addresses : GlobalAddressState) (provenance : Provenance)
    (live : Option Bool) (tracker : Bool) (hook : Option (Except String Unit)) :
    (addresses.exposeProvenance provenance live tracker hook).state.intToPtrMap = addresses.intToPtrMap := by
  cases provenance with
  | wildcard => rfl
  | concrete id tag =>
    unfold GlobalAddressState.exposeProvenance
    dsimp only
    split
    · rfl
    · cases live with
      | none => rfl
      | some live =>
        cases live with
        | false => rfl
        | true =>
          cases tracker with
          | false => rfl
          | true => cases hook with
            | none => rfl
            | some value => cases value <;> rfl

/-- Actual cache insertion introduces only its supplied live allocation id.
This includes partial-state cache errors without counting them as completion. -/
theorem cache_coherent {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState)
    (initial : LiveRows addresses (fun id => memory.isAllocLive id = true))
    (id : AllocId) (live : memory.isAllocLive id = true) (address : UInt64) :
    LiveRows (addresses.cacheAddress id address).state (fun query => memory.isAllocLive query = true) := by
  unfold GlobalAddressState.cacheAddress
  dsimp only
  split
  · exact initial
  · split
    · exact initial
    · split
      · split <;> exact initial
      · split
        · rename_i bounded
          constructor
          · intro row member
            change row ∈ addresses.intToPtrMap.insertIdx _ ⟨address,id⟩ bounded at member
            rcases Array.mem_insertIdx.mp member with same | old
            · simpa only [same] using live
            · exact initial.1 row old
          · exact initial.2
        · exact initial
/-- Fresh raw cache/address geometry derives successful nonzero insertion.
The actual binary search supplies its bounded insertion position internally. -/
theorem cache_fresh_completed (addresses : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (nonzero : address ≠ 0)
    (distinct : ∀ row ∈ addresses.intToPtrMap, row.address ≠ address) :
    ∃ position, ∃ bounded : position ≤ addresses.intToPtrMap.size,
      (addresses.cacheAddress id address).outcome = .ok () ∧
      (addresses.cacheAddress id address).state.intToPtrMap =
        addresses.intToPtrMap.insertIdx position ⟨address,id⟩ bounded := by
  obtain ⟨position,search,bounded,_⟩ := WildcardGapAddress.inverse_missing addresses.intToPtrMap address distinct
  refine ⟨position,bounded,?_⟩
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  simp only [uncached,Option.map_none,search,Bool.false_eq_true,↓reduceIte,bounded,↓reduceDIte]
  have nonzeroBool : (address == 0) = false := by simpa using nonzero
  simp only [nonzeroBool,Bool.false_eq_true,↓reduceIte]
  exact ⟨rfl,rfl⟩

/-- Exposure preserves strict inverse ordering and distinct allocation IDs
as actual vector properties, with liveness read from actual memory. -/
theorem expose_geometry (addresses : GlobalAddressState) (provenance : Provenance)
    (live : Option Bool) (tracker : Bool) (hook : Option (Except String Unit))
    (ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap)
    (unique : (addresses.intToPtrMap.toList.map InverseAddressEntry.allocId).Nodup) :
    WildcardInteriorHitAddress.Ordered (addresses.exposeProvenance provenance live tracker hook).state.intToPtrMap ∧
    ((addresses.exposeProvenance provenance live tracker hook).state.intToPtrMap.toList.map
      InverseAddressEntry.allocId).Nodup := by
  rw [expose_inverse]
  exact ⟨ordered,unique⟩

private theorem mapped_insert_unique {α β : Type} (f : α → β) (xs : List α) (x : α)
    (unique : (xs.map f).Nodup) (fresh : f x ∉ xs.map f) (position : Nat)
    (bounded : position ≤ xs.length) : ((xs.insertIdx position x).map f).Nodup := by
  induction xs generalizing position with
  | nil =>
    have zero : position = 0 := by simpa using bounded
    subst position
    simp
  | cons head tail ih =>
    have parts := List.nodup_cons.mp unique
    cases position with
    | zero => exact List.nodup_cons.mpr ⟨fresh,unique⟩
    | succ position =>
      have limit : position ≤ tail.length := Nat.le_of_succ_le_succ bounded
      have freshTail : f x ∉ tail.map f := fun member => fresh (List.mem_cons_of_mem _ member)
      have freshHead : f head ≠ f x := fun same => fresh (List.mem_cons.mpr (Or.inl same.symm))
      apply List.nodup_cons.mpr
      refine ⟨?_,ih parts.2 freshTail position limit⟩
      intro member
      obtain ⟨entry,inserted,equal⟩ := List.mem_map.mp member
      rcases (List.mem_insertIdx limit).mp inserted with same | old
      · exact freshHead (equal.symm.trans (congrArg f same))
      · exact parts.1 (List.mem_map.mpr ⟨entry,old,equal⟩)

/-- Fresh allocation identity preserves distinct inverse-map identifiers
through actual cache insertion, on successful and partial-error paths alike. -/
theorem cache_unique (addresses : GlobalAddressState) (id : AllocId) (address : UInt64)
    (unique : (addresses.intToPtrMap.toList.map InverseAddressEntry.allocId).Nodup)
    (fresh : id ∉ addresses.intToPtrMap.toList.map InverseAddressEntry.allocId) :
    ((addresses.cacheAddress id address).state.intToPtrMap.toList.map InverseAddressEntry.allocId).Nodup := by
  unfold GlobalAddressState.cacheAddress
  dsimp only
  split
  · exact unique
  · split
    · exact unique
    · split
      · split <;> exact unique
      · split
        · rename_i bounded
          change ((addresses.intToPtrMap.insertIdx _ ⟨address,id⟩ bounded).toList.map InverseAddressEntry.allocId).Nodup
          rw [Array.toList_insertIdx]
          exact mapped_insert_unique InverseAddressEntry.allocId addresses.intToPtrMap.toList ⟨address,id⟩ unique fresh _ (by simpa using bounded)
        · exact unique

private theorem insert_ordered (entries : Array InverseAddressEntry) (id : AllocId) (address : UInt64)
    (cut : Nat) (geometry : WildcardInteriorHitAddress.Cut entries address cut)
    (ordered : WildcardInteriorHitAddress.Ordered entries) :
    WildcardInteriorHitAddress.Ordered (entries.insertIdx cut ⟨address,id⟩ geometry.1) := by
  intro left right less valid
  have cutBound := geometry.1
  have rightBound : right < entries.size+1 := by simpa only [Array.size_insertIdx] using valid
  have leftBound : left < entries.size+1 := by omega
  rw [Array.getElem_insertIdx geometry.1 (by simpa only [Array.size_insertIdx] using leftBound),
    Array.getElem_insertIdx geometry.1 valid]
  by_cases beforeLeft : left < cut
  · simp only [beforeLeft,↓reduceDIte]
    by_cases beforeRight : right < cut
    · simp only [beforeRight,↓reduceDIte]
      exact ordered left right less (by omega)
    · simp only [beforeRight,↓reduceDIte]
      by_cases equalRight : right = cut
      · simp only [equalRight,↓reduceDIte]
        exact geometry.2.1 left (by omega) beforeLeft
      · simp only [equalRight,↓reduceDIte]
        have first := geometry.2.1 left (by omega) beforeLeft
        have second := geometry.2.2 (right-1) (by omega) (by omega)
        exact UInt64.lt_iff_toNat_lt.mpr (Nat.lt_trans (UInt64.lt_iff_toNat_lt.mp first) (UInt64.lt_iff_toNat_lt.mp second))
  · simp only [beforeLeft,↓reduceDIte]
    have notRight : ¬ right < cut := by omega
    have differentRight : right ≠ cut := by omega
    simp only [notRight,differentRight,↓reduceDIte]
    by_cases equalLeft : left = cut
    · simp only [equalLeft,↓reduceDIte]
      exact geometry.2.2 (right-1) (by omega) (by omega)
    · simp only [equalLeft,↓reduceDIte]
      exact ordered (left-1) (right-1) (by omega) (by omega)

/-- Raw insertion partition and initial ordering derive successful actual cache
insertion and strict ordering of the resulting inverse vector. -/
theorem cache_ordered_completed (addresses : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (nonzero : address ≠ 0) (cut : Nat)
    (geometry : WildcardInteriorHitAddress.Cut addresses.intToPtrMap address cut)
    (ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap) :
    (addresses.cacheAddress id address).outcome = .ok () ∧
    WildcardInteriorHitAddress.Ordered (addresses.cacheAddress id address).state.intToPtrMap := by
  have search := WildcardInteriorHitAddress.inverse_cut addresses.intToPtrMap address cut geometry
  have nonzeroBool : (address == 0) = false := by simpa using nonzero
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  simp only [uncached,Option.map_none,search,nonzeroBool,Bool.false_eq_true,↓reduceIte,geometry.1,↓reduceDIte]
  exact ⟨rfl,insert_ordered addresses.intToPtrMap id address cut geometry ordered⟩

end DuplicatePrefix.GlobalAddressExposureFormation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GlobalAddressExposureFormation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved exposure formation dependency {dependency}"
