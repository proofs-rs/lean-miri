import duplicate_prefix.ProvenanceCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnProvenanceClear
open Miri.ABI Miri.Memory
open ProvenanceCopy
set_option autoImplicit false

theorem boundary_subset {Prov : Type} (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (state updated : ProvenanceMap Prov)
    (ok : clear_boundary_action inRange position prov data state = .ok () updated) :
    ∀ entry ∈ updated.ptrs, entry ∈ state.ptrs := by
  unfold clear_boundary_action checkedResult at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
  cases h : pointerFragments inRange position prov data (Size.ofBytes 8) <;>
    simp only [h,Bind.bind,EStateM.bind,EStateM.get,EStateM.set] at ok
  · cases ok
  · cases ok
    exact fun _ member => member

theorem finish_subset {Prov : Type} (range : AllocRange) (finish : Size)
    (state updated : ProvenanceMap Prov)
    (ok : clear_finish_action range finish state = .ok () updated) :
    ∀ entry ∈ updated.ptrs, entry ∈ state.ptrs := by
  unfold clear_finish_action adjustedStart checkedResult at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.adjustedStart" at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
  simp only [show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl,
    show ((8 : UInt64)==0)=false from rfl,Bool.false_eq_true,↓reduceIte,
    Bind.bind,EStateM.bind,EStateM.get,EStateM.set] at ok
  cases ok
  intro entry member
  unfold removeEntries at member
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.removeEntries" at member
  exact (Array.mem_filter.mp member).1

theorem last_subset {Prov : Type} (range : AllocRange) (finish : Size) (data : Array UInt8)
    (entries : Array (Size × Prov)) (state updated : ProvenanceMap Prov)
    (ok : clear_last_action range finish data entries state = .ok () updated) :
    ∀ entry ∈ updated.ptrs, entry ∈ state.ptrs := by
  cases last : entries.back? with
  | none =>
    simp only [clear_last_action,last] at ok
    exact finish_subset range finish state updated ok
  | some pair =>
    obtain ⟨position,prov⟩ := pair
    unfold clear_last_action checkedResult at ok
    unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
    simp only [last] at ok
    cases added : Size.add position (Size.ofBytes 8) with
    | error err =>
      simp only [added,Except.mapError,Bind.bind,EStateM.bind] at ok
      cases ok
    | ok endpoint =>
      simp only [added,Except.mapError,Bind.bind,EStateM.bind] at ok
      by_cases overlap : endpoint.bytes > finish.bytes
      · simp only [overlap,↓reduceIte] at ok
        cases middle : clear_boundary_action (fun pos => finish.bytes ≤ pos.bytes) position prov data state with
        | error err after =>
          simp only [middle,Bind.bind,EStateM.bind] at ok
          cases ok
        | ok unit after =>
          cases unit
          simp only [middle,Bind.bind,EStateM.bind] at ok
          have first := boundary_subset _ _ _ _ state after middle
          have last := finish_subset range finish after updated ok
          exact fun entry member => first entry (last entry member)
      · simp only [overlap,↓reduceIte,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure] at ok
        exact finish_subset range finish state updated ok

theorem first_subset {Prov : Type} (range : AllocRange) (finish : Size) (data : Array UInt8)
    (entries : Array (Size × Prov)) (state updated : ProvenanceMap Prov)
    (ok : clear_first_action range finish data entries state = .ok () updated) :
    ∀ entry ∈ updated.ptrs, entry ∈ state.ptrs := by
  cases first : entries[0]? with
  | none =>
    simp only [clear_first_action,first] at ok
    exact last_subset range finish data entries state updated ok
  | some pair =>
    obtain ⟨position,prov⟩ := pair
    simp only [clear_first_action,first] at ok
    by_cases overlap : position.bytes < range.start.bytes
    · simp only [overlap,↓reduceIte] at ok
      cases middle : clear_boundary_action (fun pos => pos.bytes < range.start.bytes) position prov data state with
      | error err after =>
        simp only [middle,Bind.bind,EStateM.bind] at ok
        cases ok
      | ok unit after =>
        cases unit
        simp only [middle,Bind.bind,EStateM.bind] at ok
        have first := boundary_subset _ _ _ _ state after middle
        have last := last_subset range finish data entries after updated ok
        exact fun entry member => first entry (last entry member)
    · simp only [overlap,↓reduceIte,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure] at ok
      exact last_subset range finish data entries state updated ok

theorem clear_pointer_subset {Prov : Type} (state updated : ProvenanceMap Prov)
    (range : AllocRange) (finish : Size) (data : Array UInt8)
    (endpoint : range.endExclusive = .ok finish)
    (ok : ProvenanceMap.clear range data (Size.ofBytes 8) state = .ok () updated) :
    ∀ entry ∈ updated.ptrs, entry ∈ state.ptrs := by
  by_cases zero : range.size.bytes = 0
  · simp only [ProvenanceMap.clear,show (range.size.bytes == 0) = true from by simp [zero],
      ↓reduceIte,Pure.pure,EStateM.pure] at ok
    cases ok
    exact fun _ member => member
  · unfold ProvenanceMap.clear at ok
    unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
    unfold_provenance_at ".Miri.Memory.ProvenanceMap.rangeEnd" at ok
    simp only [show (range.size.bytes == 0) = false from by simp [zero],
      Bool.false_eq_true, ↓reduceIte, endpoint, Except.mapError,
      Bind.bind,EStateM.bind,EStateM.get,EStateM.set,Pure.pure,EStateM.pure] at ok
    unfold ProvenanceMap.rangePtrs at ok
    unfold_provenance_at ".Miri.Memory.ProvenanceMap.adjustedStart" at ok
    unfold_provenance_at ".Miri.Memory.ProvenanceMap.rangeEnd" at ok
    unfold_provenance_at ".Miri.Memory.ProvenanceMap.rangeEntries" at ok
    simp only [show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl,
      Bool.false_eq_true,↓reduceIte,endpoint,Except.mapError,Bind.bind,Except.bind,Pure.pure,Except.pure,
      show ((8 : UInt64) == 0) = false from rfl,show (8 : UInt64).toNat = 8 from rfl,
      show (8 : Nat)-1=7 from rfl,EStateM.bind,EStateM.get,EStateM.set,EStateM.pure] at ok
    generalize entriesEq : (state.ptrs.filter fun entry =>
      decide ((Size.ofBytes (UInt64.ofNat (range.start.bytes.toNat - 7))).bytes ≤ entry.1.bytes) &&
      decide (entry.1.bytes < finish.bytes)) = entries at ok
    let initial := mkMap state.ptrs (state.byteFragments.map fun bytes => removeEntries bytes range.start finish)
    by_cases empty : entries.isEmpty = true
    · simp only [empty,↓reduceIte,EStateM.pure] at ok
      cases ok
      exact fun _ member => member
    · simp only [empty,↓reduceIte] at ok
      have action : clear_first_action range finish data entries initial = .ok () updated := by
        unfold clear_first_action clear_last_action clear_boundary_action clear_finish_action
        simp only [pointerFragments,checkedResult,adjustedStart,insertEntry,initial]
        unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
        cases firstEntry : entries[0]? <;> cases lastEntry : entries.back? <;>
          simp only [firstEntry,lastEntry] at ok ⊢ <;> simpa_clear_implementation using ok
      exact first_subset range finish data entries initial updated action
end DuplicatePrefix.S04ReturnProvenanceClear
