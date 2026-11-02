import duplicate_prefix.S02SameDestinationUninitProvenanceFragments

namespace DuplicatePrefix.S02SameDestinationUninitProvenanceClear
open Miri.ABI Miri.Memory
open ProvenanceCopy S02SameDestinationUninitProvenanceFragments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {Prov : Type}

def Remaining (ptrs : Array (Size × Prov)) (range : AllocRange) (finish : Size) :=
  ptrs.filter fun entry => !(UInt64.ofNat (range.start.bytes.toNat - 7) ≤ entry.1.bytes && entry.1.bytes < finish.bytes)

theorem finish_effect (range : AllocRange) (finish : Size) (before after : ProvenanceMap Prov)
    (ok : clear_finish_action range finish before = .ok () after) :
    after.ptrs = Remaining before.ptrs range finish ∧ after.byteFragments = before.byteFragments := by
  unfold clear_finish_action adjustedStart checkedResult at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.adjustedStart" at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
  simp only [show (Size.ofBytes 8).bytes = (8 : UInt64) from rfl,
    show ((8 : UInt64)==0)=false from rfl, Bool.false_eq_true, ↓reduceIte,
    Bind.bind,EStateM.bind,EStateM.get,EStateM.set] at ok
  cases ok
  exact ⟨rfl,rfl⟩

theorem last_effect (original : ProvenanceMap Prov) (range : AllocRange) (finish : Size)
    (data : Array UInt8) (entries : Array (Size × Prov))
    (bounds : ∀ pointer ∈ entries, pointer.1.bytes.toNat+8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616)
    (before after : ProvenanceMap Prov)
    (old : ∀ fragment ∈ before.byteFragments.getD #[], Origin original entries fragment)
    (ok : clear_last_action range finish data entries before = .ok () after) :
    after.ptrs = Remaining before.ptrs range finish ∧
    (∀ fragment ∈ after.byteFragments.getD #[], Origin original entries fragment) ∧
    (after.byteFragments.getD #[]).size ≤ (before.byteFragments.getD #[]).size + 8 := by
  cases last : entries.back? with
  | none =>
    simp only [clear_last_action,last] at ok
    obtain ⟨ptrs,frags⟩ := finish_effect range finish before after ok
    exact ⟨ptrs,by simpa [frags] using old,by simp [frags]⟩
  | some pair =>
    obtain ⟨position,prov⟩ := pair
    have member := Array.mem_of_back? last
    have available := bounds (position,prov) member
    unfold clear_last_action at ok
    simp only [last] at ok
    rw [pointer_end_checked position data available storageFits] at ok
    unfold checkedResult at ok
    unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
    simp only [Except.mapError,Bind.bind,EStateM.bind] at ok
    by_cases crossing : (Size.ofBytes (position.bytes+8)).bytes > finish.bytes
    · simp only [crossing,↓reduceIte,Bind.bind,EStateM.bind] at ok
      cases action : clear_boundary_action (fun pos => finish.bytes ≤ pos.bytes) position prov data before with
      | error err state => simp [action] at ok
      | ok value middle =>
        cases value
        simp only [action] at ok
        obtain ⟨ptrs,frags,count⟩ := boundary_effect original entries _ position prov data available storageFits member before middle old action
        obtain ⟨finalPtrs,finalFrags⟩ := finish_effect range finish middle after ok
        exact ⟨by rw [finalPtrs,ptrs],by simpa [finalFrags] using frags,by simpa [finalFrags] using count⟩
    · simp only [crossing,↓reduceIte,Pure.pure,EStateM.pure] at ok
      obtain ⟨ptrs,frags⟩ := finish_effect range finish before after ok
      exact ⟨ptrs,by simpa [frags] using old,by simp [frags]⟩

theorem first_effect (original : ProvenanceMap Prov) (range : AllocRange) (finish : Size)
    (data : Array UInt8) (entries : Array (Size × Prov))
    (bounds : ∀ pointer ∈ entries, pointer.1.bytes.toNat+8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616)
    (before after : ProvenanceMap Prov)
    (old : ∀ fragment ∈ before.byteFragments.getD #[], Origin original entries fragment)
    (ok : clear_first_action range finish data entries before = .ok () after) :
    after.ptrs = Remaining before.ptrs range finish ∧
    (∀ fragment ∈ after.byteFragments.getD #[], Origin original entries fragment) ∧
    (after.byteFragments.getD #[]).size ≤ (before.byteFragments.getD #[]).size + 16 := by
  cases first : entries[0]? with
  | none =>
    simp only [clear_first_action,first] at ok
    obtain ⟨ptrs,frags,count⟩ := last_effect original range finish data entries bounds storageFits before after old ok
    exact ⟨ptrs,frags,by omega⟩
  | some pair =>
    obtain ⟨position,prov⟩ := pair
    have member := Array.mem_of_getElem? first
    have available := bounds (position,prov) member
    unfold clear_first_action at ok
    simp only [first] at ok
    by_cases crossing : position.bytes < range.start.bytes
    · simp only [crossing,↓reduceIte,Bind.bind,EStateM.bind] at ok
      cases action : clear_boundary_action (fun pos => pos.bytes < range.start.bytes) position prov data before with
      | error err state => simp [action] at ok
      | ok value middle =>
        cases value
        simp only [action] at ok
        obtain ⟨ptrs,frags,count⟩ := boundary_effect original entries _ position prov data available storageFits member before middle old action
        obtain ⟨finalPtrs,finalFrags,finalCount⟩ := last_effect original range finish data entries bounds storageFits middle after frags ok
        exact ⟨by rw [finalPtrs,ptrs],finalFrags,by omega⟩
    · simp only [crossing,↓reduceIte,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure] at ok
      obtain ⟨ptrs,frags,count⟩ := last_effect original range finish data entries bounds storageFits before after old ok
      exact ⟨ptrs,frags,by omega⟩

theorem clear_effect (state updated : ProvenanceMap Prov)
    (range : AllocRange) (finish : Size) (data : Array UInt8)
    (nonzero : range.size.bytes ≠ 0)
    (endpoint : range.endExclusive = .ok finish)
    (bounds : ∀ pointer ∈ state.ptrs, pointer.1.bytes.toNat+8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616)
    (ok : ProvenanceMap.clear range data (Size.ofBytes 8) state = .ok () updated) :
    updated.ptrs = Remaining state.ptrs range finish ∧
    (∀ fragment ∈ updated.byteFragments.getD #[], Origin state (overlappingPointers state range finish) fragment) ∧
    (updated.byteFragments.getD #[]).size ≤ (state.byteFragments.getD #[]).size + 16 := by
  unfold ProvenanceMap.clear at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.rangeEnd" at ok
  simp only [show (range.size.bytes == 0) = false from by simp [nonzero],
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
  have entriesIdentity : entries = overlappingPointers state range finish := entriesEq.symm
  rw [← entriesIdentity]
  let initial := mkMap state.ptrs (state.byteFragments.map fun bytes => removeEntries bytes range.start finish)
  have initialOrigin : ∀ fragment ∈ initial.byteFragments.getD #[], Origin state entries fragment := by
    intro fragment member
    apply Or.inl
    cases fragments : state.byteFragments with
    | none => simp [initial,mkMap,fragments] at member
    | some values =>
      simp only [initial,mkMap,fragments,Option.map_some,Option.getD_some] at member ⊢
      unfold removeEntries at member
      unfold_provenance_at ".Miri.Memory.ProvenanceMap.removeEntries" at member
      exact (Array.mem_filter.mp member).1
  have initialCount : (initial.byteFragments.getD #[]).size ≤ (state.byteFragments.getD #[]).size := by
    cases fragments : state.byteFragments with
    | none => simp [initial,mkMap,fragments]
    | some values =>
      simp only [initial,mkMap,fragments,Option.map_some,Option.getD_some]
      unfold removeEntries
      unfold_provenance ".Miri.Memory.ProvenanceMap.removeEntries"
      exact Array.size_filter_le
  by_cases empty : entries.isEmpty = true
  · simp only [empty,↓reduceIte,EStateM.pure] at ok
    have equal : initial = updated := by injection ok
    subst updated
    refine ⟨?_,initialOrigin,by omega⟩
    change state.ptrs = Remaining state.ptrs range finish
    symm
    apply Array.filter_eq_self.mpr
    intro entry member
    have noEntry : entry ∉ entries := by simp [Array.isEmpty_iff.mp empty]
    have absent : ¬ (UInt64.ofNat (range.start.bytes.toNat - 7) ≤ entry.1.bytes ∧ entry.1.bytes < finish.bytes) := by
      intro geometry
      apply noEntry
      rw [entriesIdentity]
      exact Array.mem_filter.mpr ⟨member,by simpa [overlappingPointers] using geometry⟩
    change (!(decide (UInt64.ofNat (range.start.bytes.toNat - 7) ≤ entry.1.bytes) && decide (entry.1.bytes < finish.bytes))) = true
    by_cases lower : UInt64.ofNat (range.start.bytes.toNat - 7) ≤ entry.1.bytes <;>
      by_cases upper : entry.1.bytes < finish.bytes <;> simp_all
  · simp only [empty,↓reduceIte] at ok
    have action : clear_first_action range finish data entries initial = .ok () updated := by
      unfold clear_first_action clear_last_action clear_boundary_action clear_finish_action
      simp only [pointerFragments,checkedResult,adjustedStart,insertEntry,initial]
      unfold_provenance ".Miri.Memory.ProvenanceMap.checked"
      cases firstEntry : entries[0]? <;> cases lastEntry : entries.back? <;>
        simp only [firstEntry,lastEntry] at ok ⊢ <;> simpa_clear_implementation using ok
    have entryBounds : ∀ pointer ∈ entries, pointer.1.bytes.toNat+8 ≤ data.size := by
      intro pointer member
      exact bounds pointer (mem_overlappingPointers state range finish pointer (entriesIdentity ▸ member))
    obtain ⟨ptrs,origin,count⟩ := first_effect state range finish data entries entryBounds storageFits initial updated initialOrigin action
    exact ⟨ptrs,origin,by omega⟩

end DuplicatePrefix.S02SameDestinationUninitProvenanceClear
