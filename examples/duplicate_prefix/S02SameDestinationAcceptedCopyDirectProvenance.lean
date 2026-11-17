import duplicate_prefix.S04ReturnProvenanceClear
import duplicate_prefix.S02SameDestinationUninitProvenanceInput
import duplicate_prefix.S02SameDestinationAcceptedCopyPointerBounds

namespace DuplicatePrefix.S02SameDestinationAcceptedCopyDirectProvenance
open Miri.ABI Miri.Memory
open ProvenanceCopy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {Prov : Type}
open S02SameDestinationUninitProvenanceInput

theorem endpoint_begin_end_order_direct (self : ProvenanceMap Prov) (capacity : Nat)
    (valid : DirectInput self capacity) (base finish : Size)
    (rangeOrder : base.bytes ≤ finish.bytes)
    (position : Size) (prov : Prov)
    (endAt : (endpointPointers self finish.bytes)[0]? = some (position, prov))
    (distinct : (((endpointPointers self base.bytes)[0]?).map fun (begin, _) => begin.bytes != position.bytes).getD true = true) :
    base.bytes ≤ position.bytes ∧
      (∀ begin beginProv, (endpointPointers self base.bytes)[0]? = some (begin, beginProv) →
        begin.bytes.toNat + 8 ≤ position.bytes.toNat) := by
  have endMember := Array.mem_of_getElem? endAt
  have endFacts := (endpoint_member_iff self finish (position, prov)).mp endMember
  cases beginAt : (endpointPointers self base.bytes)[0]? with
  | none =>
    have noCross := endpoint_none_no_cross self base.bytes beginAt
    have placement := noCross (position, prov) endFacts.1
    refine ⟨?_, ?_⟩
    · simp only [UInt64.le_iff_toNat_le] at rangeOrder ⊢
      dsimp only at endFacts placement
      omega
    · intro begin beginProv impossible
      simp [beginAt] at impossible
  | some pair =>
    obtain ⟨begin, beginProv⟩ := pair
    have beginMember := Array.mem_of_getElem? beginAt
    have beginFacts := (endpoint_member_iff self base (begin, beginProv)).mp beginMember
    have unequal : begin.bytes ≠ position.bytes := by simpa [beginAt] using distinct
    have disjoint := pairwise_intervals_disjoint self.ptrs.toList ((DirectInput.pointerOrder valid))
      (begin, beginProv) (position, prov) (by simpa using beginFacts.1) (by simpa using endFacts.1)
    have before : begin.bytes.toNat + 8 ≤ position.bytes.toNat := by
      rcases disjoint with equal | before | after
      · have same := congrArg (fun entry : Size × Prov => entry.1.bytes) equal
        exact False.elim (unequal same)
      · exact before
      · simp only [UInt64.le_iff_toNat_le] at rangeOrder
        dsimp only at beginFacts endFacts after
        omega
    refine ⟨?_, ?_⟩
    · simp only [UInt64.le_iff_toNat_le]
      dsimp only at beginFacts
      omega
    · intro other otherProv otherAt
      have equal : (begin, beginProv) = (other, otherProv) := Option.some.inj otherAt
      cases equal
      exact before

theorem pointer_count (self : ProvenanceMap Prov) (capacity : Nat)
    (valid : DirectInput self capacity) : self.ptrs.size ≤ capacity := by
  apply ordered_entry_count
  · exact (DirectInput.pointerOrder valid).imp (fun h => by omega)
  · intro entry member
    have bound := (DirectInput.pointerBounds valid) entry member
    omega

/-- Whole pointer snapshots fit as complete eight-byte pointers; crossing
pointers are represented by byte fragments instead. -/
theorem shifted_whole_bounds (self : ProvenanceMap Prov) (base finish : Size) (n : UInt64)
    (finishNat : finish.bytes.toNat = base.bytes.toNat+n.toNat) :
    ∀ entry ∈ shift_entries base (whole_entries self base finish n),
      entry.1.bytes.toNat+8 ≤ n.toNat := by
  intro entry member
  unfold shift_entries at member
  obtain ⟨original,sourceMember,rfl⟩ := Array.mem_map.mp member
  unfold whole_entries at sourceMember
  split at sourceMember
  · rename_i large
    have selected := (Array.mem_filter.mp sourceMember).2
    simp only [Bool.and_eq_true,decide_eq_true_eq] at selected
    obtain ⟨lower,upper⟩ := selected
    rw [shift_nat base original lower]
    have enough : (7 : UInt64) ≤ finish.bytes := by
      simp only [UInt64.le_iff_toNat_le, show (8 : UInt64).toNat = 8 from rfl, show (7 : UInt64).toNat = 7 from rfl] at large ⊢
      omega
    have subtraction := UInt64.toNat_sub_of_le _ _ enough
    simp only [UInt64.lt_iff_toNat_lt,UInt64.le_iff_toNat_le] at upper lower
    rw [subtraction] at upper
    change original.1.bytes.toNat < finish.bytes.toNat-7 at upper
    omega
  · simp at sourceMember

theorem prepare_interval_with_pointer_bounds (self : ProvenanceMap Prov) (base finish : Size) (n : UInt64)
    (data : Array UInt8) (valid : DirectInput self data.size)
    (storageFits : data.size < 18446744073709551616)
    (endpoint : (allocRange base (Size.ofBytes n)).endExclusive = .ok finish)
    (finishNat : finish.bytes.toNat = base.bytes.toNat + n.toNat) :
    ∃ snapshot,
      self.prepareCopy (allocRange base (Size.ofBytes n)) data (Size.ofBytes 8) = .ok snapshot ∧
      IntervalSnapshotFits snapshot n self.ptrs.size (self.byteFragments.getD #[]).size ∧
      (∀ entry ∈ snapshot.ptrs, entry.1.bytes.toNat+8 ≤ n.toNat) := by
  let beginOpt := (endpointPointers self base.bytes)[0]?
  let endOpt := (endpointPointers self finish.bytes)[0]?
  have baseQuery : self.rangePtrs (allocRange base Size.ZERO) (Size.ofBytes 8) = .ok (endpointPointers self base.bytes) := by
    exact range_ptrs_exact self _ base (zero_endpoint base)
  have endQuery : self.rangePtrs (allocRange finish Size.ZERO) (Size.ofBytes 8) = .ok (endpointPointers self finish.bytes) := by
    exact range_ptrs_exact self _ finish (zero_endpoint finish)
  have rangeOrder : base.bytes ≤ finish.bytes := by
    simp only [UInt64.le_iff_toNat_le]
    omega
  have beginBounds : ∀ position prov, beginOpt = some (position, prov) → position.bytes.toNat + 8 ≤ data.size := by
    intro position prov atBegin
    have member := Array.mem_of_getElem? atBegin
    exact (DirectInput.pointerBounds valid) (position, prov)
      ((endpoint_member_iff self base (position, prov)).mp member).1
  obtain ⟨beginEntries, beginOk, beginInside, beginOrigin, beginCount⟩ :=
    begin_stage_exists base finish beginOpt data beginBounds storageFits
  let old := old_entries self base finish
  let middle := beginEntries ++ old
  have middleInside : AbsoluteBounds base finish middle := by
    intro entry member
    rcases Array.mem_append.mp member with fromBegin | fromOld
    · exact beginInside entry fromBegin
    · exact old_entry_bounds self base finish entry fromOld
  have endBounds : ∀ position prov, endOpt = some (position, prov) → position.bytes.toNat + 8 ≤ data.size := by
    intro position prov atEnd
    exact (DirectInput.pointerBounds valid) (position, prov)
      ((endpoint_member_iff self finish (position, prov)).mp (Array.mem_of_getElem? atEnd)).1
  have distinctOrder : ∀ position prov, endOpt = some (position, prov) →
      (beginOpt.map fun (begin, _) => begin.bytes != position.bytes).getD true = true →
      base.bytes ≤ position.bytes ∧ (∀ begin beginProv, beginOpt = some (begin, beginProv) → begin.bytes.toNat + 8 ≤ position.bytes.toNat) := by
    intro position prov atEnd distinct
    exact endpoint_begin_end_order_direct self data.size valid base finish rangeOrder position prov atEnd distinct
  have middleBefore : ∀ position prov, endOpt = some (position, prov) →
      (beginOpt.map fun (begin, _) => begin.bytes != position.bytes).getD true = true →
      ∀ entry ∈ middle, entry.1.bytes < position.bytes := by
    intro position prov atEnd distinct entry member
    rcases Array.mem_append.mp member with fromBegin | fromOld
    · obtain ⟨begin, beginProv, atBegin, upper⟩ := beginOrigin entry fromBegin
      have before := (distinctOrder position prov atEnd distinct).2 begin beginProv atBegin
      simp only [UInt64.lt_iff_toNat_lt]
      omega
    · exact old_entries_before_endpoint self base finish position prov atEnd
        ((DirectInput.fragmentsAvoidPointers valid)) entry fromOld
  obtain ⟨endEntries, endOk, endInside, endCount⟩ := end_stage_exists base finish beginOpt endOpt data middle
    middleInside endBounds (fun position prov atEnd distinct => (distinctOrder position prov atEnd distinct).1) middleBefore storageFits
  have wholeOk := whole_stage_exact self base finish n finishNat
  have wholeInside := whole_entries_bounds self base finish n finishNat
  have wholeCount := whole_entries_count self base finish n
  have rangeBytes := range_bytes_exact self _ finish endpoint
  have collectOld := collect_entries_exact base old (shift_entries base beginEntries)
    (fun entry member => (old_entry_bounds self base finish entry member).1)
  have collectedMiddle : collect_entries base old (shift_entries base beginEntries) = .ok (shift_entries base middle) := by
    simpa [middle, shift_entries, Array.map_append] using collectOld
  by_cases present : beginOpt.isSome || endOpt.isSome || self.byteFragments.isSome
  · refine ⟨⟨shift_entries base (whole_entries self base finish n), shift_entries base endEntries⟩, ?_, ?_⟩
    · rw [prepare_stages_exact]
      unfold prepare_stages
      simp only [endpoint, Except.mapError, Bind.bind, Except.bind]
      change (whole_stage self base finish n >>= _) = _
      rw [wholeOk]
      dsimp only [allocRange]
      change (self.rangePtrs (allocRange base Size.ZERO) (Size.ofBytes 8) >>= _) = _
      rw [baseQuery]
      simp only [Bind.bind, Except.bind]
      change (self.rangePtrs (allocRange finish Size.ZERO) (Size.ofBytes 8) >>= _) = _
      rw [endQuery]
      simp only [Bind.bind, Except.bind]
      change (if beginOpt.isSome || endOpt.isSome || self.byteFragments.isSome then _ else _) = _
      rw [if_pos present, beginOk]
      simp only [Bind.bind, Except.bind]
      change (self.rangeBytes (allocRange base (Size.ofBytes n)) >>= _) = _
      rw [rangeBytes]
      simp only [Bind.bind, Except.bind]
      change (collect_entries base old (shift_entries base beginEntries) >>= _) = _
      rw [collectedMiddle]
      simp only [Bind.bind, Except.bind]
      change (end_stage base finish beginOpt endOpt data (shift_entries base middle) >>= _) = _
      rw [endOk]
      rfl
    · refine ⟨?_, shifted_whole_bounds self base finish n finishNat⟩
      refine ⟨shifted_absolute_bounds base finish n _ wholeInside finishNat,
        shifted_absolute_bounds base finish n _ endInside finishNat, ?_, ?_⟩
      · simpa [shift_entries] using wholeCount
      · have oldCount : old.size ≤ (self.byteFragments.getD #[]).size := Array.size_filter_le
        simp only [shift_entries, Array.size_map]
        dsimp only [middle] at endCount
        simp only [Array.size_append] at endCount
        omega
  · refine ⟨⟨shift_entries base (whole_entries self base finish n), #[]⟩, ?_, ?_⟩
    · rw [prepare_stages_exact]
      unfold prepare_stages
      simp only [endpoint, Except.mapError, Bind.bind, Except.bind]
      change (whole_stage self base finish n >>= _) = _
      rw [wholeOk]
      dsimp only [allocRange]
      change (self.rangePtrs (allocRange base Size.ZERO) (Size.ofBytes 8) >>= _) = _
      rw [baseQuery]
      simp only [Bind.bind, Except.bind]
      change (self.rangePtrs (allocRange finish Size.ZERO) (Size.ofBytes 8) >>= _) = _
      rw [endQuery]
      simp only [Bind.bind, Except.bind]
      change (if beginOpt.isSome || endOpt.isSome || self.byteFragments.isSome then _ else _) = _
      simp [present, Pure.pure, Except.pure]
    · refine ⟨?_, shifted_whole_bounds self base finish n finishNat⟩
      refine ⟨shifted_absolute_bounds base finish n _ wholeInside finishNat, by simp, ?_, by simp⟩
      simpa [shift_entries] using wholeCount

theorem interval_copy_pointer_bounds_exists (self : ProvenanceMap Prov) (base : Size) (n : UInt64)
    (data : Array UInt8) (valid : DirectInput self data.size)
    (storageFits : data.size + 32 < 18446744073709551616)
    (copyFits : base.bytes.toNat + n.toNat + n.toNat ≤ data.size) :
    let destination := Size.ofBytes (base.bytes + n)
    ∃ snapshot cleared updated,
      self.prepareCopy (allocRange base (Size.ofBytes n)) data (Size.ofBytes 8) = .ok snapshot ∧
      ProvenanceMap.clear (allocRange destination (Size.ofBytes n)) data (Size.ofBytes 8) self = .ok () cleared ∧
      ProvenanceMap.applyCopy snapshot (allocRange destination (Size.ofBytes n)) 1 cleared = .ok () updated ∧
      (∀ entry ∈ updated.ptrs, entry.1.bytes.toNat+8 ≤ data.size) := by
  dsimp only
  let destination := Size.ofBytes (base.bytes + n)
  have firstFits : base.bytes.toNat + n.toNat < 2 ^ 64 := by omega
  have destinationNat : destination.bytes.toNat = base.bytes.toNat + n.toNat := by
    simp [destination, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt firstFits]
  have sourceEnd := DuplicatePrefix.source_end base n firstFits
  obtain ⟨snapshot, prepared,⟨pointerOffsets, fragmentOffsets, pointerCount, fragmentCount⟩,wholeBounds⟩ :=
    prepare_interval_with_pointer_bounds self base destination n data valid (by omega) sourceEnd destinationNat
  have lastFits : destination.bytes.toNat + n.toNat < 2 ^ 64 := by omega
  have destinationEnd := DuplicatePrefix.source_end destination n lastFits
  obtain ⟨cleared, clearedOk⟩ := clear_exists self _ _ data destinationEnd ((DirectInput.pointerBounds valid)) (by omega)
  have totalPointers := pointer_count self data.size valid
  have totalFragments := (DirectInput.fragmentCount valid)
  obtain ⟨updated, applied⟩ := apply_copy_once_exists snapshot (allocRange destination (Size.ofBytes n))
    (by omega) (by omega)
    (by intro entry member; have bound := pointerOffsets entry member; change entry.1.bytes.toNat + destination.bytes.toNat < 2 ^ 64; omega)
    (by intro entry member; have bound := fragmentOffsets entry member; change entry.1.bytes.toNat + destination.bytes.toNat < 2 ^ 64; omega)
    cleared
  have clearedBounds : S02SameDestinationAcceptedCopyPointerBounds.Bounds data.size cleared := by
    intro entry member
    exact (DirectInput.pointerBounds valid) entry
      (S04ReturnProvenanceClear.clear_pointer_subset self cleared _ _ data destinationEnd clearedOk entry member)
  have outputBounds := S02SameDestinationAcceptedCopyPointerBounds.apply_copy_once_pointer_bounds
    snapshot (allocRange destination (Size.ofBytes n)) data.size (by omega) (by omega)
    wholeBounds (by simpa only [allocRange,Size.ofBytes] using (show destination.bytes.toNat+n.toNat ≤ data.size by omega))
    (by omega) cleared updated clearedBounds applied
  exact ⟨snapshot, cleared, updated, prepared, clearedOk, applied,outputBounds⟩

end DuplicatePrefix.S02SameDestinationAcceptedCopyDirectProvenance
