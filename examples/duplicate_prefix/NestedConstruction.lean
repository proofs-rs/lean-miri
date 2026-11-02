import duplicate_prefix.NestedBorrowAccess
import duplicate_prefix.ChildConstructor

/-! Source constructor bridges for the additional reference tags created by
`len` and `as_mut_ptr`. All requested ranges are symbolic. -/
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
namespace DuplicatePrefix.NestedConstruction
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess MixedRangeMap RangeMapNonempty NestedBorrowAccess

private theorem whole_end {α : Type} (capacity offset finish : UInt64) (outside inside : α) :
    range_split_index (partitionWithInside capacity offset finish outside inside).entries
      (intervalPosition offset) finish id =
      .ok ((partitionWithInside capacity offset finish outside inside).entries, false) := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;> simp_all [partitionWithInside, intervalPosition, homogeneous]
private theorem whole_slice {α : Type} (capacity offset finish : UInt64) (outside inside : α) :
    range_selected_slice (partitionWithInside capacity offset finish outside inside).entries
      (intervalPosition offset) (intervalPosition offset + 1) = .ok #[⟨⟨offset, finish⟩, inside⟩] := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;> simp_all [partitionWithInside, intervalPosition, homogeneous]

theorem iterMut_partition {α : Type} [DecidableEq α]
    (capacity offset len : UInt64) (outside inside : α)
    (positive : (0 : UInt64) < len) (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (partitionWithInside capacity offset (offset + len) outside inside).iterMut
      (Size.ofBytes offset) (Size.ofBytes len) =
      ⟨partitionWithInside capacity offset (offset + len) outside inside,
        #[intervalPosition offset], #[⟨⟨offset, offset + len⟩, inside⟩], .ok ()⟩ := by
  have fits : offset.toNat + len.toNat < 2^64 := by have limit := capacity.toNat_lt; omega
  have finishNat : (offset + len).toNat = offset.toNat + len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have beforeFinish : offset < offset + len := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero, finishNat] at *
    omega
  have nonempty : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  exact iter_mut_existing_segment (partitionWithInside capacity offset (offset + len) outside inside)
    (Size.ofBytes offset) (Size.ofBytes len) (offset + len) (intervalPosition offset) inside nonempty
    (initial_search capacity offset (offset + len) outside inside beforeFinish)
    (initial_start capacity offset (offset + len) outside inside) (checked_end_add offset len fits)
    (initial_segment capacity offset (offset + len) outside inside)
    (whole_end capacity offset (offset + len) outside inside)
    (whole_slice capacity offset (offset + len) outside inside)

private theorem partition_get {α : Type} (capacity offset finish : UInt64) (outside inside : α) :
    (partitionWithInside capacity offset finish outside inside).entries[intervalPosition offset]? =
      some ⟨⟨offset, finish⟩, inside⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, intervalPosition, homogeneous]
private theorem partition_update {α : Type} (capacity offset finish : UInt64) (outside inside replacement : α) :
    range_update_at (partitionWithInside capacity offset finish outside inside).entries
      (intervalPosition offset) ⟨⟨offset, finish⟩, replacement⟩ =
      .ok (partitionWithInside capacity offset finish outside replacement).entries := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_updates <;> simp_all [partitionWithInside, intervalPosition, homogeneous]

theorem modifyRange_partition {α : Type} [DecidableEq α]
    (capacity offset len : UInt64) (outside inside : α) (modify : ByteRange → α → α)
    (positive : (0 : UInt64) < len) (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (partitionWithInside capacity offset (offset + len) outside inside).modifyRange
      (Size.ofBytes offset) (Size.ofBytes len) modify =
      ⟨partitionWithInside capacity offset (offset + len) outside (modify ⟨offset, offset + len⟩ inside),
        #[intervalPosition offset], #[⟨⟨offset, offset + len⟩, modify ⟨offset, offset + len⟩ inside⟩], .ok ()⟩ := by
  have prepared : (partitionWithInside capacity offset (offset + len) outside inside).iterMutWithClone
      (Size.ofBytes offset) (Size.ofBytes len) id =
      ⟨partitionWithInside capacity offset (offset + len) outside inside,
        #[intervalPosition offset], #[⟨⟨offset, offset + len⟩, inside⟩], .ok ()⟩ :=
    iterMut_partition capacity offset len outside inside positive bounds
  unfold DedupRangeMap.modifyRange DedupRangeMap.modifyRangeWithClone
  rw [prepared]
  dsimp only
  simp only [← Array.forIn_toList]
  simp [initial_segment, partition_update, Id.run, bind, pure, Except.bind, Except.pure]

def sharedPolicy (held : Bool) : RetagPolicy.NewPermission :=
  ⟨.Frozen, .Cell, .Frozen, if held then some .StrongProtector else none⟩
def twoPhasePolicy : RetagPolicy.NewPermission :=
  ⟨.ReservedFrz false, .ReservedIM, .ReservedFrz false, none⟩

theorem shared_default_policy :
    RetagPolicy.create ⟨true, true, true⟩ .Shared .Default ⟨false, false⟩ = some (sharedPolicy false) := by decide

theorem shared_entry_policy :
    RetagPolicy.create ⟨true, true, true⟩ .Shared .FnEntry ⟨false, false⟩ = some (sharedPolicy true) := by decide

theorem mutable_two_phase_policy :
    RetagPolicy.create ⟨true, true, true⟩ .Mutable .TwoPhase ⟨false, false⟩ = some twoPhasePolicy := by decide

abbrev frozenRead : Tree.LocationState := ⟨.Frozen, true, .Read⟩
abbrev frozenNone : Tree.LocationState := ⟨.Frozen, true, .None⟩
abbrev mutableRead : Tree.LocationState := ⟨.ReservedFrz false, true, .Read⟩
abbrev mutableNone : Tree.LocationState := ⟨.ReservedFrz false, true, .None⟩

theorem shared_initial (held : Bool) :
    RetagPolicy.initialLocationState (sharedPolicy held) true = .ok frozenRead := by
  cases held <;> decide

theorem mutable_two_phase_initial :
    RetagPolicy.initialLocationState twoPhasePolicy true = .ok mutableRead := by decide

abbrev location3 (parentRead : Bool) : LocationTree :=
  ⟨⟨#[some ⟨.Unique, true, .None⟩, some mutableNone,
    some (if parentRead then frozenNone else frozenRead)]⟩, {}⟩
abbrev location4 (released : Bool) : LocationTree :=
  ⟨⟨#[some ⟨.Unique, true, .None⟩, some mutableNone, some frozenNone,
    some (if released then frozenNone else frozenRead)]⟩, {}⟩
abbrev location5 (parentRead : Bool) : LocationTree :=
  ⟨⟨#[some ⟨.Unique, true, .None⟩, some mutableNone, some frozenNone, some frozenNone,
    some (if parentRead then mutableNone else mutableRead)]⟩, {}⟩

abbrev stageNode (tags : Fin 6 → BorTag) (index : Fin 6) (parent : Option UniIndex)
    (children : Array UniIndex) (permission : Permission) (sifa : IdempotentForeignAccess) : TreeNode :=
  { tag := tags index, parent, children, defaultInitialPermission := permission, defaultInitialSifa := sifa }

abbrev tree2 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) :=
  canonicalChildTree (tags 0) (tags 1) locations

abbrev tree3 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) : BorrowTree := {
  tagMapping := { mapping := #[(tags 0, ⟨0⟩), (tags 1, ⟨1⟩), (tags 2, ⟨2⟩)] }
  nodes := { data := #[some (stageNode tags 0 (none) #[⟨1⟩] (.Disabled) .None), some (stageNode tags 1 (some ⟨0⟩) #[⟨2⟩] (.ReservedFrz false) .None), some (stageNode tags 2 (some ⟨1⟩) #[] (.Frozen) .Read)] }
  locations
  roots := #[⟨0⟩]
}

abbrev tree4 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) : BorrowTree := {
  tagMapping := { mapping := #[(tags 0, ⟨0⟩), (tags 1, ⟨1⟩), (tags 2, ⟨2⟩), (tags 3, ⟨3⟩)] }
  nodes := { data := #[some (stageNode tags 0 (none) #[⟨1⟩] (.Disabled) .None), some (stageNode tags 1 (some ⟨0⟩) #[⟨2⟩] (.ReservedFrz false) .None), some (stageNode tags 2 (some ⟨1⟩) #[⟨3⟩] (.Frozen) .Read), some (stageNode tags 3 (some ⟨2⟩) #[] (.Frozen) .Read)] }
  locations
  roots := #[⟨0⟩]
}

abbrev tree5 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) : BorrowTree := {
  tagMapping := { mapping := #[(tags 0, ⟨0⟩), (tags 1, ⟨1⟩), (tags 2, ⟨2⟩), (tags 3, ⟨3⟩), (tags 4, ⟨4⟩)] }
  nodes := { data := #[some (stageNode tags 0 (none) #[⟨1⟩] (.Disabled) .None), some (stageNode tags 1 (some ⟨0⟩) #[⟨2⟩, ⟨4⟩] (.ReservedFrz false) .None), some (stageNode tags 2 (some ⟨1⟩) #[⟨3⟩] (.Frozen) .Read), some (stageNode tags 3 (some ⟨2⟩) #[] (.Frozen) .Read), some (stageNode tags 4 (some ⟨1⟩) #[] (.ReservedFrz false) .Read)] }
  locations
  roots := #[⟨0⟩]
}

abbrev preFinalTree (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) : BorrowTree := {
  tagMapping := { mapping := #[(tags 0, ⟨0⟩), (tags 1, ⟨1⟩), (tags 2, ⟨2⟩), (tags 3, ⟨3⟩), (tags 4, ⟨4⟩), (tags 5, ⟨5⟩)] }
  nodes := { data := #[some (stageNode tags 0 (none) #[⟨1⟩] (.Disabled) .None), some (stageNode tags 1 (some ⟨0⟩) #[⟨2⟩, ⟨4⟩] (.ReservedFrz false) .None), some (stageNode tags 2 (some ⟨1⟩) #[⟨3⟩] (.Frozen) .Read), some (stageNode tags 3 (some ⟨2⟩) #[] (.Frozen) .Read), some (stageNode tags 4 (some ⟨1⟩) #[⟨5⟩] (.ReservedFrz false) .Read), some (stageNode tags 5 (some ⟨4⟩) #[] (.ReservedFrz false) .None)] }
  locations
  roots := #[⟨0⟩]
}

private theorem sifa_tree3_unchanged (tags : Fin 6 → BorTag) (capacity offset finish : UInt64) :
    let tree := tree3 tags (partitionWithInside capacity offset finish rootLocation (location3 false))
    source_sifa_update tree ⟨1⟩ .Read = (tree, .ok ()) := by
  let tree := tree3 tags (partitionWithInside capacity offset finish rootLocation (location3 false))
  change source_sifa_update tree ⟨1⟩ .Read = (tree, .ok ())
  unfold_sifa
  simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, ForIn.forIn]
  name_range_scan
  have first : scan () (none, tree, some (⟨1⟩ : UniIndex), 0, true) =
      .yield (none, tree, some (⟨1⟩ : UniIndex), 0, false) := by
    by_cases atStart : offset = 0 <;> by_cases atEnd : finish = capacity <;>
      simp [scan, tree, tree3, stageNode, partitionWithInside, rootLocation,
        location3, location4, location5, mutableNone, mutableRead, frozenRead, frozenNone,
        homogeneous, atStart, atEnd,
        UniValMap.get, UniValMap.insert, UniValMap.extendTo, UniValMap.size, UniIndex.toNat,
        DedupRangeMap.iterAll, DedupRangeMap.modifyAll,
        IdempotentForeignAccess.ensureNoStrongerThan, IdempotentForeignAccess.rank,
        Id.run, bind, pure]
  have last : scan () (none, tree, some (⟨1⟩ : UniIndex), 0, false) =
      .done (none, tree, some (⟨1⟩ : UniIndex), 0, false) := by
    simp [scan, bind, pure]
  have doneScan := loop_one_update scan _ _ first last
  simp only [doneScan, Id.run, bind, pure]

private theorem sifa_tree4_unchanged (tags : Fin 6 → BorTag) (capacity offset finish : UInt64) :
    let tree := tree4 tags (partitionWithInside capacity offset finish rootLocation (location4 false))
    source_sifa_update tree ⟨2⟩ .Read = (tree, .ok ()) := by
  let tree := tree4 tags (partitionWithInside capacity offset finish rootLocation (location4 false))
  change source_sifa_update tree ⟨2⟩ .Read = (tree, .ok ())
  unfold_sifa
  simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, ForIn.forIn]
  name_range_scan
  have first : scan () (none, tree, some (⟨2⟩ : UniIndex), 0, true) =
      .yield (none, tree, some (⟨2⟩ : UniIndex), 0, false) := by
    by_cases atStart : offset = 0 <;> by_cases atEnd : finish = capacity <;>
      simp [scan, tree, tree4, stageNode, partitionWithInside, rootLocation,
        location3, location4, location5, mutableNone, mutableRead, frozenRead, frozenNone,
        homogeneous, atStart, atEnd,
        UniValMap.get, UniValMap.insert, UniValMap.extendTo, UniValMap.size, UniIndex.toNat,
        DedupRangeMap.iterAll, DedupRangeMap.modifyAll,
        IdempotentForeignAccess.ensureNoStrongerThan, IdempotentForeignAccess.rank,
        Id.run, bind, pure]
  have last : scan () (none, tree, some (⟨2⟩ : UniIndex), 0, false) =
      .done (none, tree, some (⟨2⟩ : UniIndex), 0, false) := by
    simp [scan, bind, pure]
  have doneScan := loop_one_update scan _ _ first last
  simp only [doneScan, Id.run, bind, pure]

private theorem sifa_tree5_unchanged (tags : Fin 6 → BorTag) (capacity offset finish : UInt64) :
    let tree := tree5 tags (partitionWithInside capacity offset finish rootLocation (location5 false))
    source_sifa_update tree ⟨1⟩ .Read = (tree, .ok ()) := by
  let tree := tree5 tags (partitionWithInside capacity offset finish rootLocation (location5 false))
  change source_sifa_update tree ⟨1⟩ .Read = (tree, .ok ())
  unfold_sifa
  simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, ForIn.forIn]
  name_range_scan
  have first : scan () (none, tree, some (⟨1⟩ : UniIndex), 0, true) =
      .yield (none, tree, some (⟨1⟩ : UniIndex), 0, false) := by
    by_cases atStart : offset = 0 <;> by_cases atEnd : finish = capacity <;>
      simp [scan, tree, tree5, stageNode, partitionWithInside, rootLocation,
        location3, location4, location5, mutableNone, mutableRead, frozenRead, frozenNone,
        homogeneous, atStart, atEnd,
        UniValMap.get, UniValMap.insert, UniValMap.extendTo, UniValMap.size, UniIndex.toNat,
        DedupRangeMap.iterAll, DedupRangeMap.modifyAll,
        IdempotentForeignAccess.ensureNoStrongerThan, IdempotentForeignAccess.rank,
        Id.run, bind, pure]
  have last : scan () (none, tree, some (⟨1⟩ : UniIndex), 0, false) =
      .done (none, tree, some (⟨1⟩ : UniIndex), 0, false) := by
    simp [scan, bind, pure]
  have doneScan := loop_one_update scan _ _ first last
  simp only [doneScan, Id.run, bind, pure]

private theorem final_sifa (tags : Fin 6 → BorTag) (capacity offset finish : UInt64) :
    let before := preFinalTree tags (partitionWithInside capacity offset finish rootLocation (nestedLocation false))
    let after := nestedTree tags (partitionWithInside capacity offset finish rootLocation (nestedLocation false))
    source_sifa_update before ⟨4⟩ .None = (after, .ok ()) := by
  let before := preFinalTree tags (partitionWithInside capacity offset finish rootLocation (nestedLocation false))
  let after := nestedTree tags (partitionWithInside capacity offset finish rootLocation (nestedLocation false))
  change source_sifa_update before ⟨4⟩ .None = (after, .ok ())
  unfold_sifa
  simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, ForIn.forIn]
  name_range_scan
  have first : scan () (none, before, some (⟨4⟩ : UniIndex), 0, true) =
      .yield (none, after, some (⟨1⟩ : UniIndex), 1, true) := by
    by_cases atStart : offset = 0 <;> by_cases atEnd : finish = capacity <;>
      simp [scan, before, after, preFinalTree, nestedTree, stageNode, partitionWithInside, rootLocation,
        nestedLocation, reserved, frozenBranch, homogeneous, atStart, atEnd,
        UniValMap.get, UniValMap.insert, UniValMap.extendTo, UniValMap.size, UniIndex.toNat,
        DedupRangeMap.iterAll, DedupRangeMap.modifyAll,
        IdempotentForeignAccess.ensureNoStrongerThan, IdempotentForeignAccess.rank,
        Id.run, bind, pure]
  have second : scan () (none, after, some (⟨1⟩ : UniIndex), 1, true) =
      .yield (none, after, some (⟨1⟩ : UniIndex), 1, false) := by
    by_cases atStart : offset = 0 <;> by_cases atEnd : finish = capacity <;>
      simp [scan, after, nestedTree, partitionWithInside, rootLocation,
        nestedLocation, reserved, frozenBranch, homogeneous, atStart, atEnd,
        UniValMap.get, UniValMap.insert, UniValMap.extendTo, UniValMap.size, UniIndex.toNat,
        DedupRangeMap.iterAll, DedupRangeMap.modifyAll,
        IdempotentForeignAccess.ensureNoStrongerThan, IdempotentForeignAccess.rank,
        Id.run, bind, pure]
  have last : scan () (none, after, some (⟨1⟩ : UniIndex), 1, false) =
      .done (none, after, some (⟨1⟩ : UniIndex), 1, false) := by
    simp [scan, bind, pure]
  have final := loop_one_update scan _ _ second last
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [first, final, Id.run, bind, pure]

private theorem insert_tag2 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    (tree2 tags locations).tagMapping.insert (tags 2) =
      .Inserted (tree3 tags locations).tagMapping ⟨2⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp [tree2, tree3, canonicalChildTree, UniKeyMap.insert, UniKeyMap.get,
    UniIndex.ofNat?, eqTags, ← Array.find?_toList]

theorem new_shared2 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (tree2 tags (partitionWithInside capacity offset (offset + len) rootLocation (childLocation false))).newChild
      (Size.ofBytes offset) (.concrete (tags 1)) (tags 2)
      (DedupRangeMap.new (Size.ofBytes len) frozenRead) .Frozen false =
      ⟨tree3 tags (partitionWithInside capacity offset (offset + len) rootLocation (location3 false)), .ok ()⟩ := by
  have nonzero : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  have locationUpdate := modifyRange_partition capacity offset len rootLocation (childLocation false)
    (fun _ location => {location with perms := location.perms.insert ⟨2⟩ frozenRead}) positive bounds
  have updateValue : {childLocation false with perms := (childLocation false).perms.insert ⟨2⟩ frozenRead} =
      location3 false := by
    simp [childLocation, location3, mutableNone, frozenRead, UniValMap.insert, UniValMap.extendTo, UniIndex.toNat]
  rw [updateValue] at locationUpdate
  unfold BorrowTree.newChild
  rw [insert_tag2 tags distinct]
  simp only [← Array.forIn_toList]
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp only [tree2, tree3, canonicalChildTree, stageNode] at *
  simp_new_source
  have final := sifa_tree3_unchanged tags capacity offset (offset + len)
  exact ⟨congrArg Prod.fst final, congrArg Prod.snd final⟩

private theorem insert_tag3 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    (tree3 tags locations).tagMapping.insert (tags 3) =
      .Inserted (tree4 tags locations).tagMapping ⟨3⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp [tree3, tree4, UniKeyMap.insert, UniKeyMap.get, UniIndex.ofNat?, eqTags, ← Array.find?_toList]

theorem new_shared_entry3 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (tree3 tags (partitionWithInside capacity offset (offset + len) rootLocation (location3 true))).newChild
      (Size.ofBytes offset) (.concrete (tags 2)) (tags 3)
      (DedupRangeMap.new (Size.ofBytes len) frozenRead) .Frozen true =
      ⟨tree4 tags (partitionWithInside capacity offset (offset + len) rootLocation (location4 false)), .ok ()⟩ := by
  have nonzero : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  have locationUpdate := modifyRange_partition capacity offset len rootLocation (location3 true)
    (fun _ location => {location with perms := location.perms.insert ⟨3⟩ frozenRead}) positive bounds
  have updateValue : {location3 true with perms := (location3 true).perms.insert ⟨3⟩ frozenRead} = location4 false := by
    simp [location3, location4, location5, mutableNone, mutableRead, frozenRead, frozenNone,
      UniValMap.insert, UniValMap.extendTo, UniIndex.toNat]
  rw [updateValue] at locationUpdate
  unfold BorrowTree.newChild
  rw [insert_tag3 tags distinct]
  simp only [← Array.forIn_toList]
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp only [tree3, tree4, stageNode] at *
  simp_new_source
  have final := sifa_tree4_unchanged tags capacity offset (offset + len)
  exact ⟨congrArg Prod.fst final, congrArg Prod.snd final⟩

#print axioms new_shared_entry3
private theorem insert_tag4 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    (tree4 tags locations).tagMapping.insert (tags 4) =
      .Inserted (tree5 tags locations).tagMapping ⟨4⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp [tree4, tree5, UniKeyMap.insert, UniKeyMap.get, UniIndex.ofNat?, eqTags, ← Array.find?_toList]

theorem new_mutable4 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (tree4 tags (partitionWithInside capacity offset (offset + len) rootLocation (location4 true))).newChild
      (Size.ofBytes offset) (.concrete (tags 1)) (tags 4)
      (DedupRangeMap.new (Size.ofBytes len) mutableRead) (.ReservedFrz false) false =
      ⟨tree5 tags (partitionWithInside capacity offset (offset + len) rootLocation (location5 false)), .ok ()⟩ := by
  have nonzero : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  have locationUpdate := modifyRange_partition capacity offset len rootLocation (location4 true)
    (fun _ location => {location with perms := location.perms.insert ⟨4⟩ mutableRead}) positive bounds
  have updateValue : {location4 true with perms := (location4 true).perms.insert ⟨4⟩ mutableRead} = location5 false := by
    simp [location3, location4, location5, mutableNone, mutableRead, frozenRead, frozenNone,
      UniValMap.insert, UniValMap.extendTo, UniIndex.toNat]
  rw [updateValue] at locationUpdate
  unfold BorrowTree.newChild
  rw [insert_tag4 tags distinct]
  simp only [← Array.forIn_toList]
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp only [tree4, tree5, stageNode] at *
  simp_new_source
  have final := sifa_tree5_unchanged tags capacity offset (offset + len)
  exact ⟨congrArg Prod.fst final, congrArg Prod.snd final⟩

#print axioms new_mutable4
private theorem insert_tag5 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    (tree5 tags locations).tagMapping.insert (tags 5) =
      .Inserted (preFinalTree tags locations).tagMapping ⟨5⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp [tree5, preFinalTree, UniKeyMap.insert, UniKeyMap.get,
    UniIndex.ofNat?, eqTags, ← Array.find?_toList]

theorem new_mutable_entry5 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (tree5 tags (partitionWithInside capacity offset (offset + len) rootLocation (location5 true))).newChild
      (Size.ofBytes offset) (.concrete (tags 4)) (tags 5)
      (DedupRangeMap.new (Size.ofBytes len) mutableNone) (.ReservedFrz false) true =
      ⟨nestedTree tags (partitionWithInside capacity offset (offset + len) rootLocation (nestedLocation false)), .ok ()⟩ := by
  have nonzero : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  have locationUpdate := modifyRange_partition capacity offset len rootLocation (location5 true)
    (fun _ location => {location with perms := location.perms.insert ⟨5⟩ mutableNone}) positive bounds
  have updateValue : {location5 true with perms := (location5 true).perms.insert ⟨5⟩ mutableNone} =
      nestedLocation false := by
    simp [location5, nestedLocation, reserved, frozenBranch, mutableNone, frozenNone,
      UniValMap.insert, UniValMap.extendTo, UniIndex.toNat]
  rw [updateValue] at locationUpdate
  unfold BorrowTree.newChild
  rw [insert_tag5 tags distinct]
  simp only [← Array.forIn_toList]
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp only [tree5, preFinalTree, nestedTree, stageNode] at *
  simp_new_source
  have final := final_sifa tags capacity offset (offset + len)
  exact ⟨congrArg Prod.fst final, congrArg Prod.snd final⟩

#print axioms new_mutable_entry5
#print axioms new_shared2
#print axioms modifyRange_partition
end DuplicatePrefix.NestedConstruction

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.NestedConstruction.new_shared2,
      ``DuplicatePrefix.NestedConstruction.new_shared_entry3,
      ``DuplicatePrefix.NestedConstruction.new_mutable4,
      ``DuplicatePrefix.NestedConstruction.new_mutable_entry5,
      ``DuplicatePrefix.NestedConstruction.modifyRange_partition] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
