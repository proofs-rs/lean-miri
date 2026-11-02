import duplicate_prefix.MixedBorrowAccess

/-! Actual Tree Borrows accesses for the source-shaped nested helper topology.
The pinned root MIR creates a shared reborrow before `len` and a mutable
reborrow before `as_mut_ptr`; each helper FnEntry adds one child. Construction
and call/return connection are separate from these exact access lemmas. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace DuplicatePrefix.NestedBorrowAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess MixedRangeMap

abbrev reserved (written : Bool) : Tree.LocationState :=
  ⟨if written then .Unique else .ReservedFrz false, true, .None⟩
abbrev frozenBranch (written : Bool) : Tree.LocationState :=
  ⟨if written then .Disabled else .Frozen, true, if written then .Write else .None⟩

abbrev nestedLocation (written : Bool) : LocationTree :=
  ⟨⟨#[some ⟨.Unique, true, .None⟩, some (reserved written),
    some (frozenBranch written), some (frozenBranch written),
    some (reserved written), some (reserved written)]⟩, {}⟩

abbrev nestedNormal (written : Bool) : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, [1]⟩, ⟨some 0, [2, 4]⟩, ⟨some 1, [3]⟩,
    ⟨some 2, []⟩, ⟨some 1, [5]⟩, ⟨some 4, []⟩]⟩
  defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩,
    ⟨.Frozen, false, .Read⟩, ⟨.Frozen, false, .Read⟩,
    ⟨.ReservedFrz false, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩]
  protectedNodes := [1]
  locationStates := (nestedLocation written).perms.data
}

theorem nested_normal_status (written : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) :
    ((nestedNormal written).performAccess 5 kind mode).status = .Completed := by
  cases written <;> cases kind <;> cases mode <;> decide

theorem nested_normal_states (written : Bool) (kind : AccessKind) :
    ((nestedNormal written).performAccess 5 kind .VisitChildrenOfAccessed).tree.locationStates =
      (nestedLocation (written || kind == .Write)).perms.data := by
  cases written <;> cases kind <;> decide

abbrev nestedVisits (written : Bool) (kind : AccessKind) : List Tree.TraversalEvent :=
  [⟨5, .LocalAccess⟩, ⟨4, .LocalAccess⟩, ⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩] ++
    if !written && kind == .Write then [⟨3, .ForeignAccess⟩, ⟨2, .ForeignAccess⟩] else []

theorem nested_normal_access (written : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) :
    (nestedNormal written).performAccess 5 kind mode =
      ⟨nestedNormal (written || kind == .Write), 0, nestedVisits written kind, .Completed⟩ := by
  cases written <;> cases kind <;> cases mode <;> decide

abbrev nestedTree (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) : BorrowTree := {
  tagMapping := { mapping := #[(tags 0, ⟨0⟩), (tags 1, ⟨1⟩), (tags 2, ⟨2⟩),
    (tags 3, ⟨3⟩), (tags 4, ⟨4⟩), (tags 5, ⟨5⟩)] }
  nodes := { data := #[
    some { tag := tags 0, parent := none, children := #[⟨1⟩], defaultInitialPermission := .Disabled, defaultInitialSifa := .None },
    some { tag := tags 1, parent := some ⟨0⟩, children := #[⟨2⟩, ⟨4⟩], defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None },
    some { tag := tags 2, parent := some ⟨1⟩, children := #[⟨3⟩], defaultInitialPermission := .Frozen, defaultInitialSifa := .Read },
    some { tag := tags 3, parent := some ⟨2⟩, children := #[], defaultInitialPermission := .Frozen, defaultInitialSifa := .Read },
    some { tag := tags 4, parent := some ⟨1⟩, children := #[⟨5⟩], defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None },
    some { tag := tags 5, parent := some ⟨4⟩, children := #[], defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None }] }
  locations
  roots := #[⟨0⟩]
}
abbrev nestedProtected (tags : Fin 6 → BorTag) : ProtectedTags := childProtected (tags 1)

theorem nested_index (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    (nestedTree tags locations).indexOfTag (tags 5) = some ⟨5⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j := ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp only [BorrowTree.indexOfTag, nestedTree, UniKeyMap.get]
  rw [← Array.find?_toList]
  simp [eqTags]

theorem nested_projection (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (written : Bool) :
    source_normal_projection (nestedTree tags locations) (nestedLocation written) (nestedProtected tags) =
      nestedNormal written := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j := ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp_tree_helpers
  simp [nestedTree, nestedLocation, nestedNormal, nestedProtected, childProtected,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Array.find?_singleton, eqTags,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, Id.run]

abbrev nestedAccess (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (kind : AccessKind) (range : ByteRange) :=
  source_tree_access_at (nestedTree tags locations) (nestedLocation written)
    (some ⟨5⟩) kind (nestedProtected tags) .VisitChildrenOfAccessed range

theorem nested_access_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (written : Bool) (kind : AccessKind) (range : ByteRange) :
    source_access_location (nestedAccess tags locations written kind range) =
      nestedLocation (written || kind == .Write) ∧
    source_access_status (nestedAccess tags locations written kind range) = none := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  unfold nestedAccess
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, nested_projection tags distinct locations written,
    show (⟨5⟩ : UniIndex).toNat = 5 from rfl, nested_normal_access]
  simp [nestedTree, nestedLocation, nestedNormal, nestedVisits, nestedProtected, childProtected,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Array.find?_singleton, eqTags,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  try simp only [nested_normal_access]
  simp [Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  all_goals cases written <;> cases kind <;>
    simp [nestedVisits, nestedNormal, nestedLocation, reserved, frozenBranch, Id.run,
      UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
      BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range'_succ, List.range'_zero]

abbrev nestedNormalWithHelper (written helperProtected : Bool) : Tree.NormalTreeState :=
  { nestedNormal written with protectedNodes := if helperProtected then [1, 5] else [1] }

abbrev nestedProtectedWithHelper (tags : Fin 6 → BorTag) (helperProtected : Bool) : ProtectedTags :=
  if helperProtected then ⟨#[(tags 1, .StrongProtector), (tags 5, .StrongProtector)]⟩
  else nestedProtected tags

theorem nested_normal_with_helper_access (written helperProtected : Bool) (kind : AccessKind)
    (mode : Tree.ChildrenVisitMode) :
    (nestedNormalWithHelper written helperProtected).performAccess 5 kind mode =
      ⟨nestedNormalWithHelper (written || kind == .Write) helperProtected,
        0, nestedVisits written kind, .Completed⟩ := by
  cases written <;> cases helperProtected <;> cases kind <;> cases mode <;> decide

theorem nested_projection_with_helper (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (written helperProtected : Bool) :
    source_normal_projection (nestedTree tags locations) (nestedLocation written)
      (nestedProtectedWithHelper tags helperProtected) = nestedNormalWithHelper written helperProtected := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  cases helperProtected
  · simpa [nestedProtectedWithHelper, nestedNormalWithHelper] using nested_projection tags distinct locations written
  · simp_tree_helpers
    simp [nestedTree, nestedLocation, nestedNormal, nestedNormalWithHelper, nestedProtectedWithHelper,
      UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
      ProtectedTags.contains, ProtectedTags.get, eqTags, ← Array.find?_toList,
      bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range'_succ, List.range'_zero, Id.run]

theorem nested_min_exposed (tags : Fin 6 → BorTag)
    (locations : DedupRangeMap LocationTree) :
    source_min_exposed (nestedTree tags locations) ⟨5⟩ = none := by
  unfold_min_exposed
  simp only [Id.run, bind, pure, ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have first : scan () (none, #[⟨5⟩], 0, none) =
      .yield (none, #[], 1, none) := by
    simp [scan, UniValMap.size, UniValMap.get, UniIndex.toNat, bind, pure,
      ← Array.forIn_toList]
  have last : scan () (none, #[], 1, none) = .done (none, #[], 1, none) := by
    simp [scan, UniValMap.size, bind, pure]
  have loopDone := RangeMapNonempty.loop_one_update scan _ _ first last
  simp [loopDone, Id.run, bind, pure]

abbrev nestedAccessWithHelper (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree)
    (written helperProtected : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) (range : ByteRange) :=
  source_tree_access_at (nestedTree tags locations) (nestedLocation written)
    (some ⟨5⟩) kind (nestedProtectedWithHelper tags helperProtected) mode range

theorem nested_access_local_with_helper (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (written helperProtected : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) (range : ByteRange) :
    source_access_location (nestedAccessWithHelper tags locations written helperProtected kind mode range) =
      nestedLocation (written || kind == .Write) ∧
    source_access_status (nestedAccessWithHelper tags locations written helperProtected kind mode range) = none := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  unfold nestedAccessWithHelper
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, nested_projection_with_helper tags distinct locations written helperProtected,
    show (⟨5⟩ : UniIndex).toNat = 5 from rfl, nested_normal_with_helper_access, nested_min_exposed]
  simp [nestedTree, nestedLocation, nestedNormalWithHelper, nestedNormal, nestedVisits, nestedProtectedWithHelper, nestedProtected, childProtected,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Array.find?_singleton, eqTags,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  try simp only [nested_normal_with_helper_access, nested_min_exposed]
  simp [nested_min_exposed, Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  all_goals cases written <;> cases helperProtected <;> cases kind <;> cases mode <;>
    simp [nestedVisits, nestedNormalWithHelper, nestedNormal, nestedLocation, reserved, frozenBranch, Id.run,
      UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
      BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range'_succ, List.range'_zero]

private theorem nested_index_copy (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree)
    (distinct : Function.Injective tags) :
    (nestedTree tags locations).indexOfTag (tags 5) = some ⟨5⟩ := nested_index tags distinct locations
private theorem nested_access_local_copy (tags : Fin 6 → BorTag)
    (locations : DedupRangeMap LocationTree) (written : Bool) (kind : AccessKind) (range : ByteRange)
    (distinct : Function.Injective tags) :
    source_access_location (nestedAccess tags locations written kind range) =
      nestedLocation (written || kind == .Write) ∧
    source_access_status (nestedAccess tags locations written kind range) = none :=
  nested_access_local tags distinct locations written kind range

 theorem read_prefix (tags : Fin 6 → BorTag) (capacity offset len finish : UInt64)
    (distinct : Function.Injective tags) (positive : (0 : UInt64) < len)
    (interior : offset.toNat + len.toNat < finish.toNat) :
    let initial := nestedTree tags
      (partitionWithInside capacity offset finish rootLocation (nestedLocation false))
    let result := initial.performBorrowAccessRange (.concrete (tags 5))
      (Size.ofBytes offset) (Size.ofBytes len) .Read (nestedProtected tags) .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = nestedTree tags
      (splitInside capacity offset finish (offset + len) rootLocation (nestedLocation false)) := by
  have accessFact := nested_access_local_copy tags
    (partitionWithInside capacity offset finish rootLocation (nestedLocation false))
    false .Read ⟨offset, offset + len⟩ distinct
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [readNotWrite, Bool.false_or] at accessFact
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [nested_index_copy tags _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [iterMut_initial_prefix capacity offset len finish rootLocation (nestedLocation false) positive interior]
  simp [accessFact.1, accessFact.2, split_set_same, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem write_prefix (tags : Fin 6 → BorTag) (capacity offset finish first len : UInt64)
    (distinct : Function.Injective tags) (positive : (0 : UInt64) < len)
    (afterStart : offset < first) (bounds : first.toNat + len.toNat ≤ finish.toNat) :
    let initial := nestedTree tags
      (splitInside capacity offset finish first rootLocation (nestedLocation false))
    let result := initial.performBorrowAccessRange (.concrete (tags 5))
      (Size.ofBytes first) (Size.ofBytes len) .Write (nestedProtected tags) .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = nestedTree tags
      (doubleSplit capacity offset finish first (first + len) rootLocation
        (nestedLocation false) (nestedLocation true) (nestedLocation false)) := by
  have accessFact := nested_access_local_copy tags
    (splitInside capacity offset finish first rootLocation (nestedLocation false))
    false .Write ⟨first, first + len⟩ distinct
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [nested_index_copy tags _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [iterMut_second_prefix capacity offset finish first len rootLocation (nestedLocation false)
    positive afterStart bounds]
  simp [accessFact.1, accessFact.2, double_set_middle, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem canonical_slice_copy_borrow (tags : Fin 6 → BorTag)
    (capacity offset sliceLen n : UInt64) (distinct : Function.Injective tags)
    (positive : (0 : UInt64) < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ capacity.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat) :
    let initial := nestedTree tags
      (partitionWithInside capacity offset (offset + sliceLen) rootLocation (nestedLocation false))
    let read := initial.performBorrowAccessRange (.concrete (tags 5))
      (Size.ofBytes offset) (Size.ofBytes n) .Read (nestedProtected tags) .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete (tags 5))
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write (nestedProtected tags) .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      write.tree = nestedTree tags
        (doubleSplit capacity offset (offset + sliceLen) (offset + n) ((offset + n) + n)
          rootLocation (nestedLocation false) (nestedLocation true) (nestedLocation false)) := by
  have fits : offset.toNat + sliceLen.toNat < 2^64 := by have limit := capacity.toNat_lt; omega
  have endNat : (offset + sliceLen).toNat = offset.toNat + sliceLen.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have prefixFits : offset.toNat + n.toNat < 2^64 := by omega
  have middleNat : (offset + n).toNat = offset.toNat + n.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt prefixFits]
  have posNat : 0 < n.toNat := by simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
  have prefixInterior : offset.toNat + n.toNat < (offset + sliceLen).toNat := by omega
  have afterStart : offset < offset + n := by simp only [UInt64.lt_iff_toNat_lt, middleNat]; omega
  have suffixBounds : (offset + n).toNat + n.toNat ≤ (offset + sliceLen).toNat := by omega
  have readFact := read_prefix tags capacity offset n (offset + sliceLen)
    distinct positive prefixInterior
  have writeFact := write_prefix tags capacity offset (offset + sliceLen) (offset + n) n
    distinct positive afterStart suffixBounds
  dsimp only at readFact writeFact ⊢
  exact ⟨readFact.1, by rw [readFact.2]; exact writeFact.1, by rw [readFact.2]; exact writeFact.2⟩


#print axioms canonical_slice_copy_borrow
#print axioms nested_normal_access
#print axioms nested_access_local
#print axioms nested_normal_status
#print axioms nested_normal_states
#print axioms nested_index
#print axioms nested_projection
end DuplicatePrefix.NestedBorrowAccess

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.NestedBorrowAccess.canonical_slice_copy_borrow,
      ``DuplicatePrefix.NestedBorrowAccess.nested_access_local,
      ``DuplicatePrefix.NestedBorrowAccess.nested_normal_access,
      ``DuplicatePrefix.NestedBorrowAccess.nested_access_local_with_helper] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
