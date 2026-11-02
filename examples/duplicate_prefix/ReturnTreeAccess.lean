import duplicate_prefix.ProtectedBorrowAccess
import duplicate_prefix.ProtectedRelease

/-! Fresh physical return-slot tree facts: release the callee's child protector,
then write through the original parent tag retained by the return place. -/
namespace DuplicatePrefix.ReturnTreeAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess ProtectedBorrowAccess
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

abbrev parentWrittenLocation : LocationTree :=
  ⟨⟨#[some ⟨.Unique, true, .None⟩, some ⟨.Disabled, true, .Write⟩]⟩, {}⟩
abbrev parentNormal (written : Bool) : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, [1]⟩, ⟨some 0, []⟩]⟩
  defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩]
  protectedNodes := []
  locationStates := (childLocation written).perms.data
}
abbrev parentWrittenNormal : Tree.NormalTreeState :=
  {parentNormal false with locationStates := parentWrittenLocation.perms.data}

theorem parent_normal_write (written : Bool) :
    (parentNormal written).performAccess 0 .Write .VisitChildrenOfAccessed =
      ⟨parentWrittenNormal, 0, [⟨0, .LocalAccess⟩, ⟨1, .ForeignAccess⟩], .Completed⟩ := by
  cases written <;> decide

theorem parent_projection (root child : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (protections : ProtectedTags)
    (rootFree : protections.contains root = false) (childFree : protections.contains child = false) :
    source_normal_projection (canonicalChildTree root child locations) (childLocation written) protections =
      parentNormal written := by
  simp_tree_helpers
  simp [canonicalChildTree, childLocation, parentNormal, rootFree, childFree,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, Id.run]

abbrev parentAccess (root child : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (protections : ProtectedTags) (range : ByteRange) :=
  source_tree_access_at (canonicalChildTree root child locations) (childLocation written)
    (some ⟨0⟩) .Write protections .VisitChildrenOfAccessed range

theorem parent_access_local (root child : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (protections : ProtectedTags) (range : ByteRange)
    (rootFree : protections.contains root = false) (childFree : protections.contains child = false) :
    source_access_location (parentAccess root child locations written protections range) = parentWrittenLocation ∧
    source_access_status (parentAccess root child locations written protections range) = none := by
  unfold parentAccess
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, parent_projection root child locations written protections rootFree childFree,
    show (⟨0⟩ : UniIndex).toNat = 0 from rfl, parent_normal_write]
  simp [canonicalChildTree, childLocation, parentNormal, parentWrittenNormal, parentWrittenLocation,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat,
    TreeNode.defaultLocationState, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range'_succ, List.range'_zero]
  simp_tree_helpers
  simp [Id.run, UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]

theorem parent_index (root child : BorTag) (locations : DedupRangeMap LocationTree) :
    (canonicalChildTree root child locations).indexOfTag root = some ⟨0⟩ := by
  simp [BorrowTree.indexOfTag, UniKeyMap.get, ← Array.find?_toList]

theorem parent_write_range (root child : BorTag) (capacity offset len : UInt64) (written : Bool)
    (protections : ProtectedTags) (rootFree : protections.contains root = false)
    (childFree : protections.contains child = false)
    (positive : (0 : UInt64) < len) (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let initial := canonicalChildTree root child (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written))
    let result := initial.performBorrowAccessRange (.concrete root) (Size.ofBytes offset) (Size.ofBytes len)
      .Write protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = canonicalChildTree root child
      (partitionWithInside capacity offset (offset + len) (childLocation written) parentWrittenLocation) := by
  have callback := parent_access_local root child
    (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written)) written protections
    ⟨offset, offset + len⟩ rootFree childFree
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [parent_index]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [RangeMapNonempty.iter_mut_new_nonempty capacity offset len (childLocation written) positive bounds]
  simp [callback.1, callback.2, partition_set_replace, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem parent_write_full (root child : BorTag) (capacity : UInt64) (written : Bool)
    (protections : ProtectedTags) (rootFree : protections.contains root = false)
    (childFree : protections.contains child = false) (positive : (0 : UInt64) < capacity) :
    let initial := canonicalChildTree root child (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written))
    let result := initial.performBorrowAccessRange (.concrete root) Size.ZERO (Size.ofBytes capacity)
      .Write protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = canonicalChildTree root child
      (DedupRangeMap.new (Size.ofBytes capacity) parentWrittenLocation) := by
  have nonzero : capacity ≠ 0 := by intro h; subst capacity; exact (UInt64.lt_irrefl 0) positive
  simpa [Size.ZERO, Size.ofBytes, partitionWithInside, RangeMapNonempty.homogeneous,
    DedupRangeMap.new, nonzero] using
    parent_write_range root child capacity 0 capacity written protections rootFree childFree positive (by simp)

theorem slot_child_write_range (root child : BorTag) (capacity offset len : UInt64) (written : Bool)
    (protections : ProtectedTags) (rootFree : protections.contains root = false)
    (childHeld : protections.contains child = true) (distinct : root ≠ child)
    (positive : (0 : UInt64) < len) (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let initial := canonicalChildTree root child (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written))
    let result := initial.performBorrowAccessRange (.concrete child) (Size.ofBytes offset) (Size.ofBytes len)
      .Write protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = canonicalChildTree root child
      (partitionWithInside capacity offset (offset + len) (childLocation written) (childLocation true)) := by
  have callback := ProtectedBorrowAccess.access2_local root child
    (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written)) written .Write .VisitChildrenOfAccessed
    ⟨offset, offset + len⟩ distinct protections rootFree childHeld
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [canonical_child_index root child _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [RangeMapNonempty.iter_mut_new_nonempty capacity offset len (childLocation written) positive bounds]
  simp [callback.1, callback.2, partition_set_replace, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem slot_child_write_full (root child : BorTag) (capacity : UInt64) (written : Bool)
    (protections : ProtectedTags) (rootFree : protections.contains root = false)
    (childHeld : protections.contains child = true) (distinct : root ≠ child)
    (positive : (0 : UInt64) < capacity) :
    let initial := canonicalChildTree root child (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written))
    let result := initial.performBorrowAccessRange (.concrete child) Size.ZERO (Size.ofBytes capacity)
      .Write protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = canonicalChildTree root child
      (DedupRangeMap.new (Size.ofBytes capacity) (childLocation true)) := by
  have nonzero : capacity ≠ 0 := by intro h; subst capacity; exact (UInt64.lt_irrefl 0) positive
  simpa [Size.ZERO, Size.ofBytes, partitionWithInside, RangeMapNonempty.homogeneous,
    DedupRangeMap.new, nonzero] using
    slot_child_write_range root child capacity 0 capacity written protections rootFree childHeld distinct positive (by simp)

theorem slot_release (root child : BorTag) (capacity : UInt64) (written : Bool)
    (protections : ProtectedTags) (rootFree : protections.contains root = false)
    (childHeld : protections.contains child = true) (distinct : root ≠ child) (nonzero : capacity ≠ 0) :
    let locations := DedupRangeMap.new (Size.ofBytes capacity) (childLocation written)
    (canonicalChildTree root child locations).releaseProtector child protections =
      ⟨canonicalChildTree root child locations, .Released⟩ := by
  dsimp only
  let locations := DedupRangeMap.new (Size.ofBytes capacity) (childLocation written)
  have lookup : locations.index 0 = .ok ⟨⟨0, capacity⟩, childLocation written⟩ := by
    unfold DedupRangeMap.index
    simp_range_helpers
    simp [locations, DedupRangeMap.new, Size.ofBytes, nonzero]
  have setter := BorrowRelease.setAtPos_index_self locations 0 _ lookup
  have callback := ProtectedRelease.end2_local root child locations written ⟨0, capacity⟩ distinct protections rootFree childHeld
  simp only [access2, BorrowRelease.endKind] at callback
  change (canonicalChildTree root child locations).releaseProtector child protections = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [canonical_child_index root child locations distinct]
  have count : locations.entries.size = 1 := by simp [locations, DedupRangeMap.new, Size.ofBytes, nonzero]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, count,
    Nat.sub_zero, Nat.add_sub_cancel, List.range'_succ, List.range'_zero]
  cases written <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at callback <;>
    simp [lookup, setter, callback.1, callback.2, BorrowRelease.canonical_exposure_release,
      distinct, UniValMap.get, UniIndex.toNat, Permission.associatedAccess, Id.run, bind, pure] <;> rfl

#print axioms parent_write_full
#print axioms parent_write_range
#print axioms slot_release
end DuplicatePrefix.ReturnTreeAccess

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ReturnTreeAccess.parent_write_range,
      ``DuplicatePrefix.ReturnTreeAccess.parent_write_full, ``DuplicatePrefix.ReturnTreeAccess.slot_release, ``DuplicatePrefix.ReturnTreeAccess.slot_child_write_full,
      ``DuplicatePrefix.ReturnTreeAccess.slot_child_write_range] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
