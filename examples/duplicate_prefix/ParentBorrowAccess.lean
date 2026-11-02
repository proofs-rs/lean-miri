import duplicate_prefix.BorrowRangeAccess

/-! Actual parent reborrow access after a fresh child protector is installed. -/
namespace DuplicatePrefix.ParentBorrowAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open DuplicatePrefix.BorrowRangeAccess

theorem root_projection_protected (tag : BorTag) (size : Size) (protections : ProtectedTags)
    (unprotected : protections.contains tag = false) :
    source_normal_projection (BorrowTree.new tag size) rootLocation protections = rootNormal := by
  simp_tree_helpers
  simp [BorrowTree.new, rootLocation, rootNormal, UniValMap.insert, UniValMap.extendTo,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    Permission.newDisabled, Permission.newUnique, unprotected,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp_tree_helpers
  simp [Id.run, rootNormal, UniIndex.toNat, bind, pure, unprotected]

abbrev parentAccess (tag : BorTag) (size : Size) (kind : AccessKind)
    (protections : ProtectedTags) (range : ByteRange) :=
  source_tree_access_at (BorrowTree.new tag size) rootLocation (some ⟨0⟩) kind protections
    Tree.ChildrenVisitMode.VisitChildrenOfAccessed range

theorem parent_access_local (tag : BorTag) (size : Size) (kind : AccessKind)
    (protections : ProtectedTags) (range : ByteRange)
    (unprotected : protections.contains tag = false) :
    source_access_location (parentAccess tag size kind protections range) = rootLocation ∧
    source_access_status (parentAccess tag size kind protections range) = none := by
  unfold parentAccess
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, root_projection_protected tag size protections unprotected,
    UniIndex.toNat, root_normal_access]
  simp [rootNormal, rootLocation, BorrowTree.new, BorrowTree.nodeAt, UniValMap.insert, UniValMap.extendTo,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    Permission.newDisabled, Permission.newUnique, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp_tree_helpers
  simp only [root_normal_access]
  simp [Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem parent_range_result (tag : BorTag) (capacity offset len : UInt64) (kind : AccessKind)
    (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let result := (BorrowTree.new tag (Size.ofBytes capacity)).performBorrowAccessRange
      (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) kind protections .VisitChildrenOfAccessed
    result.tree = { BorrowTree.new tag (Size.ofBytes capacity) with
      locations := RangeMapNonempty.intervalPartition capacity offset (offset + len) rootLocation } ∧
      result.status = .Completed := by
  have accessFact := parent_access_local tag (Size.ofBytes capacity) kind protections
    ⟨offset, offset + len⟩ unprotected
  constructor
  all_goals
    unfold BorrowTree.performBorrowAccessRange
    dsimp only
    rw [new_root_index]
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rw [new_locations, RangeMapNonempty.iter_mut_new_nonempty capacity offset len rootLocation
      positiveLength bounds]
    simp [accessFact.1, accessFact.2, partition_set_same, Id.run, bind, pure,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem parent_with_child_protector (rootTag childTag : BorTag)
    (capacity offset len : UInt64) (kind : AccessKind) (distinct : rootTag ≠ childTag)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let result := (BorrowTree.new rootTag (Size.ofBytes capacity)).performBorrowAccessRange
      (.concrete rootTag) (Size.ofBytes offset) (Size.ofBytes len) kind (childProtected childTag)
      .VisitChildrenOfAccessed
    result.tree = { BorrowTree.new rootTag (Size.ofBytes capacity) with
      locations := RangeMapNonempty.intervalPartition capacity offset (offset + len) rootLocation } ∧
      result.status = .Completed := by
  have unprotected : (childProtected childTag).contains rootTag = false := by
    simp [childProtected, ProtectedTags.contains, ProtectedTags.get, Array.find?_singleton,
      distinct, Ne.symm distinct]
  exact parent_range_result rootTag capacity offset len kind (childProtected childTag)
    unprotected positiveLength bounds

#print axioms parent_with_child_protector
end DuplicatePrefix.ParentBorrowAccess
