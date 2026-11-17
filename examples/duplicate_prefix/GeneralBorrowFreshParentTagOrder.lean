import duplicate_prefix.GeneralBorrowWildcardParentTagOrder
import duplicate_prefix.GeneralBorrowFreshMetadata
import duplicate_prefix.GeneralBorrowFreshMetadataChildAttach
import duplicate_prefix.GeneralBorrowFreshMetadataChildReuseGraph
namespace DuplicatePrefix.GeneralBorrowFreshParentTagOrder
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFreshGraph
open GeneralBorrowExposure
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem transfer (before after : BorrowTree) (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (order : ParentTagOrder before) : ParentTagOrder after := by
  intro child node present parent parentNode edge parentPresent
  obtain ⟨old,oldPresent,tag,parents,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm child node present
  obtain ⟨oldParent,oldParentPresent,parentTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm parent parentNode parentPresent
  have bounded := order child old oldPresent parent oldParent (parents.trans edge) oldParentPresent
  simpa only [tag,parentTag] using bounded

private theorem old_fields (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode node : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (different : query ≠ index) (present : (attached tree index parent parentNode newNode).nodeAt query = some node) :
    ∃ old, tree.nodeAt query = some old ∧ old.tag = node.tag ∧ old.parent = node.parent := by
  by_cases isParent : query = parent
  · subst query
    rw [GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant parentPresent] at present
    cases present
    exact ⟨parentNode,parentPresent,rfl,rfl⟩
  · rw [GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode newNode vacant parentPresent isParent different] at present
    exact ⟨node,present,rfl,rfl⟩

private theorem retained_fields (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode old : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (present : tree.nodeAt query = some old) :
    ∃ node, (attached tree index parent parentNode newNode).nodeAt query = some node ∧ node.tag = old.tag ∧ node.parent = old.parent := by
  by_cases isParent : query = parent
  · subst query
    cases Option.some.inj (present.symm.trans parentPresent)
    exact ⟨_,GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant parentPresent,rfl,rfl⟩
  · have different : query ≠ index := by intro equal;subst query;change tree.nodes.get index = some old at present;rw [vacant] at present;cases present
    exact ⟨old,(GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode newNode vacant parentPresent isParent different).trans present,rfl,rfl⟩

/-- Actual topology insertion at any vacant allocator slot preserves an existing
parent/tag order when the new tag is at least its parent's tag. Permissions,
SIFA, exposure and global protector policy do not enter this graph law. -/
theorem attached_order (tree : BorrowTree) (depth : ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (edge : newNode.parent = some parent) (freshOrder : parentNode.tag.value ≤ newNode.tag.value) :
    ParentTagOrder (attached tree index parent parentNode newNode) := by
  intro child node present ancestor ancestorNode childEdge ancestorPresent
  change (attached tree index parent parentNode newNode).nodeAt child = some node at present
  change (attached tree index parent parentNode newNode).nodeAt ancestor = some ancestorNode at ancestorPresent
  by_cases isNew : child = index
  · subst child
    rw [GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index parent parentNode newNode vacant parentPresent] at present
    cases present
    have equal : ancestor = parent := Option.some.inj (childEdge.symm.trans edge)
    subst ancestor
    rw [GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant parentPresent] at ancestorPresent
    cases ancestorPresent
    exact freshOrder
  · obtain ⟨old,oldPresent,tag,parents⟩ := old_fields tree index parent child parentNode newNode node vacant parentPresent isNew present
    obtain ⟨oldParent,oldParentPresent,_⟩ := depth.parent child old oldPresent ancestor (parents.trans childEdge)
    obtain ⟨next,nextPresent,nextTag,_⟩ := retained_fields tree index parent ancestor parentNode newNode oldParent vacant parentPresent oldParentPresent
    have equal : next = ancestorNode := Option.some.inj (nextPresent.symm.trans ancestorPresent)
    subst next
    have bounded := order child old oldPresent ancestor oldParent (parents.trans childEdge) oldParentPresent
    simpa only [tag,←nextTag] using bounded
/-- An append index is vacant even though it is outside the old array. -/
theorem vacant_at_end (tree : BorrowTree) (index : UniIndex) (atEnd : index.toNat = tree.nodes.data.size) :
    tree.nodes.get index = none := by
  unfold UniValMap.get
  rw [show tree.nodes.data[index.toNat]? = none from Array.getElem?_eq_none (by omega)]

/-- Graph order passes through range materialization and the actual SIFA result
using its already-proved structural frame. Applies equally to Frozen shared and
ReservedFrz mutable policies and to append/reuse allocator slots. -/
theorem staged_order (tree : BorrowTree) (depth : ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (edge : newNode.parent = some parent) (freshOrder : parentNode.tag.value ≤ newNode.tag.value)
    (mapping : UniKeyMap BorTag)
    (locations : Miri.DataStructures.DedupRangeMap LocationTree) (after : BorrowTree)
    (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape
      (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations)) :
    ParentTagOrder after := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations
  have stageOrder : ParentTagOrder stage := by
    change ParentTagOrder (attached tree index parent parentNode newNode)
    exact attached_order tree depth order index parent parentNode newNode vacant parentPresent edge freshOrder
  exact transfer stage after same stageOrder

end DuplicatePrefix.GeneralBorrowFreshParentTagOrder
