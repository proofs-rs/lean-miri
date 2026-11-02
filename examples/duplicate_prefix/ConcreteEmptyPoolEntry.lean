import duplicate_prefix.EmptyForestSharedAppend
import duplicate_prefix.GeneralBorrowZeroProtectedDefaultConstructor
import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot
import duplicate_prefix.GeneralBorrowCanonicalParentDepth
import duplicate_prefix.GeneralBorrowGcVacantClean
import duplicate_prefix.GeneralBorrowFreshStagePool

namespace DuplicatePrefix.ConcreteEmptyPoolEntry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshAnchor
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

set_option autoImplicit false in
/-- Initial metadata for the ACTUAL allocator branch of a zero protected Default child.
Sparse vacancy and per-location permission Clean are separate fields. -/
structure Input (tree : BorrowTree) (parentTag tag : BorTag) where
  parent : UniIndex
  parentNode : TreeNode
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  tagged : tree.tagMapping.get parentTag = some parent
  present : tree.nodeAt parent = some parentNode
  fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag
  slot : Slot tree depth parent
  clean : GeneralBorrowFreshFutureClean.Clean tree (GeneralBorrowFreshMetadataChildSlot.index slot)

private theorem slotVacant (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parent : UniIndex) (slot : Slot tree depth parent) :
    tree.nodes.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none := by
  cases slot with
  | append noFree aligned fits =>
    change tree.nodes.get (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex) = none
    have endEq : (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat = tree.nodes.data.size := by
      simp only [UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    unfold UniValMap.get
    simp [endEq]
  | reuse child available bounded missing slack => exact missing

namespace Input
variable {tree : BorrowTree} {parentTag tag : BorTag}
def index (input : Input tree parentTag tag) : UniIndex := GeneralBorrowFreshMetadataChildSlot.index input.slot
def free (input : Input tree parentTag tag) : Array UniIndex :=
  match input.slot with
  | .append .. => tree.tagMapping.deassigned
  | .reuse .. => tree.tagMapping.deassigned.pop
def mapping (input : Input tree parentTag tag) : UniKeyMap BorTag :=
  ⟨tree.tagMapping.mapping.push (tag,input.index),input.free⟩
def stage (input : Input tree parentTag tag) : BorrowTree :=
  {(attached tree input.index input.parent input.parentNode (GeneralBorrowFreshChild.child tag input.parent)) with tagMapping := input.mapping}
def after (input : Input tree parentTag tag) : BorrowTree := (sourceUpdateSifa input.stage input.parent .None).1

theorem vacant (input : Input tree parentTag tag) : tree.nodes.get input.index = none := by
  cases selected : input.slot with
  | append noFree aligned fits =>
    have endEq : (GeneralBorrowFreshMetadataChildSlot.index input.slot).toNat = tree.nodes.data.size := by
      simp only [selected,GeneralBorrowFreshMetadataChildSlot.index,UniIndex.toNat,UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    unfold UniValMap.get
    simp [index,endEq]
  | reuse child available bounded missing slack => simpa only [index,selected,GeneralBorrowFreshMetadataChildSlot.index] using missing

/-- Both actual protected Default allocator branches finish and produce the exact SIFA-updated
tree. No successful tag insertion, SIFA result or constructor is an input. -/
theorem child (input : Input tree parentTag tag) (offset : UInt64) :
    tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true = ⟨input.after,.ok ()⟩ := by
  have success : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () ∧
      (tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree = input.after := by
    cases selected : input.slot with
    | append noFree aligned fits =>
      simpa only [after,stage,mapping,free,index,selected,GeneralBorrowFreshMetadataChildSlot.index] using
        GeneralBorrowZeroProtectedDefaultConstructor.append tree input.depth parentTag tag input.parent input.parentNode
          input.tagged input.present input.fresh noFree aligned fits offset
    | reuse child available bounded missing slack =>
      simpa only [after,stage,mapping,free,index,selected,GeneralBorrowFreshMetadataChildSlot.index] using
        GeneralBorrowZeroProtectedDefaultConstructor.reuse tree input.depth parentTag tag input.parent child input.parentNode
          input.tagged input.present input.fresh available bounded missing slack offset
  cases raw : tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true with
  | mk current outcome =>
    simp only [raw] at success
    cases success.1
    rw [success.2]

private noncomputable def attachedDepth (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parent : UniIndex) (node : TreeNode) (present : tree.nodeAt parent = some node)
    (tag : BorTag) (slot : Slot tree depth parent) :
    GeneralBorrowExposure.ParentDepth (attached tree (GeneralBorrowFreshMetadataChildSlot.index slot) parent node (GeneralBorrowFreshChild.child tag parent)).nodes := by
  cases slot with
  | append noFree aligned fits =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    have endEq : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    change GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent node (GeneralBorrowFreshChild.child tag parent))
    exact attached_depth tree.nodes depth index parent node (GeneralBorrowFreshChild.child tag parent) endEq present rfl
  | reuse child available bounded missing slack =>
    change GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes child parent node (GeneralBorrowFreshChild.child tag parent))
    exact GeneralBorrowFreshReuseNode.attached_depth tree.nodes depth child parent node
      (GeneralBorrowFreshChild.child tag parent) bounded missing present rfl slack

noncomputable def afterDepth (input : Input tree parentTag tag) : GeneralBorrowExposure.ParentDepth input.after.nodes := by
  let stageDepth : GeneralBorrowExposure.ParentDepth input.stage.nodes :=
    attachedDepth tree input.depth input.parent input.parentNode input.present tag input.slot
  exact GeneralBorrowFreshMetadata.parent_depth input.stage input.after
    (GeneralBorrowSifaView.preserves input.stage input.parent .None) stageDepth

theorem future_clean (input : Input tree parentTag tag) (query : UniIndex)
    (clean : GeneralBorrowFreshFutureClean.Clean tree query) : GeneralBorrowFreshFutureClean.Clean input.after query :=
  GeneralBorrowFreshFutureClean.sifa_preserves input.stage input.parent .None query clean

theorem mapping_after (input : Input tree parentTag tag) : input.after.tagMapping = input.mapping :=
  GeneralBorrowFreshMetadata.mapping input.stage input.after (GeneralBorrowSifaView.preserves input.stage input.parent .None)

theorem stage_new (input : Input tree parentTag tag) : input.stage.nodeAt input.index = some (GeneralBorrowFreshChild.child tag input.parent) := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes input.index input.parent input.parentNode input.vacant input.present
  change ((tree.nodes.insert input.index (GeneralBorrowFreshChild.child tag input.parent)).insert input.parent (updatedParent input.parentNode input.index)).get input.index = _
  rw [GeneralBorrowFreshLocation.get_other _ input.parent input.index _ (Ne.symm different),GeneralBorrowFreshLocation.get_same]

theorem node_exists (input : Input tree parentTag tag) :
    ∃ node, input.after.nodeAt input.index = some node ∧ node.isExposed = false := by
  obtain ⟨node,lookup,_,_,_,_,exposed⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .None input.index (GeneralBorrowFreshChild.child tag input.parent) input.stage_new
  exact ⟨node,lookup,exposed⟩

/-- The actual release scan succeeds for the new lazy protected child in either
allocator branch, using explicit Clean rather than inferring it from vacancy. -/
theorem release (input : Input tree parentTag tag) (protections : ProtectedTags) :
    input.after.releaseProtector tag protections = ⟨input.after,.Released⟩ := by
  obtain ⟨node,present,exposed⟩ := input.node_exists
  have tagged : input.after.indexOfTag tag = some input.index := by
    unfold BorrowTree.indexOfTag
    rw [input.mapping_after]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag input.fresh input.index input.free
  exact EmptyForestUnmaterializedRelease.release input.after tag input.index node tagged present exposed
    (input.future_clean input.index input.clean) protections
end Input

/-- Form a branch-parametric Input from a coherent arbitrary finite free pool.
Rank normalization derives strict reuse slack. VacantClean is an independent
permission invariant and is not discharged by node vacancy. -/
def factory (tree : BorrowTree) (parentTag tag : BorTag) (parent : UniIndex) (node : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some node)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool tree.nodes tree.tagMapping.deassigned)
    (accounting : GeneralBorrowFreshStagePool.Accounting tree)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) : Input tree parentTag tag := by
  let normalized := GeneralBorrowCanonicalParentDepth.normalize tree.nodes depth
  let slot := GeneralBorrowCanonicalParentDepth.slot tree depth parent node present pool
    (GeneralBorrowFreshStagePool.empty_aligned tree accounting) (fun _ => fits)
  exact {
    parent := parent,parentNode := node,depth := normalized,tagged := tagged,present := present,fresh := fresh,slot := slot
    clean := clean _ (slotVacant tree normalized parent slot) }

end DuplicatePrefix.ConcreteEmptyPoolEntry
