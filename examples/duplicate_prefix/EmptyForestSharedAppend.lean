import duplicate_prefix.EmptyForestSharedZeroBorrow
import duplicate_prefix.EmptyForestUnmaterializedRelease
import duplicate_prefix.GeneralBorrowSifaExactReadFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildSifa

namespace DuplicatePrefix.EmptyForestSharedAppend
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
structure Input (tree : BorrowTree) (parentTag tag : BorTag) where
  parent : UniIndex
  parentNode : TreeNode
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  tagged : tree.tagMapping.get parentTag = some parent
  present : tree.nodeAt parent = some parentNode
  fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag
  noFree : tree.tagMapping.deassigned.back? = none
  aligned : tree.tagMapping.mapping.size = tree.nodes.data.size
  fits : tree.tagMapping.mapping.size ≤ 4294967295
  clean : ∀ position (valid : position < tree.locations.entries.size),
    tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ = none

namespace Input
variable {tree : BorrowTree} {parentTag tag : BorTag}
def index (input : Input tree parentTag tag) : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
def mapping (input : Input tree parentTag tag) : UniKeyMap BorTag :=
  ⟨tree.tagMapping.mapping.push (tag,input.index),tree.tagMapping.deassigned⟩
def stage (input : Input tree parentTag tag) : BorrowTree :=
  { (attached tree input.index input.parent input.parentNode (sharedNode tag input.parent)) with
    tagMapping := input.mapping }
def after (input : Input tree parentTag tag) : BorrowTree :=
  (sourceUpdateSifa input.stage input.parent .Read).1

theorem atEnd (input : Input tree parentTag tag) : input.index.toNat = tree.nodes.data.size := by
  simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by have := input.fits;omega : tree.tagMapping.mapping.size < 2^32)]
  exact input.aligned

/-- Actual shared zero constructor for either ordinary or FnEntry shared policy;
append and ancestor-SIFA completion are derived from graph/resource data. -/
theorem child (input : Input tree parentTag tag) (offset : UInt64) (protectedValue : Bool) :
    tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) sharedState) .Frozen protectedValue = ⟨input.after,.ok ()⟩ := by
  have success := GeneralBorrowZeroSharedConstructor.append tree input.depth parentTag tag input.parent input.parentNode
    input.tagged input.present input.fresh input.noFree input.aligned input.fits offset protectedValue
  cases raw : tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) sharedState) .Frozen protectedValue with
  | mk current outcome =>
    simp only [raw] at success
    rcases success with ⟨outcomeEq,treeEq⟩
    cases outcomeEq
    dsimp only [after,stage,mapping,index] at treeEq ⊢
    rw [treeEq]

def afterDepth (input : Input tree parentTag tag) : GeneralBorrowExposure.ParentDepth input.after.nodes := by
  have stageDepth : GeneralBorrowExposure.ParentDepth input.stage.nodes := by
    simpa only [stage,attached] using
      (attached_depth tree.nodes input.depth input.index input.parent input.parentNode (sharedNode tag input.parent)
        input.atEnd input.present rfl)
  exact GeneralBorrowFreshMetadata.parent_depth input.stage input.after
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read) stageDepth

theorem afterClean (input : Input tree parentTag tag) :
    ∀ position (valid : position < input.after.locations.entries.size),
      input.after.locations.entries[position].data.perms.get input.index = none :=
  GeneralBorrowSifaExactReadFrame.sifa_exact input.stage input.parent input.index none
    (by intro state impossible;cases impossible) input.clean

/-- The newly protected len-reference is released by the real per-location
scan and exposure branch. No release-success equation is an input field. -/
theorem release (input : Input tree parentTag tag) (protections : ProtectedTags) :
    input.after.releaseProtector tag protections = ⟨input.after,.Released⟩ := by
  have beforePresent : input.stage.nodeAt input.index = some (sharedNode tag input.parent) :=
    by simpa only [stage,BorrowTree.nodeAt] using
      (GeneralBorrowFreshGraph.new_lookup tree input.index input.parent input.parentNode (sharedNode tag input.parent)
        input.atEnd input.present)
  obtain ⟨node,present,_,_,_,_,unexposed⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read input.index (sharedNode tag input.parent) beforePresent
  have mapEq := GeneralBorrowFreshMetadata.mapping input.stage input.after
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
  have tagged : input.after.indexOfTag tag = some input.index := by
    unfold BorrowTree.indexOfTag
    rw [mapEq]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag input.fresh input.index tree.tagMapping.deassigned
  exact EmptyForestUnmaterializedRelease.release input.after tag input.index node tagged present unexposed input.afterClean protections
end Input
end DuplicatePrefix.EmptyForestSharedAppend
