import duplicate_prefix.CurrentCallEmptyEntryPostLenCompleteRelease
import duplicate_prefix.CurrentCallEmptyEntryOrphanOriginalWrite
import duplicate_prefix.CurrentCallEmptyEntryFactoryLocations
namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroBorrowRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFreshActiveWithin CurrentCallEmptyEntryBool
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

structure Result (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (tag : BorTag) (provenance : Provenance) (offset : UInt64) : Prop where
  completed : (tree.releaseProtector tag global.protectedTags).status=.Released
  shape : (tree.releaseProtector tag global.protectedTags).tree={tree with locations:=(tree.releaseProtector tag global.protectedTags).tree.locations}
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts (tree.releaseProtector tag global.protectedTags).tree global
  order : ParentTagOrder (tree.releaseProtector tag global.protectedTags).tree
  capacity : (tree.releaseProtector tag global.protectedTags).tree.locations.size=tree.locations.size
  afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (tree.releaseProtector tag global.protectedTags).tree (global.endCall frame)
  originalWrite : ((tree.releaseProtector tag global.protectedTags).tree.performBorrowAccessRange (S04ReturnBorrowBridge.extra provenance)
    (Size.ofBytes offset) (Size.ofBytes 1) .Write (global.endCall frame).protectedTags .VisitChildrenOfAccessed).status=.Completed

private theorem hidden_after (tree : BorrowTree) (global : GlobalState) (tag : BorTag) (frame : FrameState)
    (hidden : S04ReturnReleaseParent.HiddenFrame tree frame)
    (shape : (tree.releaseProtector tag global.protectedTags).tree={tree with locations:=(tree.releaseProtector tag global.protectedTags).tree.locations}) :
    S04ReturnReleaseParent.HiddenFrame (tree.releaseProtector tag global.protectedTags).tree frame := by
  intro row member index node present same
  have old : tree.nodeAt index=some node := by
    change (tree.releaseProtector tag global.protectedTags).tree.nodes.get index=some node at present
    rw [congrArg BorrowTree.nodes shape] at present
    exact present
  exact hidden row member index node old same

private theorem complete_release (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (tag qTag : BorTag) (provenance : Provenance) (offset : UInt64)
    (h : BoolHoldings tree global tag qTag provenance offset)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree h.completion)
    (order : ParentTagOrder tree) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat) (short : tree.nodes.size<65536)
    (member : (allocation,tag)∈frame.protectedTags.toList) (hidden : S04ReturnReleaseParent.HiddenFrame tree frame) :
    Result tree global frame tag provenance offset := by
  have owned : OwnedOn (Authority tree h.completion global.protectedTags h.child) offset (offset+1) tree.locations := by
    intro position valid positive start stop
    exact (h.owned position valid positive start stop).2
  have leaf := CurrentCallEmptyEntryPostLenCompleteRelease.release tree global frame allocation h.completion runtime complete order
    h.child h.parent h.node h.parentNode h.present h.hidden (by simpa only [h.nodeTag] using member) h.parentAt provenance
    h.parentProvenance h.edge offset bounds short h.active owned
  have shape : (tree.releaseProtector tag global.protectedTags).tree={tree with locations:=(tree.releaseProtector tag global.protectedTags).tree.locations} := by
    simpa only [h.nodeTag] using leaf.shape
  have afterHidden := hidden_after tree global tag frame hidden shape
  refine ⟨?_,shape,?_,?_,?_,?_,?_⟩
  · simpa only [h.nodeTag] using leaf.completed
  · simpa only [h.nodeTag] using leaf.runtime
  · simpa only [h.nodeTag] using leaf.order
  · simpa only [h.nodeTag] using leaf.capacity
  · simpa only [h.nodeTag] using leaf.afterRuntime (by simpa only [h.nodeTag] using afterHidden)
  · simpa only [h.nodeTag] using leaf.originalWrite (by simpa only [h.nodeTag] using afterHidden)

private theorem orphan_release (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (tag qTag : BorTag) (originalAllocation : AllocId) (originalTag : BorTag) (offset : UInt64)
    (h : BoolHoldings tree global tag qTag (.concrete originalAllocation originalTag) offset)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat) (short : tree.nodes.size<65536)
    (member : (allocation,tag)∈frame.protectedTags.toList) (hidden : S04ReturnReleaseParent.HiddenFrame tree frame)
    (factory : OrphanWriteFactory tree h.completion global.protectedTags h.child qTag)
    (physical : h.node.parent=some h.parent) : Result tree global frame tag (.concrete originalAllocation originalTag) offset := by
  obtain ⟨done,shape,afterRuntime,capacity,afterOwned⟩ := CurrentCallEmptyEntryOrphanRelease.release tree global tag qTag
    (.concrete originalAllocation originalTag) offset h runtime order bounds short factory
  obtain ⟨parentAt,provenance,parentOwned,endRuntime⟩ := CurrentCallEmptyEntryOrphanRelease.restore_parent tree global tag qTag
    (.concrete originalAllocation originalTag) offset h runtime order bounds short factory frame allocation
    (by simpa only [h.nodeTag] using member) physical
  let after := (tree.releaseProtector tag global.protectedTags).tree
  have nodes : after.nodes=tree.nodes := by
    have actual := congrArg BorrowTree.nodes shape
    exact actual
  have afterOrder := GeneralBorrowParentTagInvariant.nodes_frame tree after nodes order
  have afterHidden := hidden_after tree global tag frame hidden shape
  have afterBounds : offset.toNat+1≤after.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have afterShort : after.nodes.size<65536 := by rw [nodes];exact short
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨framed⟩ := CurrentCallEmptyEntryFactoryLocations.transport tree h.completion global.protectedTags h.child qTag depth after.locations factory
  have afterFactory : OrphanWriteFactory after h.completion global.protectedTags h.child qTag := by
    change OrphanWriteFactory (tree.releaseProtector tag global.protectedTags).tree _ _ _ _
    rw [shape]
    exact framed
  have childAt : after.nodeAt h.child=some h.node := by change after.nodes.get h.child=some h.node;rw [nodes];exact h.present
  have childOwned : OwnedOn (Authority after h.completion global.protectedTags h.child) offset (offset+1) after.locations := by
    intro position valid positive start stop
    exact (afterOwned position valid positive start stop).2
  have normal : OwnedOn (fun row=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal after row (global.endCall frame).protectedTags h.parent))
      offset (offset+1) after.locations := by
    intro position valid positive start stop
    exact (parentOwned position valid positive start stop).1
  have original : (after.performBorrowAccessRange (.concrete h.parentNode.tag) (Size.ofBytes offset) (Size.ofBytes 1) .Write
      (global.endCall frame).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
    exact CurrentCallEmptyEntryOrphanOriginalWrite.range_metadata after global frame h.completion h.child h.parent h.node h.parentNode qTag offset
      childAt parentAt physical afterRuntime (endRuntime afterHidden) afterOrder afterHidden afterFactory afterBounds afterShort normal childOwned
  refine ⟨done,shape,afterRuntime,afterOrder,capacity,endRuntime afterHidden,?_⟩
  simpa only [S04ReturnBorrowBridge.extra,h.parentProvenance] using original

/-- Release the actual current Bool child and write through its original
provenance after the WHOLE root frame ends. All geometry alternatives are
retained constructor facts, including wildcard completeness. -/
theorem release (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (tag qTag : BorTag) (provenance : Provenance) (offset : UInt64)
    (h : BoolHoldings tree global tag qTag provenance offset)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat) (short : tree.nodes.size<65536)
    (member : (allocation,tag)∈frame.protectedTags.toList) (hidden : S04ReturnReleaseParent.HiddenFrame tree frame) :
    Result tree global frame tag provenance offset := by
  cases provenance with
  | wildcard =>
    exact complete_release tree global frame allocation tag qTag .wildcard offset h runtime
      (h.wildcardComplete rfl) order bounds short member hidden
  | concrete originalAllocation originalTag =>
    rcases h.physicalOrComplete with physical | complete
    · rcases h.geometry with complete | factory
      · exact complete_release tree global frame allocation tag qTag _ offset h runtime complete order bounds short member hidden
      · obtain ⟨factory⟩ := factory
        exact orphan_release tree global frame allocation tag qTag originalAllocation originalTag offset h runtime order bounds short member hidden factory physical
    · exact complete_release tree global frame allocation tag qTag _ offset h runtime complete order bounds short member hidden

end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroBorrowRelease

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroBorrowRelease" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual nonzero release dependency {dependency}"
