import duplicate_prefix.CurrentCallEmptyEntryCompleteRelease
import duplicate_prefix.CurrentCallRootRelease
namespace DuplicatePrefix.CurrentCallEmptyEntryPostLenCompleteRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFreshActiveWithin
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure Result (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (completion : Completion)
    (child parent : UniIndex) (node originalNode : TreeNode) (provenance : Provenance) (offset : UInt64) : Prop where
  completed : (tree.releaseProtector node.tag global.protectedTags).status=.Released
  shape : (tree.releaseProtector node.tag global.protectedTags).tree={tree with locations:=(tree.releaseProtector node.tag global.protectedTags).tree.locations}
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts (tree.releaseProtector node.tag global.protectedTags).tree global
  complete : Completes (tree.releaseProtector node.tag global.protectedTags).tree completion
  order : ParentTagOrder (tree.releaseProtector node.tag global.protectedTags).tree
  capacity : (tree.releaseProtector node.tag global.protectedTags).tree.locations.size=tree.locations.size
  childPresent : (tree.releaseProtector node.tag global.protectedTags).tree.nodeAt child=some node
  owned : OwnedOn (Authority (tree.releaseProtector node.tag global.protectedTags).tree completion global.protectedTags child)
    offset (offset+1) (tree.releaseProtector node.tag global.protectedTags).tree.locations
  originalPresent : (tree.releaseProtector node.tag global.protectedTags).tree.nodeAt parent=some originalNode
  originalOwned : OwnedOn (Authority (tree.releaseProtector node.tag global.protectedTags).tree completion (global.endCall frame).protectedTags parent)
    offset (offset+1) (tree.releaseProtector node.tag global.protectedTags).tree.locations
  originalNormal : OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal
    (tree.releaseProtector node.tag global.protectedTags).tree row (global.endCall frame).protectedTags parent))
    offset (offset+1) (tree.releaseProtector node.tag global.protectedTags).tree.locations
  afterRuntime : S04ReturnReleaseParent.HiddenFrame (tree.releaseProtector node.tag global.protectedTags).tree frame →
    DuplicatePrefixBorrowContract.RuntimeFacts (tree.releaseProtector node.tag global.protectedTags).tree (global.endCall frame)
  originalWrite : S04ReturnReleaseParent.HiddenFrame (tree.releaseProtector node.tag global.protectedTags).tree frame →
    ((tree.releaseProtector node.tag global.protectedTags).tree.performBorrowAccessRange (S04ReturnBorrowBridge.extra provenance)
      (Size.ofBytes offset) (Size.ofBytes 1) .Write (global.endCall frame).protectedTags .VisitChildrenOfAccessed).status=.Completed

/-- Release the actual current Bool child, then reanchor its authority after the whole root frame ends. -/
theorem release (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion) (order : ParentTagOrder tree)
    (child parent : UniIndex) (node originalNode : TreeNode) (present : tree.nodeAt child=some node)
    (hidden : node.isExposed=false) (member : (allocation,node.tag)∈frame.protectedTags.toList)
    (originalPresent : tree.nodeAt parent=some originalNode) (provenance : Provenance)
    (binds : match provenance with | .concrete _ tag => tag=originalNode.tag | .wildcard => originalNode.isExposed=true)
    (edge : completion.parents[child.toNat]?=some (some parent))
    (offset : UInt64) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat) (short : tree.nodes.size<65536)
    (active : ActiveWithin tree child .Write offset (offset+1))
    (owned : OwnedOn (Authority tree completion global.protectedTags child) offset (offset+1) tree.locations) :
    Result tree global frame completion child parent node originalNode provenance offset := by
  have positive : offset.toNat<(offset+1).toNat := by
    have fits : offset.toNat+1<2^64 := Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits];omega
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState child node present
  obtain ⟨done,shape,afterRuntime,afterComplete,capacity,afterOwned⟩ :=
    S05CurrentMutableProtectorRelease.release_owned tree global completion runtime complete order position root child rootNode node slot rootAt path present hidden offset 1 positive active owned short
  let after := (tree.releaseProtector node.tag global.protectedTags).tree
  have nodes : after.nodes=tree.nodes := by
    have framed := congrArg BorrowTree.nodes shape
    exact framed
  have childAt : after.nodeAt child=some node := by change after.nodes.get child=_;rw [nodes];exact present
  have originalAt : after.nodeAt parent=some originalNode := by change after.nodes.get parent=_;rw [nodes];exact originalPresent
  have afterOrder := GeneralBorrowParentTagInvariant.nodes_frame tree after nodes order
  have afterShort : after.nodes.size<65536 := by rw [nodes];exact short
  have parentOwned := S05CompletedChildReanchor.owned_end_call after completion global frame allocation child parent node offset (offset+1) edge childAt member afterOwned
  obtain ⟨originalPosition,originalRoot,originalRootNode,originalSlot,originalRootAt,originalPath⟩ :=
    CandidateCurrentWindowAuthority.root_path after afterRuntime.formed.toGraphState parent originalNode originalAt
  obtain ⟨depth⟩ := afterRuntime.formed.depth
  have normal : OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal after row (global.endCall frame).protectedTags parent)) offset (offset+1) after.locations := by
    intro cursor valid isPositive start stop
    have authority := parentOwned cursor valid isPositive start stop
    apply S05CompletedAncestryNormal.normal after completion _ _ afterComplete afterRuntime.formed.toGraphState depth
      (by change after.nodes.size≤4294967296;omega) originalPosition originalRoot parent originalRootNode originalSlot originalRootAt originalPath
    · intro index current atNode path below
      exact (authority index current atNode).1 below
    · intro index current atNode path outside
      exact (authority index current atNode).2 outside
  have endRuntime := fun hiddenFrame => S05CompletedChildReanchor.runtime_end_call after global frame afterRuntime hiddenFrame
  exact ⟨done,shape,afterRuntime,afterComplete,afterOrder,capacity,childAt,afterOwned,originalAt,parentOwned,normal,endRuntime,
    fun hiddenFrame => CurrentCallRootRelease.write_original after (global.endCall frame) completion (endRuntime hiddenFrame)
      afterComplete afterOrder parent originalNode originalAt provenance binds offset (by rw [capacity];exact bounds) parentOwned afterShort⟩

end
end DuplicatePrefix.CurrentCallEmptyEntryPostLenCompleteRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryPostLenCompleteRelease" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved post-Len release dependency {dependency}"
