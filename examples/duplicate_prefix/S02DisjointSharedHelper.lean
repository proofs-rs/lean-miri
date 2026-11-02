import duplicate_prefix.S02DisjointReleasePositive
import duplicate_prefix.S02DisjointSharedFnEntry
import duplicate_prefix.GeneralBorrowSharedLenHelperGraph
namespace DuplicatePrefix.S02DisjointSharedHelper
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Protected shared helper construction, real release, and singleton endCall retain a disjoint full capability. -/
theorem destination (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawSharedFnEntry.Input tree tracker.global)
    (stepRoom : tree.nodes.size+1 < 65536)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (positive : Positive tree tracker.global.protectedTags source selected maximum lower width) :
    Nonempty (Positive (GeneralBorrowSharedLenHelperGraph.releasedTree tree tracker input)
      tracker.global.protectedTags source selected maximum lower width) := by
  let borrowed := GeneralBorrowRawSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  let held := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  obtain ⟨borrowedRuntime,capacity,growth,roots,heldTag,fresh,child,lookup,⟨parentPositive⟩,⟨childPositive⟩,active⟩ :=
    GeneralBorrowRawSharedFnEntryResources.resources tree tracker {} allocation runtime input
  obtain ⟨graphChild,graphLookup,⟨node,present,sameTag,parent,hidden⟩,oldNodes⟩ :=
    GeneralBorrowRawSharedFnEntryGraph.graph tree tracker {} allocation runtime input
  have childEq : graphChild = child := Option.some.inj (graphLookup.symm.trans lookup)
  subst graphChild
  obtain ⟨destinationBefore⟩ := S02DisjointSharedFnEntry.final_tree tree tracker {} allocation runtime input source selected maximum lower width outside positive
  have outsideRelease : (input.offset+input.len).toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat := by
    rcases outside with left | right
    · left
      exact Nat.le_trans (by rw [UInt64.toNat_add];exact Nat.mod_le _ _) left
    · exact Or.inr right
  obtain ⟨destinationReleased⟩ := S02DisjointReleasePositive.release borrowed held borrowedRuntime tracker.global.nextPointerTag
    child input.selected input.maximum input.offset input.len childPositive node present hidden lookup
    (by rw [roots];exact input.distinct)
    (GeneralBorrowRawSharedFnEntryOrder.order tree tracker {} allocation runtime input)
    (Nat.lt_of_le_of_lt growth stepRoom) active source selected maximum lower width outsideRelease destinationBefore
  obtain ⟨done,releasedRuntime,_,_,frame,_⟩ := GeneralBorrowReadProtectorRelease.release borrowed held borrowedRuntime
    tracker.global.nextPointerTag child input.selected input.maximum input.offset input.len childPositive node present hidden lookup
    (by rw [roots];exact input.distinct)
    (GeneralBorrowRawSharedFnEntryOrder.order tree tracker {} allocation runtime input)
    (Nat.lt_of_le_of_lt growth stepRoom) active
  have presentReleased : (borrowed.releaseProtector tracker.global.nextPointerTag held.protectedTags).tree.nodeAt child = some node := by
    rw [frame];exact present
  obtain ⟨destinationEnded⟩ := S02DisjointReleasePositive.end_call _ held releasedRuntime allocation tracker.global.nextPointerTag child node
    presentReleased sameTag hidden source selected maximum lower width destinationReleased
  have exactGlobal := GeneralBorrowSharedFnEntryGlobalReturn.queries tree tracker.global runtime {} allocation input.tagRoom
  have table : (held.endCall (({} : FrameState).addProtector allocation tracker.global.nextPointerTag)).protectedTags = tracker.global.protectedTags := exactGlobal.1
  rw [table] at destinationEnded
  rw [GeneralBorrowSharedLenHelperGraph.releasedTree_eq]
  exact ⟨destinationEnded⟩
end DuplicatePrefix.S02DisjointSharedHelper
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointSharedHelper.destination) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
