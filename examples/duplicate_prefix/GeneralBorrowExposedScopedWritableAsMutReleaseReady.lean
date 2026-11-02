import duplicate_prefix.GeneralBorrowExposedScopedWritableAsMutReleasePlan
import duplicate_prefix.GeneralBorrowExposedScopedWritableReadEndCall
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableAsMutReleaseReady
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Real reserved-child release and the actual endCall table retain both next
partial-Read and next Write inputs for the returned raw pointer tag. -/
theorem ready (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (tag : BorTag)
    (input : GeneralBorrowExposedScopedWritableAsMutReleasePlan.Input tree global.protectedTags tag)
    (hidden : ∀ row∈frame.protectedTags.toList,∀ index node,tree.nodeAt index=some node → node.tag=row.2 → node.isExposed=false) :
    let result := tree.releaseProtector tag global.protectedTags
    result.status=.Released ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context result.tree input.anchor input.selected input.head input.tail,
        GeneralRangeMapOrigins.OwnedOn
          (fun location => Nonempty (GeneralBorrowExposedScopedWritableReadData.Data result.tree location (global.endCall frame).protectedTags
            input.anchor input.selected input.head input.tail input.support (fun _=>true)) ∧
            Nonempty (GeneralBorrowExposedKnownRootRangeData.Data result.tree location (global.endCall frame).protectedTags
              input.anchor input.selected input.head input.tail .Write)) input.lower input.upper result.tree.locations ∧
        result.tree.locations.WellFormed ∧ result.tree.locations.size=tree.locations.size := by
  have released := GeneralBorrowExposedScopedWritableReadRelease.release tree global.protectedTags tag input.anchor input.selected input.head input.tail
    input.context input.support (fun _=>true) input.lower input.upper input.positive input.fits input.hidden input.tagPresent
    (GeneralBorrowFreshActiveWithin.active_on tree input.anchor .Read input.lower input.upper input.well input.within) input.owned
  let result := tree.releaseProtector tag global.protectedTags
  have geometry := GeneralBorrowStructuralReleaseGeometry.release tree global.protectedTags tag input.well
  have context : GeneralBorrowExposedKnownRootRangeData.Context result.tree input.anchor input.selected input.head input.tail := by
    rw [released.2.1]
    exact ⟨input.context.anchorNode,input.context.selectedNode,input.context.anchorPresent,input.context.selectedPresent,
      input.context.roots,input.context.depth,input.context.children,input.context.tags⟩
  have hiddenAfter : ∀ row∈frame.protectedTags.toList,∀ index node,result.tree.nodeAt index=some node → node.tag=row.2 → node.isExposed=false := by
    intro row member index node present equal
    rw [released.2.1] at present
    exact hidden row member index node present equal
  refine ⟨released.1,context,?_,geometry⟩
  intro position valid positive lower upper
  obtain ⟨data⟩ := released.2.2 position valid positive lower upper
  let after := GeneralBorrowExposedScopedWritableReadEndCall.end_call result.tree _ global frame hiddenAfter
    input.anchor input.selected input.head input.tail input.support (fun _=>true) context data
  exact ⟨⟨after⟩,⟨GeneralBorrowExposedScopedWritableReadData.write result.tree _ (global.endCall frame).protectedTags
    input.anchor input.selected input.head input.tail input.support context after⟩⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWritableAsMutReleaseReady
