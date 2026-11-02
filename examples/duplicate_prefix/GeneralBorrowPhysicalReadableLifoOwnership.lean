import duplicate_prefix.GeneralBorrowPhysicalReadableAuthorityLifo
import duplicate_prefix.GeneralBorrowPhysicalReadableLifoGlobal
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableLifoOwnership
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowPhysicalReadableLifo GeneralRangeMapState GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- All actual release outcomes retain the allocation's root array, including
stopped error prefixes. -/
theorem roots (id : AllocId) (state : Snapshot) (count : Nat) :
    (GeneralBorrowForestGeneratedTagHistory.run id state (List.replicate count .release)).state.tree.roots=state.tree.roots := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    cases back : state.frames.back? with
    | none => simp only [List.replicate_succ,GeneralBorrowForestGeneratedTagHistory.run,step,back,Bool.false_eq_true,↓reduceIte]
    | some row =>
      cases row with
      | mk tag frame =>
        have same := congrArg BorrowTree.roots (GeneralBorrowStructuralReleaseGeometryFrame.release state.tree state.global.protectedTags tag)
        by_cases completed : (state.tree.releaseProtector tag state.global.protectedTags).status==.Released
        · simpa only [List.replicate_succ,GeneralBorrowForestGeneratedTagHistory.run,step,back,completed,↓reduceIte] using
            (ih (⟨(state.tree.releaseProtector tag state.global.protectedTags).tree,state.global.endCall frame,state.frames.pop⟩:Snapshot)).trans same
        · simpa only [List.replicate_succ,GeneralBorrowForestGeneratedTagHistory.run,step,back,completed,Bool.false_eq_true,↓reduceIte] using same

/-- Real implicit release of every stored frame, followed by its actual
endCall, restores current root Write ownership. Held reservations need no
current Write ownership before the release. The only permission inputs are
readability and latent local-writable/other-possible scalar policy. -/
theorem restore (id : AllocId) (state : Snapshot) (root : UniIndex)
    (structural : GeneralBorrowStructuralHistoryState.State state.tree) (single : state.tree.roots=#[root])
    (readable : Every (fun location=>GeneralBorrowPhysicalReadable.Profile state.tree location state.global.protectedTags) state.tree.locations)
    (authority : GeneralBorrowStructuralHistoryRootAuthorityAt.Profile state.tree root)
    (metadata : Frames id state.tree state.global state.frames)
    (covered : GeneralBorrowForestGeneratedRootEndFrames.Covered state) (lower upper : UInt64) :
    let actual:=GeneralBorrowForestGeneratedTagHistory.run id state (List.replicate state.frames.size .release)
    actual.completed=true ∧ actual.state.frames=#[] ∧ Released id state state.frames.size ∧
      OwnedOn (GeneralBorrowRange.LocationOwned actual.state.tree actual.state.global.protectedTags root .Write) lower upper actual.state.tree.locations := by
  have finished:=GeneralBorrowPhysicalReadableAuthorityLifo.run id state.frames state.tree state.global root structural single readable authority metadata
  have trace : Released id state state.frames.size := finished.2.2.2.2.2
  have unheld:=GeneralBorrowPhysicalReadableLifoGlobal.unheld id state trace covered
  let actual:=GeneralBorrowForestGeneratedTagHistory.run id state (List.replicate state.frames.size .release)
  have member : root∈actual.state.tree.roots.toList := by
    rw [roots id state state.frames.size,single]
    simp
  have formed : GeneralBorrowStructuralHistoryRootAuthorityState.Formed actual.state.tree root :=
    ⟨finished.2.2.1,member,finished.2.2.2.2.1⟩
  refine ⟨finished.1,finished.2.1,trace,?_⟩
  apply GeneralBorrowStructuralHistoryRootAuthorityState.owned actual.state.tree root formed actual.state.global.protectedTags _ lower upper
  intro row member
  exact unheld row.2.tag
end DuplicatePrefix.GeneralBorrowPhysicalReadableLifoOwnership
