import duplicate_prefix.GeneralBorrowForestMixedReleaseFrame
import duplicate_prefix.GeneralBorrowForestMixedRestore
import duplicate_prefix.StackPopRelease
namespace DuplicatePrefix.GeneralBorrowForestMixedStackPop
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
private theorem release_complete (result : BorrowTree.ProtectorReleaseResult) (done : result.status = .Released) :
    result = ⟨result.tree,.Released⟩ := by
  cases result with | mk tree status => cases done;rfl

/-- Real multiple-root implicit release, allocation commit, and global endCall
recover FULL old mutable slice records from mixed labels and path metadata.
No release, stack-pop or restored-ownership result is assumed. -/
theorem shared_restoring {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker)
    (current : state.stack.currentFrame? = some frame) (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree K)
    (frameOwned : borrowFrame.protectedTags = #[(id,tag)])
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (anchor target primary : UniIndex) (extras : List UniIndex) (writable : Nat → Bool) (lower upper : UInt64)
    (positive : lower.toNat < upper.toNat) (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296)
    (context : GeneralBorrowForestAccessData.Context entry.allocation.extra anchor primary extras)
    (rootPath : ∀ location : LocationTree,
      ((source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat)
    (tagPresent : entry.allocation.extra.indexOfTag tag = some anchor)
    (active : GeneralBorrowFreshReleaseLoop.ActiveOn entry.allocation.extra anchor .Read lower upper)
    (restore : GeneralBorrowFreshLifetimeRestore.RestoreTo entry.allocation.extra tracker.global.protectedTags
      (tracker.global.endCall borrowFrame).protectedTags anchor target writable)
    (owned : OwnedOn (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data entry.allocation.extra location tracker.global.protectedTags anchor primary extras writable))
      lower upper entry.allocation.extra.locations) :
    ∃ tree, MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with
        memory := StackPopRelease.commitTree state.machine.memory id entry tree,
        borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
      OwnedOn (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location (tracker.global.endCall borrowFrame).protectedTags target primary extras))
        lower upper tree.locations ∧ (tracker.global.endCall borrowFrame).protectedTags.contains tag = false := by
  let released := entry.allocation.extra.releaseProtector tag tracker.global.protectedTags
  have ready := GeneralBorrowForestMixedReleaseFrame.release entry.allocation.extra tracker.global.protectedTags tag anchor primary extras
    writable lower upper positive fits context tagPresent active owned
  change released.status = .Released ∧ released.tree = {entry.allocation.extra with locations := released.tree.locations} ∧
    OwnedOn (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data released.tree location tracker.global.protectedTags anchor primary extras writable))
      lower upper released.tree.locations at ready
  have restoreReleased : GeneralBorrowFreshLifetimeRestore.RestoreTo released.tree tracker.global.protectedTags
      (tracker.global.endCall borrowFrame).protectedTags anchor target writable := by
    rw [ready.2.1]
    exact GeneralBorrowFreshLifetimeRestore.restore_map entry.allocation.extra released.tree.locations _ _ anchor target writable restore
  have releasedPath : ∀ location : LocationTree,
      ((source_normal_projection released.tree location tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat := by
    intro location
    rw [ready.2.1]
    exact rootPath location
  refine ⟨released.tree,StackPopRelease.single_live globalKind globals sync state tracker frame borrowFrame enabled
    current framed id tag entry released.tree frameOwned present (release_complete released ready.1),?_,?_⟩
  · intro position valid positive lowerBound upperBound
    obtain ⟨data⟩ := ready.2.2 position valid positive lowerBound upperBound
    refine ⟨GeneralBorrowForestMixedRestore.restore released.tree _ tracker.global.protectedTags
      (tracker.global.endCall borrowFrame).protectedTags (GeneralBorrowRelease.end_call_weakens tracker.global borrowFrame)
      anchor target primary extras writable restoreReleased ?_ data⟩
    exact releasedPath _
  · apply GeneralBorrowRelease.end_call_owned_absent tracker.global borrowFrame id tag
    rw [frameOwned]
    simp
end DuplicatePrefix.GeneralBorrowForestMixedStackPop
