import duplicate_prefix.StackPopRelease
import duplicate_prefix.GeneralBorrowFreshReleaseLoop
import duplicate_prefix.GeneralBorrowFreshLifetimeRestore
namespace DuplicatePrefix.GeneralBorrowFreshStackPop
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem release_complete (result : BorrowTree.ProtectorReleaseResult) (done : result.status = .Released) :
    result = ⟨result.tree,.Released⟩ := by
  cases result with | mk tree status => cases done;rfl

/-- A real single-protector frame pop derives its tree release, allocation
commit and global endCall bookkeeping from explicit location/graph data. No
successful release, stack-pop outcome or release-plan premise is supplied. -/
theorem single_live {K U : Type} [DecidableEq K]
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
    (anchor root : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (positive : lower.toNat < upper.toNat) (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296)
    (depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (children : GeneralBorrowGraph.ChildNodes entry.allocation.extra)
    (anchorNode : TreeNode) (anchorPresent : entry.allocation.extra.nodeAt anchor = some anchorNode)
    (notExposed : anchorNode.isExposed = false) (roots : entry.allocation.extra.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (tagPresent : entry.allocation.extra.indexOfTag tag = some anchor)
    (active : GeneralBorrowFreshReleaseLoop.ActiveOn entry.allocation.extra anchor ownerKind lower upper)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags anchor ownerKind)
      lower upper entry.allocation.extra.locations) :
    ∃ tree, MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with
        memory := StackPopRelease.commitTree state.machine.memory id entry tree,
        borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
      OwnedOn (GeneralBorrowRange.LocationOwned tree (tracker.global.endCall borrowFrame).protectedTags anchor ownerKind)
        lower upper tree.locations ∧ (tracker.global.endCall borrowFrame).protectedTags.contains tag = false := by
  let released := entry.allocation.extra.releaseProtector tag tracker.global.protectedTags
  have ready := GeneralBorrowFreshReleaseLoop.release entry.allocation.extra tracker.global.protectedTags tag anchor root
    ownerKind lower upper positive fits depth children anchorNode anchorPresent notExposed roots covered tagPresent active owned
  change released.status = .Released ∧
    OwnedOn (GeneralBorrowRange.LocationOwned released.tree tracker.global.protectedTags anchor ownerKind)
      lower upper released.tree.locations at ready
  refine ⟨released.tree,StackPopRelease.single_live globalKind globals sync state tracker frame borrowFrame enabled
    current framed id tag entry released.tree frameOwned present (release_complete released ready.1),?_,?_⟩
  · exact GeneralBorrowFreshProtectorRelease.end_call_owned_on released.tree tracker.global borrowFrame
      anchor ownerKind lower upper ready.2
  · apply GeneralBorrowRelease.end_call_owned_absent tracker.global borrowFrame id tag
    rw [frameOwned]
    simp
/-- End a real shared lifetime and recover an older mutable anchor, while
retaining arbitrary caller history and multiple read-only Frozen ancestors.
All release and stack-pop successes are derived from mixed ownership, active
range coherence and explicit metadata for the post-endCall local-path change. -/
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
    (anchor target root : UniIndex) (writable : Nat → Bool) (lower upper : UInt64)
    (positive : lower.toNat < upper.toNat) (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296)
    (depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (children : GeneralBorrowGraph.ChildNodes entry.allocation.extra)
    (anchorNode : TreeNode) (anchorPresent : entry.allocation.extra.nodeAt anchor = some anchorNode)
    (notExposed : anchorNode.isExposed = false) (roots : entry.allocation.extra.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (tagPresent : entry.allocation.extra.indexOfTag tag = some anchor)
    (active : GeneralBorrowFreshReleaseLoop.ActiveOn entry.allocation.extra anchor .Read lower upper)
    (restore : GeneralBorrowFreshLifetimeRestore.RestoreTo entry.allocation.extra tracker.global.protectedTags
      (tracker.global.endCall borrowFrame).protectedTags anchor target writable)
    (owned : OwnedOn (GeneralBorrowFreshReleaseMixed.Combined entry.allocation.extra tracker.global.protectedTags anchor writable)
      lower upper entry.allocation.extra.locations) :
    ∃ tree, MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with
        memory := StackPopRelease.commitTree state.machine.memory id entry tree,
        borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
      OwnedOn (GeneralBorrowRange.LocationOwned tree (tracker.global.endCall borrowFrame).protectedTags target .Write)
        lower upper tree.locations ∧ (tracker.global.endCall borrowFrame).protectedTags.contains tag = false := by
  let released := entry.allocation.extra.releaseProtector tag tracker.global.protectedTags
  have ready := GeneralBorrowFreshReleaseMixed.release_shared_mixed entry.allocation.extra tracker.global.protectedTags tag anchor root
    writable lower upper positive fits depth children anchorNode anchorPresent notExposed roots covered tagPresent active owned
  change released.status = .Released ∧ released.tree = {entry.allocation.extra with locations := released.tree.locations} ∧
    OwnedOn (GeneralBorrowFreshReleaseMixed.Combined released.tree tracker.global.protectedTags anchor writable)
      lower upper released.tree.locations at ready
  have restoreReleased : GeneralBorrowFreshLifetimeRestore.RestoreTo released.tree tracker.global.protectedTags
      (tracker.global.endCall borrowFrame).protectedTags anchor target writable := by
    rw [ready.2.1]
    exact GeneralBorrowFreshLifetimeRestore.restore_map entry.allocation.extra released.tree.locations _ _ anchor target writable restore
  refine ⟨released.tree,StackPopRelease.single_live globalKind globals sync state tracker frame borrowFrame enabled
    current framed id tag entry released.tree frameOwned present (release_complete released ready.1),?_,?_⟩
  · exact GeneralBorrowFreshLifetimeRestore.restore_owned_on released.tree tracker.global.protectedTags
      (tracker.global.endCall borrowFrame).protectedTags (GeneralBorrowRelease.end_call_weakens tracker.global borrowFrame)
      anchor target writable restoreReleased lower upper ready.2.2
  · apply GeneralBorrowRelease.end_call_owned_absent tracker.global borrowFrame id tag
    rw [frameOwned]
    simp
end DuplicatePrefix.GeneralBorrowFreshStackPop
#print axioms DuplicatePrefix.GeneralBorrowFreshStackPop.single_live

#print axioms DuplicatePrefix.GeneralBorrowFreshStackPop.shared_restoring
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshStackPop." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual frame lifetime completion dependency {dependency}"
