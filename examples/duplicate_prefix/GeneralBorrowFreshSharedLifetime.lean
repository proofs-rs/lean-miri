import duplicate_prefix.GeneralBorrowFreshStackPop
import duplicate_prefix.GeneralBorrowFreshSharedPaths
import duplicate_prefix.GeneralBorrowFreshActiveWithin
namespace DuplicatePrefix.GeneralBorrowFreshSharedLifetime
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Derive actual shared helper pop and recover the old mutable anchor from
mixed ownership and two leaf-insertion topology certificates. Both read-only
shared nodes are removed from the target local path by actual endCall data.
Neither a release result, a pop result nor a RestoreTo premise is assumed. -/
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
    (before middle : BorrowTree) (anchor target expr root : UniIndex) (lower upper : UInt64)
    (positive : lower.toNat < upper.toNat) (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296)
    (depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (children : GeneralBorrowGraph.ChildNodes entry.allocation.extra)
    (anchorNode : TreeNode) (anchorPresent : entry.allocation.extra.nodeAt anchor = some anchorNode)
    (notExposed : anchorNode.isExposed = false) (roots : entry.allocation.extra.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (tagPresent : entry.allocation.extra.indexOfTag tag = some anchor)
    (well : entry.allocation.extra.locations.WellFormed)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra anchor .Read lower upper)
    (targetNode exprNode : TreeNode)
    (targetPresent : entry.allocation.extra.nodeAt target = some targetNode)
    (exprPresent : entry.allocation.extra.nodeAt expr = some exprNode)
    (childTag : anchorNode.tag = tag)
    (exprUnheld : tracker.global.protectedTags.contains exprNode.tag = false)
    (first : ∀ location : LocationTree, GeneralBorrowFreshSharedPaths.Attach
      (source_normal_projection before location tracker.global.protectedTags).topology
      (source_normal_projection middle location tracker.global.protectedTags).topology target.toNat expr.toNat)
    (second : ∀ location : LocationTree, GeneralBorrowFreshSharedPaths.Attach
      (source_normal_projection middle location tracker.global.protectedTags).topology
      (source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology expr.toNat anchor.toNat)
    (owned : OwnedOn (GeneralBorrowFreshReleaseMixed.Combined entry.allocation.extra tracker.global.protectedTags anchor (GeneralBorrowFreshSharedPrefix.labels expr anchor))
      lower upper entry.allocation.extra.locations) :
    ∃ tree, MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with
        memory := StackPopRelease.commitTree state.machine.memory id entry tree,
        borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
      OwnedOn (GeneralBorrowRange.LocationOwned tree (tracker.global.endCall borrowFrame).protectedTags target .Write)
        lower upper tree.locations ∧ (tracker.global.endCall borrowFrame).protectedTags.contains tag = false := by
  have paths := fun location => GeneralBorrowFreshSharedPaths.two_step _ _ _ target.toNat expr.toNat anchor.toNat
    (first location) (second location)
  have registered : (id,anchorNode.tag) ∈ borrowFrame.protectedTags.toList := by
    rw [frameOwned,childTag]
    simp
  have restore := GeneralBorrowFreshSharedPrefix.restore_data entry.allocation.extra tracker.global borrowFrame
    target expr anchor targetNode exprNode anchorNode targetPresent exprPresent anchorPresent id registered exprUnheld
    (fun location => (paths location).1) (fun location => (paths location).2.1) (fun location => (paths location).2.2)
  exact GeneralBorrowFreshStackPop.shared_restoring globalKind globals sync state tracker frame borrowFrame enabled
    current framed id tag entry frameOwned present anchor target root (GeneralBorrowFreshSharedPrefix.labels expr anchor)
    lower upper positive fits depth children anchorNode anchorPresent notExposed roots covered tagPresent
    (GeneralBorrowFreshActiveWithin.active_on entry.allocation.extra anchor .Read lower upper well active) restore owned
end DuplicatePrefix.GeneralBorrowFreshSharedLifetime
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedLifetime." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared lifetime dependency {dependency}"
