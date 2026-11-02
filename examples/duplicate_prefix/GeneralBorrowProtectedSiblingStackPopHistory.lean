import duplicate_prefix.GeneralBorrowProtectedStackPopHistory
import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseHistory
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingStackPopHistory
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
open DuplicatePrefix.GeneralBorrowProtectedReleaseHistory (Tags execute)
open DuplicatePrefix.GeneralBorrowProtectedStackPopHistory (memoryAfter)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Every actual source-order commit is represented in memoryAfter; the final
live entry stores exactly the actual release history tree. -/
theorem final_entry {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (protections : ProtectedTags) (tags : List BorTag)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    (memoryAfter memory id entry protections tags).live.find? (fun row => row.1 == id) =
      some (id,{entry with allocation := entry.allocation.setExtra (execute entry.allocation.extra protections tags)}) := by
  induction tags generalizing memory entry with
  | nil => exact present
  | cons tag rest ih =>
    let result := entry.allocation.extra.releaseProtector tag protections
    let nextEntry := {entry with allocation := entry.allocation.setExtra result.tree}
    have lookup := StackPopRelease.lookup_commit_same memory id entry result.tree
    exact ih (StackPopRelease.commitTree memory id entry result.tree) nextEntry lookup

/-- Actual one-allocation stack pop, arbitrary duplicate-free frame length:
release statuses, commits, final endCall and the final allocation cache invariant
all follow from initial data. Only tags released before the final tag need
Read-stable exposed permissions; the final reservation may be unconflicted. -/
theorem before_stack_pop {K U : Type} [DecidableEq K]
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker) (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tags : List BorTag) (root : UniIndex)
    (rows : borrowFrame.protectedTags.toList = tags.map (fun tag => (id,tag))) (distinct : tags.Nodup)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296) (depth : ParentDepth entry.allocation.extra.nodes)
    (children : GeneralBorrowGraph.ChildNodes entry.allocation.extra) (roots : entry.allocation.extra.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (nodeTags : ∀ index node,entry.allocation.extra.nodeAt index = some node → entry.allocation.extra.indexOfTag node.tag = some index)
    (mapped : Tags entry.allocation.extra tracker.global.protectedTags tags)
    (initial : Every (Profile entry.allocation.extra tracker.global.protectedTags) entry.allocation.extra.locations)
    (coherent : Every (fun location => LocationCoherent entry.allocation.extra location tracker.global.protectedTags) entry.allocation.extra.locations)
    (stable : Every (GeneralBorrowProtectedSiblingReleaseStable.ForTags tags.dropLast entry.allocation.extra) entry.allocation.extra.locations) :
    let memory := memoryAfter state.machine.memory id entry tracker.global.protectedTags tags
    let finalTree := execute entry.allocation.extra tracker.global.protectedTags tags
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with
        memory := memory,
        borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
    memory.live.find? (fun row => row.1 == id) = some (id,{entry with allocation := entry.allocation.setExtra finalTree}) ∧
    Every (fun location => LocationCoherent finalTree location (tracker.global.endCall borrowFrame).protectedTags) finalTree.locations := by
  have cached := GeneralBorrowProtectedSiblingReleaseHistory.complete entry.allocation.extra tracker.global.protectedTags tags root
    distinct fits depth children roots covered nodeTags mapped initial coherent stable
  have cleanup := GeneralBorrowProtectedReleaseCacheHistory.pending_end_call tracker.global borrowFrame id tags rows
  refine ⟨GeneralBorrowProtectedStackPopHistory.before_stack_pop globalKind globals sync state tracker frame borrowFrame enabled current framed
    id entry tags root rows present fits depth children roots covered mapped initial,final_entry _ id entry _ tags present,?_⟩
  rw [cleanup]
  exact cached.2
end DuplicatePrefix.GeneralBorrowProtectedSiblingStackPopHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingStackPopHistory.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected stack-pop cache history dependency {dependency}"
