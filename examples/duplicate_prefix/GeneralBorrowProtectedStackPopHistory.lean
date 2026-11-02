import duplicate_prefix.GeneralBorrowProtectedReleaseHistory
import duplicate_prefix.StackPopRelease
namespace DuplicatePrefix.GeneralBorrowProtectedStackPopHistory
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
open DuplicatePrefix.GeneralBorrowProtectedReleaseHistory (Tags AllReleased)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Real source-order tree commits for an arbitrary finite frame-owned list
on one live buffer allocation. Each later lookup uses the previous commit. -/
def memoryAfter {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (protections : ProtectedTags) : List BorTag → MemoryState Provenance BorrowTree K
  | [] => memory
  | tag::rest =>
      let result := entry.allocation.extra.releaseProtector tag protections
      let nextEntry := {entry with allocation := entry.allocation.setExtra result.tree}
      memoryAfter (StackPopRelease.commitTree memory id entry result.tree) id nextEntry protections rest

private theorem released_record (result : BorrowTree.ProtectorReleaseResult) (complete : result.status = .Released) :
    result = ⟨result.tree,.Released⟩ := by
  cases result
  cases complete
  rfl

/-- The source stack-pop Plan is derived from initial readable tree data and
mapped held tags. Neither a Plan nor any individual release success is an input. -/
theorem plan {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (protections : ProtectedTags) (tags : List BorTag) (root : UniIndex)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296) (depth : ParentDepth entry.allocation.extra.nodes)
    (children : GeneralBorrowGraph.ChildNodes entry.allocation.extra) (roots : entry.allocation.extra.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra) (mapped : Tags entry.allocation.extra protections tags)
    (initial : Every (Profile entry.allocation.extra protections) entry.allocation.extra.locations) :
    StackPopRelease.Plan protections (tags.map (fun tag => (id,tag))) memory (memoryAfter memory id entry protections tags) := by
  have history := GeneralBorrowProtectedReleaseHistory.run entry.allocation.extra protections tags root fits depth children roots covered mapped initial
  have build : ∀ tags (memory : MemoryState Provenance BorrowTree K) (entry : LocalAllocation Provenance BorrowTree K),
      memory.live.find? (fun row => row.1 == id) = some (id,entry) → AllReleased entry.allocation.extra protections tags →
      StackPopRelease.Plan protections (tags.map (fun tag => (id,tag))) memory (memoryAfter memory id entry protections tags) := by
    intro tags
    induction tags with
    | nil => intro memory entry _ _;exact StackPopRelease.Plan.nil memory
    | cons tag rest ih =>
      intro memory entry present complete
      obtain ⟨released,tail⟩ := complete
      let result := entry.allocation.extra.releaseProtector tag protections
      let nextEntry := {entry with allocation := entry.allocation.setExtra result.tree}
      have lookup := StackPopRelease.lookup_commit_same memory id entry result.tree
      have after := ih (StackPopRelease.commitTree memory id entry result.tree) nextEntry lookup tail
      exact StackPopRelease.Plan.live id tag entry result.tree (rest.map (fun tag => (id,tag))) memory _ present
        (released_record result released) after
  exact build tags memory entry present history.1

/-- The ACTUAL MachineHooks stack-pop ensure/release/commit/endCall sequence
completes for arbitrary finite frame tags on one live allocation. Initial tree
profiles and frame/heap metadata derive the Plan internally; the full global
protector table remains in force throughout every release. Final cache
coherence after removing the frame's tags is not claimed. -/
theorem before_stack_pop {K U : Type} [DecidableEq K]
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker) (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tags : List BorTag) (root : UniIndex)
    (rows : borrowFrame.protectedTags.toList = tags.map (fun tag => (id,tag)))
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296) (depth : ParentDepth entry.allocation.extra.nodes)
    (children : GeneralBorrowGraph.ChildNodes entry.allocation.extra) (roots : entry.allocation.extra.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (mapped : Tags entry.allocation.extra tracker.global.protectedTags tags)
    (initial : Every (Profile entry.allocation.extra tracker.global.protectedTags) entry.allocation.extra.locations) :
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with
        memory := memoryAfter state.machine.memory id entry tracker.global.protectedTags tags,
        borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} := by
  apply StackPopRelease.before_stack_pop_of_plan globalKind globals sync state tracker frame borrowFrame enabled current framed
  rw [rows]
  exact plan state.machine.memory id entry tracker.global.protectedTags tags root present fits depth children roots covered mapped initial

/-- The matching endCall removes exactly the listed frame-owned tags, while
retaining the previous kind of every unrelated global entry. -/
theorem end_call_get (global : GlobalState) (borrowFrame : FrameState) (id : AllocId) (tags : List BorTag)
    (rows : borrowFrame.protectedTags.toList = tags.map (fun tag => (id,tag))) (query : BorTag) :
    (global.endCall borrowFrame).protectedTags.get query = if query ∈ tags then none else global.protectedTags.get query := by
  rw [StackPopRelease.end_call_get,rows]
  simp [List.map_map,Function.comp_def]
end DuplicatePrefix.GeneralBorrowProtectedStackPopHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedStackPopHistory.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected stack-pop history dependency {dependency}"
