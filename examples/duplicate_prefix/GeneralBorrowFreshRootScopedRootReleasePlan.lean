import duplicate_prefix.GeneralBorrowFreshRootScopedBothRelease
import duplicate_prefix.ActualPopPlan
import duplicate_prefix.PhysicalMachineWrite

namespace DuplicatePrefix.GeneralBorrowFreshRootScopedRootReleasePlan
open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- Release data for the real root's ordered buffer/return-slot protector pair.
The buffer tree is arbitrary; raw owner-window and runtime conditions
are explicit. No successful release or stack-pop proposition is a field. -/
structure Input (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (global : Miri.TreeBorrows.GlobalState) where
  id : AllocId
  tag : BorTag
  buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind
  present : memory.live.find? (fun row => row.1 == id) = some (id,buffer)
  anchor : UniIndex
  selected : UniIndex
  maximum : BorTag
  offset : UInt64
  len : UInt64
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts buffer.allocation.extra global
  positive : GeneralBorrowFreshRootScopedRow.Positive buffer.allocation.extra global.protectedTags
    anchor selected maximum offset len
  node : TreeNode
  anchorPresent : buffer.allocation.extra.nodeAt anchor = some node
  notExposed : node.isExposed = false
  tagPresent : buffer.allocation.extra.indexOfTag tag = some anchor
  distinct : buffer.allocation.extra.roots.toList.Nodup
  short : buffer.allocation.extra.nodes.size < 65536
  active : GeneralBorrowFreshActiveWithin.ActiveWithin buffer.allocation.extra anchor .Write offset (offset+len)
  slotId : AllocId
  separate : slotId ≠ id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : memory.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true
  slotRootFree : global.protectedTags.contains slotRoot = false
  slotChildHeld : global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild

noncomputable def bufferRelease {memory global} (input : Input memory global) :=
  input.buffer.allocation.extra.releaseProtector input.tag global.protectedTags

def frame {memory global} (input : Input memory global) : FrameState :=
  (({} : FrameState).addProtector input.id input.tag).addProtector input.slotId input.slotChild

noncomputable def releasedMemory {memory global} (input : Input memory global) :=
  StackPopRelease.commitTree
    (StackPopRelease.commitTree memory input.id input.buffer (bufferRelease input).tree)
    input.slotId input.slot input.slot.allocation.extra

private theorem complete_result (result : BorrowTree.ProtectorReleaseResult) (done : result.status = .Released) :
    result = ⟨result.tree,.Released⟩ := by
  cases result with | mk tree status => cases done;rfl

/-- Derive the real associated Read/Write release from current raw resources. -/
theorem buffer_released {memory global} (input : Input memory global) :
    (bufferRelease input).status = .Released ∧
    DuplicatePrefixBorrowContract.RuntimeFacts (bufferRelease input).tree global ∧
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive (bufferRelease input).tree global.protectedTags
      input.anchor input.selected input.maximum input.offset input.len) := by
  obtain ⟨done,runtime,positive,rest⟩ := GeneralBorrowFreshRootScopedBothRelease.release input.buffer.allocation.extra global
    input.runtime input.tag input.anchor input.selected input.maximum input.offset input.len input.positive
    input.node input.anchorPresent input.notExposed input.tagPresent input.distinct input.short input.active
  exact ⟨done,runtime,positive⟩

/-- Execute the real two-row release order before the global endCall fold. -/
theorem to_plan {memory global} (input : Input memory global) :
    StackPopRelease.Plan global.protectedTags (frame input).protectedTags.toList memory (releasedMemory input) := by
  change StackPopRelease.Plan global.protectedTags [(input.id,input.tag),(input.slotId,input.slotChild)] memory (releasedMemory input)
  apply StackPopRelease.Plan.live input.id input.tag input.buffer (bufferRelease input).tree
    [(input.slotId,input.slotChild)] memory (releasedMemory input) input.present
    (complete_result _ (buffer_released input).1)
  apply StackPopRelease.Plan.live input.slotId input.slotChild input.slot input.slot.allocation.extra []
    (StackPopRelease.commitTree memory input.id input.buffer (bufferRelease input).tree)
    (releasedMemory input)
    (StackPopRelease.lookup_commit_other memory input.id input.slotId input.buffer input.slot
      (bufferRelease input).tree input.separate input.slotPresent)
  · rw [input.slotTree]
    exact ReturnTreeAccess.slot_release input.slotRoot input.slotChild 1 true global.protectedTags
      input.slotRootFree input.slotChildHeld input.slotDistinct (by decide)
  · exact .nil _

/-- The generic buffer release preserves the independent return-slot allocation. -/
theorem slot_lookup {memory global} (input : Input memory global) :
    (releasedMemory input).live.find? (fun row => row.1 == input.slotId) = some (input.slotId,input.slot) := by
  have same (allocation : Allocation Provenance BorrowTree) : allocation.setExtra allocation.extra = allocation := by
    cases allocation
    rfl
  simpa only [releasedMemory,same] using StackPopRelease.lookup_commit_same
    (StackPopRelease.commitTree memory input.id input.buffer (bufferRelease input).tree)
    input.slotId input.slot input.slot.allocation.extra

/-- The production pop is proved from the data-only plan input. -/
theorem pop
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (input : Input machine.memory tracker.global)
    (framed : caller.extra.borrowTracker = some (frame input))
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let config := PreparedContracts.actualConfig options () remaining span
    (GenericCallReturn.sourceControl config limits).popFrame () (Storage.withCurrent frames caller machine) =
      (⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames caller
        (ActualPopPlan.released machine (releasedMemory input) tracker (frame input))
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok caller) :=
  ActualPopPlan.pop_of_plan options limits remaining span frames caller machine tracker (frame input)
    tracked framed (releasedMemory input) (to_plan input) thread active

end DuplicatePrefix.GeneralBorrowFreshRootScopedRootReleasePlan
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowFreshRootScopedRootReleasePlan.buffer_released,
      ``DuplicatePrefix.GeneralBorrowFreshRootScopedRootReleasePlan.to_plan,
      ``DuplicatePrefix.GeneralBorrowFreshRootScopedRootReleasePlan.slot_lookup,
      ``DuplicatePrefix.GeneralBorrowFreshRootScopedRootReleasePlan.pop] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved generic root release plan dependency {dependency}"
