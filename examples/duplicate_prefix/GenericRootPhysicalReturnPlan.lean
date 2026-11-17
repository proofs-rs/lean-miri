import duplicate_prefix.GeneralBorrowFreshReleaseLoop
import duplicate_prefix.ActualPopPlan
import duplicate_prefix.PhysicalMachineWrite

namespace DuplicatePrefix.GenericRootPhysicalReturnPlan
open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- Release data for the real root's ordered buffer/return-slot protector pair.
The buffer tree is arbitrary; only its graph, active range and slice ownership
are constrained. No successful release or stack-pop proposition is a field. -/
structure Input (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (protections : ProtectedTags) where
  id : AllocId
  tag : BorTag
  buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind
  present : memory.live.find? (fun row => row.1 == id) = some (id,buffer)
  anchor : UniIndex
  root : UniIndex
  kind : AccessKind
  lower : UInt64
  upper : UInt64
  positive : lower.toNat < upper.toNat
  fits : buffer.allocation.extra.nodes.data.size ≤ 4294967296
  depth : GeneralBorrowExposure.ParentDepth buffer.allocation.extra.nodes
  children : GeneralBorrowGraph.ChildNodes buffer.allocation.extra
  node : TreeNode
  anchorPresent : buffer.allocation.extra.nodeAt anchor = some node
  notExposed : node.isExposed = false
  roots : buffer.allocation.extra.roots = #[root]
  covered : GeneralBorrowGraph.RootsCover buffer.allocation.extra
  tagPresent : buffer.allocation.extra.indexOfTag tag = some anchor
  active : GeneralBorrowFreshReleaseLoop.ActiveOn buffer.allocation.extra anchor kind lower upper
  owned : OwnedOn (GeneralBorrowRange.LocationOwned buffer.allocation.extra protections anchor kind)
    lower upper buffer.allocation.extra.locations
  slotId : AllocId
  separate : slotId ≠ id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : memory.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true
  slotRootFree : protections.contains slotRoot = false
  slotChildHeld : protections.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild

noncomputable def bufferRelease {memory protections} (input : Input memory protections) :=
  input.buffer.allocation.extra.releaseProtector input.tag protections

def frame {memory protections} (input : Input memory protections) : FrameState :=
  (({} : FrameState).addProtector input.id input.tag).addProtector input.slotId input.slotChild

noncomputable def releasedMemory {memory protections} (input : Input memory protections) :=
  StackPopRelease.commitTree
    (StackPopRelease.commitTree memory input.id input.buffer (bufferRelease input).tree)
    input.slotId input.slot input.slot.allocation.extra

private theorem complete_result (result : BorrowTree.ProtectorReleaseResult) (done : result.status = .Released) :
    result = ⟨result.tree,.Released⟩ := by
  cases result with | mk tree status => cases done;rfl

/-- The actual buffer release is derived from slice ownership and active-range
coherence, with no restriction to canonical nested-tree constructors. -/
theorem buffer_released {memory protections} (input : Input memory protections) :
    (bufferRelease input).status = .Released ∧
    OwnedOn (GeneralBorrowRange.LocationOwned (bufferRelease input).tree protections input.anchor input.kind)
      input.lower input.upper (bufferRelease input).tree.locations :=
  GeneralBorrowFreshReleaseLoop.release input.buffer.allocation.extra protections input.tag input.anchor input.root
    input.kind input.lower input.upper input.positive input.fits input.depth input.children input.node input.anchorPresent
    input.notExposed input.roots input.covered input.tagPresent input.active input.owned

/-- Execute the real two-row release order before the global endCall fold. -/
theorem to_plan {memory protections} (input : Input memory protections) :
    StackPopRelease.Plan protections (frame input).protectedTags.toList memory (releasedMemory input) := by
  change StackPopRelease.Plan protections [(input.id,input.tag),(input.slotId,input.slotChild)] memory (releasedMemory input)
  apply StackPopRelease.Plan.live input.id input.tag input.buffer (bufferRelease input).tree
    [(input.slotId,input.slotChild)] memory (releasedMemory input) input.present
    (complete_result _ (buffer_released input).1)
  apply StackPopRelease.Plan.live input.slotId input.slotChild input.slot input.slot.allocation.extra []
    (StackPopRelease.commitTree memory input.id input.buffer (bufferRelease input).tree)
    (releasedMemory input)
    (StackPopRelease.lookup_commit_other memory input.id input.slotId input.buffer input.slot
      (bufferRelease input).tree input.separate input.slotPresent)
  · rw [input.slotTree]
    exact ReturnTreeAccess.slot_release input.slotRoot input.slotChild 1 true protections
      input.slotRootFree input.slotChildHeld input.slotDistinct (by decide)
  · exact .nil _

/-- The generic buffer release preserves the independent return-slot allocation. -/
theorem slot_lookup {memory protections} (input : Input memory protections) :
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
    (input : Input machine.memory tracker.global.protectedTags)
    (framed : caller.extra.borrowTracker = some (frame input))
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let config := PreparedContracts.actualConfig options () remaining span
    (GenericCallReturn.sourceControl config limits).popFrame () (Storage.withCurrent frames caller machine) =
      (⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames caller
        (ActualPopPlan.released machine (releasedMemory input) tracker (frame input))
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok caller) :=
  ActualPopPlan.pop_of_plan options limits remaining span frames caller machine tracker (frame input)
    tracked framed (releasedMemory input) (to_plan input) thread active

end DuplicatePrefix.GenericRootPhysicalReturnPlan
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GenericRootPhysicalReturnPlan.buffer_released,
      ``DuplicatePrefix.GenericRootPhysicalReturnPlan.to_plan,
      ``DuplicatePrefix.GenericRootPhysicalReturnPlan.slot_lookup,
      ``DuplicatePrefix.GenericRootPhysicalReturnPlan.pop] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved generic root release plan dependency {dependency}"
