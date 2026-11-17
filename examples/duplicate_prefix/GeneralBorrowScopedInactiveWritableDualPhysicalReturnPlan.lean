import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDualRelease
import duplicate_prefix.ActualPopPlan
import duplicate_prefix.PhysicalMachineWrite

namespace DuplicatePrefix.GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan
open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
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
  selected : UniIndex
  head : UniIndex
  tail : List UniIndex
  lower : UInt64
  upper : UInt64
  positive : lower.toNat < upper.toNat
  fits : buffer.allocation.extra.nodes.data.size ≤ 4294967296
  context : GeneralBorrowExposedKnownRootRangeData.Context buffer.allocation.extra anchor selected head tail
  notExposed : context.anchorNode.isExposed = false
  tagPresent : buffer.allocation.extra.indexOfTag tag = some anchor
  active : GeneralBorrowFreshReleaseLoop.ActiveOn buffer.allocation.extra anchor .Write lower upper
  support : Nat → Prop
  owned : OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedInactiveWritableAccessData.Data
    buffer.allocation.extra location protections anchor selected head tail support)) lower upper buffer.allocation.extra.locations
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
      (bufferRelease input).tree = {input.buffer.allocation.extra with locations := (bufferRelease input).tree.locations} :=
  let done := GeneralBorrowExposedScopedInactiveWritableDualRelease.release input.buffer.allocation.extra protections input.tag input.anchor input.selected input.head input.tail
    input.context input.support input.lower input.upper input.positive input.fits input.notExposed input.tagPresent input.active input.owned
  ⟨done.1,done.2.1⟩

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

end DuplicatePrefix.GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan.buffer_released,
      ``DuplicatePrefix.GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan.to_plan,
      ``DuplicatePrefix.GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan.slot_lookup,
      ``DuplicatePrefix.GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan.pop] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved generic root release plan dependency {dependency}"
