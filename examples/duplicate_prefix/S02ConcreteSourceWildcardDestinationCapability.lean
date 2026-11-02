import duplicate_prefix.S02ConcreteSourceWildcardReturnPacket
import duplicate_prefix.S02SeparateDestinationRuntimeRebase
import duplicate_prefix.GeneralBorrowRawSharedToLenLedger

namespace DuplicatePrefix.S02ConcreteSourceWildcardDestinationCapability
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- Source-side Ref/len leaves the distinct wildcard return tree authorized
under the new tracker, including its high-water RuntimeFacts. -/
theorem preserved
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    {sourceId : AllocId} {sourceTag : BorTag} {borrowFrame : FrameState}
    (packet : S02ConcreteSourceWildcardReturnPacket.ReturnPacket machine place sourceId sourceTag borrowFrame)
    (tracker held : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (sourceTree finalTree : BorrowTree) (selected : UniIndex)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph sourceTree finalTree selected tracker held) :
    DuplicatePrefixBorrowContract.RuntimeFacts packet.destination.entry.allocation.extra held.global ∧
    DuplicatePrefixBorrowAuthorization.Positive packet.destination.entry.allocation.extra held.global.protectedTags
      (some packet.child) (some packet.child) (some packet.returnTag) packet.destination.offset 1 := by
  have same : packet.tracker = tracker := Option.some.inj (packet.enabled.symm.trans enabled)
  have counter : packet.tracker.global.nextPointerTag.value.toNat ≤ held.global.nextPointerTag.value.toNat := by
    rw [same]
    have h := graph.tagCounter
    omega
  have runtime := S02SeparateDestinationRuntimeRebase.advance packet.destination.entry.allocation.extra
    packet.tracker.global held.global packet.runtime (by rw [same]; exact graph.protections) counter
  have positive : DuplicatePrefixBorrowAuthorization.Positive packet.destination.entry.allocation.extra
      held.global.protectedTags (some packet.child) (some packet.child) (some packet.returnTag)
      packet.destination.offset 1 := by
    rw [graph.protections,←same]
    exact packet.positive
  exact ⟨runtime,positive⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardDestinationCapability

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardDestinationCapability.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard destination capability dependency {dependency}"
