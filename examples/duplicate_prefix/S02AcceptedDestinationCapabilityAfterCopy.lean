import duplicate_prefix.S02SeparateDestinationRejectedDestinationCapability
import duplicate_prefix.S02SeparateDestinationRuntimeRebase

namespace DuplicatePrefix.S02AcceptedDestinationCapabilityAfterCopy
open Miri Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- The separate return byte retains its authorization across shared Ref/len
and the later source-only Default/as_mut/copy sequence. -/
theorem preserved
    {frame : CompilerFrameContext.ActualFrame}
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    (packet : S02SeparateDestinationZeroCore.Packet frame machine place)
    (tracker sharedHeld copyHeld : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (sourceTree finalTree : BorrowTree) (selected : UniIndex)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph sourceTree finalTree selected tracker sharedHeld)
    (protections : copyHeld.global.protectedTags = sharedHeld.global.protectedTags)
    (counter : sharedHeld.global.nextPointerTag.value.toNat ≤ copyHeld.global.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts packet.destination.entry.allocation.extra copyHeld.global ∧
    DuplicatePrefixBorrowAuthorization.Positive packet.destination.entry.allocation.extra copyHeld.global.protectedTags
      (some packet.child) (some packet.selected) packet.maximum packet.destination.offset 1 := by
  obtain ⟨sharedRuntime,sharedPositive⟩ :=
    S02SeparateDestinationRejectedDestinationCapability.preserved packet tracker sharedHeld enabled
      sourceTree finalTree selected graph
  have runtime := S02SeparateDestinationRuntimeRebase.advance
    packet.destination.entry.allocation.extra sharedHeld.global copyHeld.global
    sharedRuntime protections counter
  have positive : DuplicatePrefixBorrowAuthorization.Positive packet.destination.entry.allocation.extra
      copyHeld.global.protectedTags (some packet.child) (some packet.selected) packet.maximum
      packet.destination.offset 1 := by
    rw [protections]
    exact sharedPositive
  exact ⟨runtime,positive⟩

end
end DuplicatePrefix.S02AcceptedDestinationCapabilityAfterCopy

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedDestinationCapabilityAfterCopy.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted destination capability dependency {dependency}"
