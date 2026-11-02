import duplicate_prefix.S02ConcreteSourceWildcardPhysicalTransport
import duplicate_prefix.S02ConcreteSourceWildcardDestinationCapability
import duplicate_prefix.S02SeparateDestinationRuntimeRebase
import duplicate_prefix.CopyRootExitData

namespace DuplicatePrefix.S02ConcreteSourceWildcardAcceptedDestinationCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- The accepted guard's two accounting ticks preserve the wildcard return descriptor. -/
def after_guard (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    {place : MPlaceTy Provenance}
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : S04FinalReturnWildcardInput.Destination post place) :
    S04FinalReturnWildcardInput.Destination
      (RootZeroCompleteState.tick options remaining span
        (RootZeroCompleteState.tick options remaining span post)) place := by
  let first := RootZeroCompleteState.tick options remaining span post
  obtain ⟨memory1,_borrow1,_race1,_threads1,addresses1,_types1,_backend1,_extras1⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span post
  obtain ⟨memory2,_borrow2,_race2,_threads2,addresses2,_types2,_backend2,_extras2⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span first
  exact S02ConcreteSourceWildcardPhysicalTransport.other_source destination
    (by rw [memory2,memory1]; exact destination.live)
    (addresses2.trans addresses1)

/-- The source-only physical copy keeps the wildcard return byte's descriptor. -/
def after_copy {place : MPlaceTy Provenance}
    (before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : S04FinalReturnWildcardInput.Destination before place)
    (sourceId : AllocId) (sourceKind : MemoryKind MiriMemoryKind)
    (copied : Allocation Provenance BorrowTree)
    (different : destination.id ≠ sourceId)
    (memory : after.memory = CopyHelperCall.memoryAfter before.memory sourceId sourceKind copied)
    (addresses : after.user.addresses = before.user.addresses) :
    S04FinalReturnWildcardInput.Destination after place := by
  have live : after.memory.live.find? (fun row => row.1 == destination.id) =
      some (destination.id,destination.entry) := by
    rw [memory,CopyRootExitData.memory_after_eq_commit]
    exact StackPopRelease.lookup_commit_other before.memory sourceId destination.id
      ⟨sourceKind,copied⟩ destination.entry copied.extra different destination.live
  exact S02ConcreteSourceWildcardPhysicalTransport.other_source destination live addresses

/-- The wildcard return authorization survives source-only copy and tracker growth. -/
theorem capability
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} {sourceId : AllocId} {sourceTag : BorTag}
    {borrowFrame : FrameState}
    (packet : S02ConcreteSourceWildcardReturnPacket.ReturnPacket machine place sourceId sourceTag borrowFrame)
    (tracker held copyHeld : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (sourceTree finalTree : BorrowTree) (selected : UniIndex)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph sourceTree finalTree selected tracker held)
    (protections : copyHeld.global.protectedTags = held.global.protectedTags)
    (counter : held.global.nextPointerTag.value.toNat ≤ copyHeld.global.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts packet.destination.entry.allocation.extra copyHeld.global ∧
    DuplicatePrefixBorrowAuthorization.Positive packet.destination.entry.allocation.extra copyHeld.global.protectedTags
      (some packet.child) (some packet.child) (some packet.returnTag) packet.destination.offset 1 := by
  obtain ⟨runtime,positive⟩ :=
    S02ConcreteSourceWildcardDestinationCapability.preserved packet tracker held enabled
      sourceTree finalTree selected graph
  refine ⟨S02SeparateDestinationRuntimeRebase.advance _ _ _ runtime protections counter,?_⟩
  rw [protections]
  exact positive

end
end DuplicatePrefix.S02ConcreteSourceWildcardAcceptedDestinationCopy

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedDestinationCopy.after_guard,
      ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedDestinationCopy.after_copy,
      ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedDestinationCopy.capability] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved wildcard accepted destination-copy dependency {declaration}: {dependency}"
