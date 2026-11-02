import duplicate_prefix.S02SeparateDestinationZeroCore
import duplicate_prefix.GeneralBorrowRowRootMetadata

namespace DuplicatePrefix.S02SeparateDestinationPacketSourceTag
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- The selected-root cutoff in the current source Positive packet identifies
its actual installed protector node; no extra constructor witness is needed. -/
theorem same
    {frame : CompilerFrameContext.ActualFrame}
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    (packet : S02SeparateDestinationZeroCore.Packet frame machine place)
    (selected : packet.sourceSelected = packet.sourceChild)
    (maximum : packet.sourceMaximum = some packet.sourceTag) :
    packet.sourceNode.tag = packet.sourceTag := by
  have geometry := GeneralBorrowRowRootMetadata.of_positive
    packet.sourceEntry.allocation.extra packet.tracker.global.protectedTags
    packet.sourceChild packet.sourceSelected packet.sourceMaximum
    packet.sourceOffset packet.sourceLen packet.sourceRuntime.formed.toState.well
    packet.sourcePositive
  obtain ⟨node,present,cutoff⟩ := geometry.root
  rw [selected] at present
  have nodeEq := Option.some.inj (packet.sourcePresent.symm.trans present)
  rw [nodeEq]
  exact Option.some.inj (by rw [maximum] at cutoff; exact cutoff.symm)

end
end DuplicatePrefix.S02SeparateDestinationPacketSourceTag

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationPacketSourceTag.same) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved packet source-tag dependency {dependency}"
