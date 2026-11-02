import duplicate_prefix.S03FinalReturnInputBounds

namespace DuplicatePrefix.S02SeparateDestinationPhysicalTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- A write to a different allocation preserves the physical return-place packet. -/
def other_source
    {place : MPlaceTy Provenance}
    {before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    (destination : S03FinalReturnInputBounds.Destination before place)
    (live : after.memory.live.find? (fun row => row.1 == destination.id) =
      some (destination.id,destination.entry))
    (addresses : after.user.addresses = before.user.addresses) :
    S03FinalReturnInputBounds.Destination after place := {
      destination with
      live := live
      cachedBase := by rw [addresses]; exact destination.cachedBase
    }

end
end DuplicatePrefix.S02SeparateDestinationPhysicalTransport

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationPhysicalTransport.other_source) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved physical transport dependency {dependency}"
