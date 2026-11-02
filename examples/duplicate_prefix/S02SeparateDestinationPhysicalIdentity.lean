import duplicate_prefix.S03FinalReturnInputBounds

namespace DuplicatePrefix.S02SeparateDestinationPhysicalIdentity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false

/-- The concrete physical packet reconstructed after uninit still denotes
the very same original return allocation and parent tag. -/
theorem original {before machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (physical : S03FinalReturnInputBounds.Destination machine place)
    (returnTag : BorTag)
    (concrete : input.pointer.provenance = .concrete input.id returnTag) :
    physical.id = input.id ∧ physical.tag = returnTag := by
  have pointers := physical.physicalPointer.symm.trans input.physicalPointer
  have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) pointers
  simp only [Pointer.withOptionalProvenance,physical.concrete,concrete] at provenance
  have pair := Option.some.inj provenance
  exact Provenance.concrete.inj pair

end DuplicatePrefix.S02SeparateDestinationPhysicalIdentity

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationPhysicalIdentity.original) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination physical identity dependency {dependency}"
