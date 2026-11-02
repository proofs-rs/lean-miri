import duplicate_prefix.S02SeparateDestinationPhysicalTransport
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S02SeparateDestinationTickLedger

namespace DuplicatePrefix.S02SeparateDestinationRejectedPhysicalTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- The rejected body only replaces the source allocation, so its distinct concrete return place remains physically valid. -/
def after_body
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    {place : MPlaceTy Provenance}
    {machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    (destination : S03FinalReturnInputBounds.Destination machine place)
    (source : AllocId) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tree : BorrowTree) (different : source ≠ destination.id)
    (memory : post.memory = RetagEntry.updatedMemory
      (RootZeroCompleteState.tick options remaining span machine).memory source sourceEntry tree)
    (addresses : post.user.addresses = (RootZeroCompleteState.tick options remaining span machine).user.addresses) :
    S03FinalReturnInputBounds.Destination post place := by
  obtain ⟨tickMemory,_borrow,_race,_threads,tickAddresses,_types,_backend,_extras⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span machine
  have present : post.memory.live.find? (fun row => row.1 == destination.id) =
      some (destination.id,destination.entry) := by
    rw [memory,tickMemory,S02SeparateDestinationTransport.other_live _ _ _ _ _ different]
    exact destination.live
  exact S02SeparateDestinationPhysicalTransport.other_source destination present
    (addresses.trans tickAddresses)

end
end DuplicatePrefix.S02SeparateDestinationRejectedPhysicalTransport

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationRejectedPhysicalTransport.after_body) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved rejected physical transport dependency {dependency}"
