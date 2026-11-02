import duplicate_prefix.S04FinalReturnWildcardInput
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S02SeparateDestinationTickLedger
import duplicate_prefix.GeneralBorrowRawLenRejectedFrame

namespace DuplicatePrefix.S02ConcreteSourceWildcardPhysicalTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- An operation on a distinct source allocation preserves the physical
wildcard return descriptor, including its inverse-map geometry. -/
def other_source
    {place : MPlaceTy Provenance}
    {machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    (destination : S04FinalReturnWildcardInput.Destination machine place)
    (live : post.memory.live.find? (fun row => row.1 == destination.id) =
      some (destination.id,destination.entry))
    (addresses : post.user.addresses = machine.user.addresses) :
    S04FinalReturnWildcardInput.Destination post place where
  pointer := destination.pointer
  physicalPointer := destination.physicalPointer
  layout := destination.layout
  aligned := destination.aligned
  id := destination.id
  entry := destination.entry
  base := destination.base
  offset := destination.offset
  capacity := destination.capacity
  live := live
  cachedBase := by rw [addresses]; exact destination.cachedBase
  pointerAddress := destination.pointerAddress
  nonnull := destination.nonnull
  addressFits := destination.addressFits
  bounds := destination.bounds
  size := destination.size
  bytes := destination.bytes
  mutable := destination.mutable
  maskValid := destination.maskValid
  maskLength := destination.maskLength
  pointerBounds := destination.pointerBounds
  borrowSize := destination.borrowSize
  wildcard := destination.wildcard
  mode := by rw [addresses]; exact destination.mode
  exposed := by rw [addresses]; exact destination.exposed
  geometry := by rw [addresses]; exact destination.geometry

/-- Transport through actual Ref/len's source-only tree update. -/
def after_shared
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    {place : MPlaceTy Provenance}
    {machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    (destination : S04FinalReturnWildcardInput.Destination machine place)
    (source : AllocId) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tree : BorrowTree) (different : source ≠ destination.id)
    (memory : post.memory = RetagEntry.updatedMemory
      (RootZeroCompleteState.tick options remaining span machine).memory source sourceEntry tree)
    (addresses : post.user.addresses =
      (RootZeroCompleteState.tick options remaining span machine).user.addresses) :
    S04FinalReturnWildcardInput.Destination post place := by
  obtain ⟨tickMemory,_borrow,_race,_threads,tickAddresses,_types,_backend,_extras⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span machine
  have present : post.memory.live.find? (fun row => row.1 == destination.id) =
      some (destination.id,destination.entry) := by
    rw [memory,tickMemory,S02SeparateDestinationTransport.other_live _ _ _ _ _ different]
    exact destination.live
  exact other_source destination present (addresses.trans tickAddresses)

/-- Rejected guard accounting performs no memory or address change. -/
def after_guard
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    {place : MPlaceTy Provenance}
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : S04FinalReturnWildcardInput.Destination post place) :
    S04FinalReturnWildcardInput.Destination
      (RootZeroCompleteState.tick options remaining span
        (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span post))) place := by
  obtain ⟨memory,_borrow,_race,_threads,addresses,_types,_extras,_backend⟩ :=
    GeneralBorrowRawLenRejectedFrame.machine_ledger options remaining span post
  exact other_source destination (by rw [memory]; exact destination.live) addresses

end
end DuplicatePrefix.S02ConcreteSourceWildcardPhysicalTransport

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S02ConcreteSourceWildcardPhysicalTransport.other_source,
      ``DuplicatePrefix.S02ConcreteSourceWildcardPhysicalTransport.after_shared,
      ``DuplicatePrefix.S02ConcreteSourceWildcardPhysicalTransport.after_guard] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved wildcard physical transport dependency {declaration}: {dependency}"
