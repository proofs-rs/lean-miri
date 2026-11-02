import duplicate_prefix.S02SameDestinationZeroCore
import duplicate_prefix.S02SeparateDestinationTickLedger

namespace DuplicatePrefix.S02SameDestinationRejectedPhysicalTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- Shared/len execution changes only the current common allocation's borrow
tree. Current byte, initialization and provenance bounds remain physical facts. -/
def after_body
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    {place : MPlaceTy Provenance}
    {machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    (destination : S03FinalReturnInputBounds.Destination machine place) (tree : BorrowTree)
    (memory : post.memory = RetagEntry.updatedMemory
      (RootZeroCompleteState.tick options remaining span machine).memory destination.id destination.entry tree)
    (addresses : post.user.addresses = (RootZeroCompleteState.tick options remaining span machine).user.addresses)
    (capacity : tree.locations.size = destination.entry.allocation.extra.locations.size)
    (tagged : tree.indexOfTag destination.tag = some destination.parent) :
    S03FinalReturnInputBounds.Destination post place := by
  obtain ⟨_memory,_borrow,_race,_threads,tickAddresses,_types,_backend,_extras⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span machine
  exact {
    pointer := destination.pointer,physicalPointer := destination.physicalPointer,
    layout := destination.layout,aligned := destination.aligned,id := destination.id,
    entry := {destination.entry with allocation := destination.entry.allocation.setExtra tree},
    base := destination.base,offset := destination.offset,capacity := destination.capacity,
    live := by rw [memory];exact MemoryCopyBridge.live_lookup_replaced _ _ _,
    cachedBase := by rw [addresses,tickAddresses];exact destination.cachedBase,
    pointerAddress := destination.pointerAddress,nonnull := destination.nonnull,
    addressFits := destination.addressFits,bounds := destination.bounds,
    size := destination.size,bytes := destination.bytes,mutable := destination.mutable,
    maskValid := destination.maskValid,maskLength := destination.maskLength,
    pointerBounds := destination.pointerBounds,
    borrowSize := by change tree.locations.size.bytes = destination.capacity;rw [capacity];exact destination.borrowSize,
    tag := destination.tag,parent := destination.parent,concrete := destination.concrete,tagged := tagged }

end
end DuplicatePrefix.S02SameDestinationRejectedPhysicalTransport
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedPhysicalTransport.after_body) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved same rejected physical transport dependency {dependency}"
