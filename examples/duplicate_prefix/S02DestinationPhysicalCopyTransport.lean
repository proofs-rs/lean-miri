import duplicate_prefix.S03FinalReturnInputBounds
import duplicate_prefix.CopyRootExitData

namespace DuplicatePrefix.S02DestinationPhysicalCopyTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open S03FinalReturnInputBounds
set_option autoImplicit false
noncomputable section

/-- A physical bool return place survives the actual copy helper's update
when its allocation is distinct from the copied source allocation. -/
def after_source_copy
    (before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (destination : Destination before place)
    (sourceId : AllocId) (sourceKind : MemoryKind MiriMemoryKind)
    (copied : Allocation Provenance BorrowTree)
    (distinct : destination.id ≠ sourceId)
    (memory : after.memory = CopyHelperCall.memoryAfter before.memory sourceId sourceKind copied)
    (addresses : after.user.addresses = before.user.addresses) :
    Destination after place := by
  have live : after.memory.live.find? (fun row => row.1 == destination.id) =
      some (destination.id,destination.entry) := by
    rw [memory,CopyRootExitData.memory_after_eq_commit]
    exact StackPopRelease.lookup_commit_other before.memory sourceId destination.id
      ⟨sourceKind,copied⟩ destination.entry copied.extra distinct destination.live
  have cached : after.user.addresses.baseAddr.find? (fun row => row.allocId == destination.id) =
      some ⟨destination.id,destination.base⟩ := by
    rw [addresses]
    exact destination.cachedBase
  exact {
    pointer := destination.pointer,
    physicalPointer := destination.physicalPointer,
    layout := destination.layout,
    aligned := destination.aligned,
    id := destination.id,
    entry := destination.entry,
    base := destination.base,
    offset := destination.offset,
    capacity := destination.capacity,
    live := live,
    cachedBase := cached,
    pointerAddress := destination.pointerAddress,
    nonnull := destination.nonnull,
    addressFits := destination.addressFits,
    bounds := destination.bounds,
    size := destination.size,
    bytes := destination.bytes,
    mutable := destination.mutable,
    maskValid := destination.maskValid,
    maskLength := destination.maskLength,
    pointerBounds := destination.pointerBounds,
    borrowSize := destination.borrowSize,
    tag := destination.tag,
    parent := destination.parent,
    concrete := destination.concrete,
    tagged := destination.tagged }

end
end DuplicatePrefix.S02DestinationPhysicalCopyTransport

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02DestinationPhysicalCopyTransport.after_source_copy) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved destination physical copy dependency {dependency}"
