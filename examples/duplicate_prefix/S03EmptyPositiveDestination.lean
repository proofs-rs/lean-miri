import duplicate_prefix.S03EmptyIntegerTransport

namespace DuplicatePrefix.S03EmptyPositiveDestination
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Zero Shared/len operations change only BorrowTree extras in their one live
allocation. Physical bytes, masks, provenance, capacity and layout remain exact. -/
def concrete {before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : S03FinalReturnInputBounds.Destination before place)
    (tree : BorrowTree)
    (live : after.memory.live.find? (fun row => row.1 == input.id) =
      some (input.id,{input.entry with allocation := input.entry.allocation.setExtra tree}))
    (addresses : after.user.addresses = before.user.addresses)
    (capacity : tree.locations.size = input.entry.allocation.extra.locations.size)
    (tagged : tree.indexOfTag input.tag = some input.parent) :
    S03FinalReturnInputBounds.Destination after place where
  pointer := input.pointer
  physicalPointer := input.physicalPointer
  layout := input.layout
  aligned := input.aligned
  id := input.id
  entry := {input.entry with allocation := input.entry.allocation.setExtra tree}
  base := input.base
  offset := input.offset
  capacity := input.capacity
  live := live
  cachedBase := by rw [addresses];exact input.cachedBase
  pointerAddress := input.pointerAddress
  nonnull := input.nonnull
  addressFits := input.addressFits
  bounds := input.bounds
  size := input.size
  bytes := input.bytes
  mutable := input.mutable
  maskValid := input.maskValid
  maskLength := input.maskLength
  pointerBounds := input.pointerBounds
  borrowSize := by change tree.locations.size.bytes = input.capacity;rw [capacity];exact input.borrowSize
  tag := input.tag
  parent := input.parent
  concrete := input.concrete
  tagged := tagged

/-- The same exact physical frame retains wildcard inverse-map geometry. -/
def wildcard {before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : S04FinalReturnWildcardInput.Destination before place)
    (tree : BorrowTree)
    (live : after.memory.live.find? (fun row => row.1 == input.id) =
      some (input.id,{input.entry with allocation := input.entry.allocation.setExtra tree}))
    (addresses : after.user.addresses = before.user.addresses)
    (capacity : tree.locations.size = input.entry.allocation.extra.locations.size) :
    S04FinalReturnWildcardInput.Destination after place where
  pointer := input.pointer
  physicalPointer := input.physicalPointer
  layout := input.layout
  aligned := input.aligned
  id := input.id
  entry := {input.entry with allocation := input.entry.allocation.setExtra tree}
  base := input.base
  offset := input.offset
  capacity := input.capacity
  live := live
  cachedBase := by rw [addresses];exact input.cachedBase
  pointerAddress := input.pointerAddress
  nonnull := input.nonnull
  addressFits := input.addressFits
  bounds := input.bounds
  size := input.size
  bytes := input.bytes
  mutable := input.mutable
  maskValid := input.maskValid
  maskLength := input.maskLength
  pointerBounds := input.pointerBounds
  borrowSize := by change tree.locations.size.bytes = input.capacity;rw [capacity];exact input.borrowSize
  wildcard := input.wildcard
  mode := by rw [addresses];exact input.mode
  exposed := by rw [addresses];exact input.exposed
  geometry := by rw [addresses];exact input.geometry

end
end DuplicatePrefix.S03EmptyPositiveDestination
