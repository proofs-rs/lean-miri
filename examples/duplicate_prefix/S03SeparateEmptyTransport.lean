import duplicate_prefix.S03FinalReturnInputBounds
import duplicate_prefix.S04FinalReturnWildcardInput

namespace DuplicatePrefix.S03SeparateEmptyTransport
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The actual other-allocation commit retains this entire current concrete destination. -/
def concrete {before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    (input : S03FinalReturnInputBounds.Destination before place)
    (live : after.memory.live.find? (fun row => row.1 == input.id) = some (input.id,input.entry))
    (addresses : after.user.addresses = before.user.addresses) :
    S03FinalReturnInputBounds.Destination after place where
  pointer := input.pointer
  physicalPointer := input.physicalPointer
  layout := input.layout
  aligned := input.aligned
  id := input.id
  entry := input.entry
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
  borrowSize := input.borrowSize
  tag := input.tag
  parent := input.parent
  concrete := input.concrete
  tagged := input.tagged

/-- The current wildcard destination and inverse-map geometry survive the exact frame. -/
def wildcard {before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    (input : S04FinalReturnWildcardInput.Destination before place)
    (live : after.memory.live.find? (fun row => row.1 == input.id) = some (input.id,input.entry))
    (addresses : after.user.addresses = before.user.addresses) :
    S04FinalReturnWildcardInput.Destination after place where
  pointer := input.pointer
  physicalPointer := input.physicalPointer
  layout := input.layout
  aligned := input.aligned
  id := input.id
  entry := input.entry
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
  borrowSize := input.borrowSize
  wildcard := input.wildcard
  mode := by rw [addresses];exact input.mode
  exposed := by rw [addresses];exact input.exposed
  geometry := by rw [addresses];exact input.geometry

end
end DuplicatePrefix.S03SeparateEmptyTransport
