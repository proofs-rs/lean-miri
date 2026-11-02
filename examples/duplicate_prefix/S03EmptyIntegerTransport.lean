import duplicate_prefix.S03FinalReturnInputBounds
import duplicate_prefix.S04FinalReturnWildcardInput

namespace DuplicatePrefix.S03EmptyIntegerTransport
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The integer empty body changes no allocation or address-map metadata. -/
def concrete {before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    (input : S03FinalReturnInputBounds.Destination before place)
    (memory : after.memory = before.memory) (addresses : after.user.addresses = before.user.addresses) :
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
  live := by rw [memory];exact input.live
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

/-- Wildcard inverse-map geometry is retained by the same exact metadata frame. -/
def wildcard {before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    (input : S04FinalReturnWildcardInput.Destination before place)
    (memory : after.memory = before.memory) (addresses : after.user.addresses = before.user.addresses) :
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
  live := by rw [memory];exact input.live
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

/-- Raising the checked tag counter leaves all current borrow permissions and
runtime consistency intact. The actual body supplies both data equalities. -/
theorem runtime (tree : BorrowTree) (before after : GlobalState)
    (current : DuplicatePrefixBorrowContract.RuntimeFacts tree before)
    (same : after = {before with nextPointerTag := after.nextPointerTag})
    (raise : before.nextPointerTag.value.toNat ≤ after.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree after := by
  have raised : DuplicatePrefixBorrowContract.RuntimeFacts tree {before with nextPointerTag := after.nextPointerTag} :=
    ⟨current.formed,current.coherent,current.possible,
      GeneralBorrowForestTagHighWaterHistory.weaken tree before.protectedTags before.nextPointerTag after.nextPointerTag current.below raise⟩
  exact same.symm ▸ raised

end
end DuplicatePrefix.S03EmptyIntegerTransport
