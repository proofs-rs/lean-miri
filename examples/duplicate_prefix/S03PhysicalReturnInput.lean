import duplicate_prefix.DuplicatePrefixReturnPlaceInput
import duplicate_prefix.RootCompilerFacts

namespace DuplicatePrefix.S03PhysicalReturnInput
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.Interpreter

set_option autoImplicit false in
/-- Internal current physical return packet. Pointer bounds are sufficient
for the actual provenance clear; original caller Input retains full structural
well-formedness. No execution-success assumption is stored here. -/
structure Input (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) where
  tracker : MachineHooks.BorrowState
  enabled : before.borrowTracker = some tracker
  pointer : Pointer Provenance
  physicalPointer : place.mplace.ptr = pointer.withOptionalProvenance
  layout : place.layout = RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned = none
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  capacity : UInt64
  live : before.memory.live.find? (fun row => row.1 == id) = some (id, entry)
  cachedBase : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩
  pointerAddress : pointer.offset.bytes = base + offset
  nonnull : pointer.offset.bytes ≠ 0
  addressFits : base.toNat + capacity.toNat < 2^64
  bounds : offset.toNat + 1 ≤ capacity.toNat
  size : entry.allocation.byteSize = Size.ofBytes capacity
  bytes : entry.allocation.len = capacity.toNat
  mutable : entry.allocation.mutability = .Mut
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = Size.ofBytes capacity
  pointerBounds : ∀ row ∈ entry.allocation.provenanceMap.ptrs, row.1.bytes.toNat+8≤entry.allocation.len
  borrowSize : entry.allocation.extra.locations.size.bytes = capacity
  source : Option UniIndex
  selectedRoot : Option UniIndex
  maximum : Option BorTag
  binding : DuplicatePrefixReferenceInput.Binding before.user.addresses pointer id base
    entry.allocation.byteSize entry.allocation.extra source
  borrow : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
    source selectedRoot maximum offset 1

/-- The public caller packet supplies the weaker internal storage invariant. -/
def Input.of_input {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : DuplicatePrefixReturnPlaceInput.Input before place) :
    Input before place where
  tracker := input.tracker
  enabled := input.enabled
  pointer := input.pointer
  physicalPointer := input.physicalPointer
  layout := input.layout
  aligned := input.aligned
  id := input.id
  entry := input.entry
  base := input.base
  offset := input.offset
  capacity := input.capacity
  live := input.live
  cachedBase := input.cachedBase
  pointerAddress := input.pointerAddress
  nonnull := input.nonnull
  addressFits := input.addressFits
  bounds := input.bounds
  size := input.size
  bytes := input.bytes
  mutable := input.mutable
  maskValid := input.maskValid
  maskLength := input.maskLength
  pointerBounds := ProvenanceCopy.WellFormed.pointerBounds input.provenanceMap
  borrowSize := input.borrowSize
  source := input.source
  selectedRoot := input.selectedRoot
  maximum := input.maximum
  binding := input.binding
  borrow := input.borrow

/-- The destination is a real byte of its backing allocation, not a one-past
pointer. This follows from raw capacity containment. -/
theorem Input.inside {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : Input before place) :
    input.offset.toNat < input.capacity.toNat := by
  have bound := input.bounds
  omega

/-- The normalized physical address and the one-byte interval do not wrap.
Neither address equality nor bounds is replaced by a successful memory access. -/
theorem Input.address_interval {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : Input before place) :
    input.pointer.offset.bytes.toNat = input.base.toNat + input.offset.toNat ∧
    input.pointer.offset.bytes.toNat + 1 ≤ input.base.toNat + input.capacity.toNat ∧
    (input.offset + 1).toNat = input.offset.toNat + 1 := by
  have bound := input.bounds
  have fits := input.addressFits
  have capacityFits := input.capacity.toNat_lt
  have addressFits : input.base.toNat + input.offset.toNat < 2^64 := by omega
  have intervalFits : input.offset.toNat + 1 < 2^64 := by omega
  have address : input.pointer.offset.bytes.toNat = input.base.toNat + input.offset.toNat := by
    rw [input.pointerAddress, UInt64.toNat_add, Nat.mod_eq_of_lt addressFits]
  refine ⟨address, by omega, ?_⟩
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt intervalFits

end DuplicatePrefix.S03PhysicalReturnInput
