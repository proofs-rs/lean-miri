import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionNonzeroLenMetadata
import duplicate_prefix.GeneralBorrowExposedScopedAcceptedCallInput
import duplicate_prefix.GeneralBorrowExposedScopedAsMutCallReturnReady
import duplicate_prefix.GeneralBorrowScopedCopyRootGuardBody
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
noncomputable section
abbrev lenHeld (s : GeneralBorrowPositiveWildcardPartitionNonzeroInput.Initial) :=
  let tracker := GeneralBorrowPositiveWildcardPartitionNonzeroInput.expressionTracker s.toBase
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker s.helperFresh) tracker.global.nextPointerTag
abbrev lenEnded (s : GeneralBorrowPositiveWildcardPartitionNonzeroInput.Initial) : MachineHooks.BorrowState :=
  let held := lenHeld s
  let tag := GeneralBorrowPositiveWildcardPartitionNonzeroInput.helperTag s.toBase
  {held with global:=held.global.endCall (({} : FrameState).addProtector s.id tag)}
abbrev mutableTag (s : GeneralBorrowPositiveWildcardPartitionNonzeroInput.Initial) := (lenEnded s).global.nextPointerTag
set_option autoImplicit false in
/-- Accepted-count original caller resources. Future tags, byte storage and
initialization concern the original input only; every later operation and
borrow resource is derived. Provenance maps are arbitrary well-formed maps. -/
structure Initial extends GeneralBorrowPositiveWildcardPartitionNonzeroInput.Initial where
  within : count≤len/2
  mutableFresh : (mutableTag toInitial).value<18446744073709551615
  mutableHelperFresh : (ReferenceBorrowDriver.allocatedTracker (lenEnded toInitial) mutableFresh).global.nextPointerTag.value<18446744073709551615
  mutableMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (mutableTag toInitial)
  mutableHelperMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (lenEnded toInitial) mutableFresh).global.nextPointerTag
  mutableUnheld : tracker.global.protectedTags.contains (mutableTag toInitial)=false
  mutableHelperUnheld : tracker.global.protectedTags.contains
    (ReferenceBorrowDriver.allocatedTracker (lenEnded toInitial) mutableFresh).global.nextPointerTag=false
  bufferStorage : entry.allocation.len=entry.allocation.byteSize.bytes.toNat
  bufferMaskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  bufferMaskLength : entry.allocation.initializationMask.len=entry.allocation.byteSize
  bufferInitialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes 0) (Size.ofBytes count)
  bufferProvenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  bufferStorageFits : entry.allocation.len+64<18446744073709551616
  bufferMutable : entry.allocation.mutability=.Mut
  bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==id)=some (id,⟨none,#[]⟩)
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedInput
