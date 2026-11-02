import duplicate_prefix.GeneralBorrowForestAcceptedFunctionSafety
import duplicate_prefix.GeneralBorrowForestRejectedFunctionSafety
import duplicate_prefix.GeneralBorrowForestZeroSafety
namespace DuplicatePrefix.GeneralBorrowForestAllCountInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
/-- One ORIGINAL caller contract for arbitrary count. Initial forest, physical
memory, compiler settings and finite allocator/tag reserves are explicit.
Source-byte initialization and intrinsic size bounds are required only in the
numeric accepted branch. No guard outcome, poststate or successful operation
is supplied. Positive slice length remains an explicit scope condition. -/
structure Initial extends toOriginal : GeneralBorrowForestFunctionEntryZero.Initial where
  count : UInt64
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  fresh3 : (held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
  fresh4 : (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag.value < 18446744073709551615
  exprUnheld : (held tracker fresh slotFresh).global.protectedTags.contains (held tracker fresh slotFresh).global.nextPointerTag = false
  helperUnheld : (held tracker fresh slotFresh).global.protectedTags.get
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag = none
  rootFreeAfterHelper : ((TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4)
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag).global.endCall
      (({} : FrameState).addProtector id (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag)).protectedTags.contains slotRoot = false
  slotHeldAfterHelper : ((TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4)
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag).global.endCall
      (({} : FrameState).addProtector id (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag)).protectedTags.contains
      (next tracker fresh).global.nextPointerTag = true
  statementFuel : limits.validation = validityFuel+1
  allocator : GeneralBorrowGcAllocator.Invariant entry.allocation.extra
  room : entry.allocation.extra.nodes.size+8 ≤ 4294967295
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  exprFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (held tracker fresh slotFresh).global.nextPointerTag
  helperFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag
  rootExprDifferent : tracker.global.nextPointerTag ≠ (held tracker fresh slotFresh).global.nextPointerTag
  rootHelperDifferent : tracker.global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag
  storageBuffer : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  maskValidBuffer : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLengthBuffer : entry.allocation.initializationMask.len = entry.allocation.byteSize
  initializedBuffer : count ≤ len/2 → InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  provenanceBuffer : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  storageFitsBuffer : entry.allocation.len+64 < 18446744073709551616
  mutableBuffer : entry.allocation.mutability = .Mut
  bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  bounded : count ≤ len/2 → count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes
  fresh5 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag.value < 18446744073709551615
  fresh6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag.value < 18446744073709551615
  map5 : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag
  map6 : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag
  unheld5 : (held tracker fresh slotFresh).global.protectedTags.get (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag = none
  unheld6 : (held tracker fresh slotFresh).global.protectedTags.get
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag = none
  rootDifferent5 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag ≠ tracker.global.nextPointerTag
  rootDifferent6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag ≠ tracker.global.nextPointerTag
  exprDifferent5 : (held tracker fresh slotFresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag
  exprDifferent6 : (held tracker fresh slotFresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag
  helperDifferent5 : (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag
  helperDifferent6 : (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag
  different56 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag
  slotRootDifferent5 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag ≠ slotRoot
  slotRootDifferent6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag ≠ slotRoot
  slotChildDifferent5 : (next tracker fresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag
  slotChildDifferent6 : (next tracker fresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag

def nonzero (s : Initial) (positive : (0 : UInt64) < s.count) : GeneralBorrowForestNonzeroMachinePrefix.Initial := {
  toInitial := s.toOriginal
  countPositive := positive
  count := s.count
  preciseOff := s.preciseOff
  implicitOff := s.implicitOff
  budget := s.budget
  dispatchFuel := s.dispatchFuel
  fresh3 := s.fresh3
  fresh4 := s.fresh4
  exprUnheld := s.exprUnheld
  helperUnheld := s.helperUnheld
  rootFreeAfterHelper := s.rootFreeAfterHelper
  slotHeldAfterHelper := s.slotHeldAfterHelper
}

def accepted (s : Initial) (positive : (0 : UInt64) < s.count) (within : s.count ≤ s.len/2) :
    GeneralBorrowForestAcceptedFunctionSafety.Initial := {
  toPrefix := nonzero s positive
  within := within
  statementFuel := s.statementFuel
  allocator := s.allocator
  room := s.room
  vacantClean := s.vacantClean
  exprFresh := s.exprFresh
  helperFresh := s.helperFresh
  rootExprDifferent := s.rootExprDifferent
  rootHelperDifferent := s.rootHelperDifferent
  storageBuffer := s.storageBuffer
  maskValidBuffer := s.maskValidBuffer
  maskLengthBuffer := s.maskLengthBuffer
  initializedBuffer := s.initializedBuffer within
  provenanceBuffer := s.provenanceBuffer
  storageFitsBuffer := s.storageFitsBuffer
  mutableBuffer := s.mutableBuffer
  bufferExtras := s.bufferExtras
  bounded := s.bounded within
  fresh5 := s.fresh5
  fresh6 := s.fresh6
  map5 := s.map5
  map6 := s.map6
  unheld5 := s.unheld5
  unheld6 := s.unheld6
  rootDifferent5 := s.rootDifferent5
  rootDifferent6 := s.rootDifferent6
  exprDifferent5 := s.exprDifferent5
  exprDifferent6 := s.exprDifferent6
  helperDifferent5 := s.helperDifferent5
  helperDifferent6 := s.helperDifferent6
  different56 := s.different56
  slotRootDifferent5 := s.slotRootDifferent5
  slotRootDifferent6 := s.slotRootDifferent6
  slotChildDifferent5 := s.slotChildDifferent5
  slotChildDifferent6 := s.slotChildDifferent6
}

def rejected (s : Initial) (outside : s.count > s.len/2) : GeneralBorrowForestRejectedFunctionSafety.Initial := {
  toMachine := {
    toInitial := s.toOriginal
    rejected := outside
    count := s.count
    preciseOff := s.preciseOff
    implicitOff := s.implicitOff
    budget := s.budget
    dispatchFuel := s.dispatchFuel
    fresh3 := s.fresh3
    fresh4 := s.fresh4
    exprUnheld := s.exprUnheld
    helperUnheld := s.helperUnheld
    rootFreeAfterHelper := s.rootFreeAfterHelper
    slotHeldAfterHelper := s.slotHeldAfterHelper
  }
  allocator := s.allocator
  room := by change s.entry.allocation.extra.nodes.size+6 ≤ 4294967295;have room := s.room;omega
  vacantClean := s.vacantClean
  exprFresh := s.exprFresh
  helperFresh := s.helperFresh
  rootExprDifferent := s.rootExprDifferent
  rootHelperDifferent := s.rootHelperDifferent
}

end
end DuplicatePrefix.GeneralBorrowForestAllCountInput
