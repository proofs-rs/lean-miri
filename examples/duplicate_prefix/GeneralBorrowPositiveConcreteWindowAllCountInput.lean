import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowEarlyCallResult
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAllCountInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveConcreteWindowNonzeroInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

abbrev rawLenHeld {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode)
    (fresh : (helperTag s).value<18446744073709551615) :=
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker (expressionTracker s) fresh) (helperTag s)
abbrev rawLenEnded {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode)
    (fresh : (helperTag s).value<18446744073709551615) : MachineHooks.BorrowState :=
  let registered:=rawLenHeld s fresh
  {registered with global:=registered.global.endCall (({} : FrameState).addProtector s.id (helperTag s))}

set_option autoImplicit false in
/-- Explicit sufficient call-time contract for every UInt64 count on a bounded
concrete slice with exposed selected ancestors and mixed writable other leaves.
This contract does not characterize all valid callers. Copy storage and the
correct source initialization interval are conditional on the accepted branch. -/
structure InitialFor (profileMode : ProfileMode) extends toBase : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode where
  statementFuel : limits.validation=validityFuel+1
  budget : Nat
  dispatchFuel : limits.callDispatch=budget+1
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  helperMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (helperTag toBase)
  helperFresh : (helperTag toBase).value<18446744073709551615
  expressionUnheld : tracker.global.protectedTags.contains (held toBase).global.nextPointerTag=false
  helperUnheld : tracker.global.protectedTags.contains (helperTag toBase)=false
  mutableFresh : (rawLenEnded toBase helperFresh).global.nextPointerTag.value<18446744073709551615
  mutableHelperFresh : (ReferenceBorrowDriver.allocatedTracker (rawLenEnded toBase helperFresh) mutableFresh).global.nextPointerTag.value<18446744073709551615
  mutableMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (rawLenEnded toBase helperFresh).global.nextPointerTag
  mutableHelperMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (rawLenEnded toBase helperFresh) mutableFresh).global.nextPointerTag
  mutableUnheld : tracker.global.protectedTags.contains (rawLenEnded toBase helperFresh).global.nextPointerTag=false
  mutableHelperUnheld : tracker.global.protectedTags.contains
    (ReferenceBorrowDriver.allocatedTracker (rawLenEnded toBase helperFresh) mutableFresh).global.nextPointerTag=false
  bufferStorage : (0 : UInt64)<count→count≤len/2→entry.allocation.len=entry.allocation.byteSize.bytes.toNat
  bufferMaskValid : (0 : UInt64)<count→count≤len/2→InitMaskCopy.WellFormed entry.allocation.initializationMask
  bufferMaskLength : (0 : UInt64)<count→count≤len/2→entry.allocation.initializationMask.len=entry.allocation.byteSize
  bufferInitialized : (0 : UInt64)<count→count≤len/2→
    InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  bufferProvenance : (0 : UInt64)<count→count≤len/2→ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  bufferStorageFits : (0 : UInt64)<count→count≤len/2→entry.allocation.len+64<18446744073709551616
  bufferMutable : (0 : UInt64)<count→count≤len/2→entry.allocation.mutability=.Mut
  bufferExtras : (0 : UInt64)<count→count≤len/2→before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==id)=some (id,⟨none,#[]⟩)

/-- Legacy all-allocation profile contract. -/
abbrev Initial := InitialFor .global

def zero {profileMode : ProfileMode} (s : InitialFor profileMode) (zero : s.count=0) : GeneralBorrowPositiveConcreteWindowZero.InitialFor profileMode :=
  {toBase:=s.toBase,zero:=zero,vacantClean:=s.vacantClean}

def nonzero {profileMode : ProfileMode} (s : InitialFor profileMode) (positive : (0 : UInt64)<s.count) : GeneralBorrowPositiveConcreteWindowNonzeroInput.InitialFor profileMode := {
  toBase:=s.toBase,countPositive:=positive,budget:=s.budget,dispatchFuel:=s.dispatchFuel,
  vacantClean:=s.vacantClean,helperMapFresh:=s.helperMapFresh,helperFresh:=s.helperFresh,
  expressionUnheld:=s.expressionUnheld,helperUnheld:=s.helperUnheld }


def accepted {profileMode : ProfileMode} (s : InitialFor profileMode) (positive : (0 : UInt64)<s.count) (within : s.count≤s.len/2) :
    GeneralBorrowPositiveConcreteWindowAcceptedInput.InitialFor profileMode := {
  toInitial:=nonzero s positive,within:=within,
  mutableFresh:=s.mutableFresh,mutableHelperFresh:=s.mutableHelperFresh,
  mutableMapFresh:=s.mutableMapFresh,mutableHelperMapFresh:=s.mutableHelperMapFresh,
  mutableUnheld:=s.mutableUnheld,mutableHelperUnheld:=s.mutableHelperUnheld,
  bufferStorage:=s.bufferStorage positive within,bufferMaskValid:=s.bufferMaskValid positive within,bufferMaskLength:=s.bufferMaskLength positive within,
  bufferInitialized:=s.bufferInitialized positive within,bufferProvenance:=s.bufferProvenance positive within,
  bufferStorageFits:=s.bufferStorageFits positive within,bufferMutable:=s.bufferMutable positive within,bufferExtras:=s.bufferExtras positive within }

def acceptedComplete {profileMode : ProfileMode} (s : InitialFor profileMode) (positive : (0 : UInt64)<s.count) (within : s.count≤s.len/2) :
    GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput.InitialFor profileMode := {
  toAccepted:=accepted s positive within,statementFuel:=s.statementFuel }

def rejected {profileMode : ProfileMode} (s : InitialFor profileMode) (outside : s.count>s.len/2) : GeneralBorrowPositiveConcreteWindowRejected.InitialFor profileMode := {
  toInitial:=nonzero s (by apply UInt64.lt_iff_toNat_lt.mpr;have bound:=UInt64.lt_iff_toNat_lt.mp outside;change 0<s.count.toNat;omega),
  rejected:=outside }
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAllCountInput
