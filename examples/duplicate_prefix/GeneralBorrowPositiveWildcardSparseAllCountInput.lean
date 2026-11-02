import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAcceptedInput
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseZeroSafety
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseRejectedSafety
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAllCountInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveWildcardSparseNonzeroInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

abbrev rawLenHeld (s : GeneralBorrowPositiveWildcardSparseOriginalInput.Base)
    (fresh : (helperTag s).value<18446744073709551615) :=
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker (expressionTracker s) fresh) (helperTag s)
abbrev rawLenEnded (s : GeneralBorrowPositiveWildcardSparseOriginalInput.Base)
    (fresh : (helperTag s).value<18446744073709551615) : MachineHooks.BorrowState :=
  let registered:=rawLenHeld s fresh
  {registered with global:=registered.global.endCall (({} : FrameState).addProtector s.id (helperTag s))}

set_option autoImplicit false in
/-- One raw original caller for every UInt64 count in the exact-base,
positive-length sparse/mixed exposed-leaf wildcard family. The original
sourceRaw permissions may be effective lazy defaults; no exact-Unique row or
post-operation certificate is a field. Initial cleanliness and tag reserves
are common; copy storage and initialization are required only when the count
is positive and accepted. Compiler/physical/settings conditions remain explicit. -/
structure Initial extends GeneralBorrowPositiveWildcardSparseOriginalInput.Base where
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
    InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes 0) (Size.ofBytes count)
  bufferProvenance : (0 : UInt64)<count→count≤len/2→ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  bufferStorageFits : (0 : UInt64)<count→count≤len/2→entry.allocation.len+64<18446744073709551616
  bufferMutable : (0 : UInt64)<count→count≤len/2→entry.allocation.mutability=.Mut
  bufferExtras : (0 : UInt64)<count→count≤len/2→before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==id)=some (id,⟨none,#[]⟩)

def zero (s : Initial) (zero : s.count=0) : GeneralBorrowPositiveWildcardSparseZero.Initial :=
  {toBase:=s.toBase,zero:=zero}

def nonzero (s : Initial) (positive : (0 : UInt64)<s.count) : GeneralBorrowPositiveWildcardSparseNonzeroInput.Initial := {
  toBase:=s.toBase,countPositive:=positive,budget:=s.budget,dispatchFuel:=s.dispatchFuel,
  vacantClean:=s.vacantClean,helperMapFresh:=s.helperMapFresh,helperFresh:=s.helperFresh,
  expressionUnheld:=s.expressionUnheld,helperUnheld:=s.helperUnheld }

def accepted (s : Initial) (positive : (0 : UInt64)<s.count) (within : s.count≤s.len/2) :
    GeneralBorrowPositiveWildcardSparseAcceptedInput.Initial := {
  toInitial:=nonzero s positive,within:=within,
  mutableFresh:=s.mutableFresh,mutableHelperFresh:=s.mutableHelperFresh,
  mutableMapFresh:=s.mutableMapFresh,mutableHelperMapFresh:=s.mutableHelperMapFresh,
  mutableUnheld:=s.mutableUnheld,mutableHelperUnheld:=s.mutableHelperUnheld,
  bufferStorage:=s.bufferStorage positive within,bufferMaskValid:=s.bufferMaskValid positive within,bufferMaskLength:=s.bufferMaskLength positive within,
  bufferInitialized:=s.bufferInitialized positive within,bufferProvenance:=s.bufferProvenance positive within,
  bufferStorageFits:=s.bufferStorageFits positive within,bufferMutable:=s.bufferMutable positive within,bufferExtras:=s.bufferExtras positive within }

def rejected (s : Initial) (outside : s.count>s.len/2) : GeneralBorrowPositiveWildcardSparseRejected.Initial := {
  toInitial:=nonzero s (by apply UInt64.lt_iff_toNat_lt.mpr;have bound:=UInt64.lt_iff_toNat_lt.mp outside;change 0<s.count.toNat;omega),
  rejected:=outside }
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAllCountInput
