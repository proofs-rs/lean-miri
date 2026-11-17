import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedInput
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedNumerics
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveConcreteWindowAcceptedInput GeneralBorrowPositiveConcreteWindowNonzeroInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual six pointer-tag allocations are strictly ordered in Nat. The
caller supplies only the original allocation high-water conditions. -/
theorem values {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowAcceptedInput.InitialFor profileMode) :
    (held s.toBase).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+2 ∧
    (expressionTracker s.toBase).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+3 ∧
    (mutableTag s.toInitial).value.toNat=s.tracker.global.nextPointerTag.value.toNat+4 ∧
    (ReferenceBorrowDriver.allocatedTracker (lenEnded s.toInitial) s.mutableFresh).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+5 := by
  have one := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
  have two := GenericFunctionEntryNumerics.successor_value (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag s.slotFresh
  have three := GenericFunctionEntryNumerics.successor_value (held s.toBase).global.nextPointerTag s.sharedFresh
  have four := GenericFunctionEntryNumerics.successor_value (expressionTracker s.toBase).global.nextPointerTag s.helperFresh
  have five := GenericFunctionEntryNumerics.successor_value (mutableTag s.toInitial) s.mutableFresh
  change (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+1 at one
  change (held s.toBase).global.nextPointerTag.value.toNat=(GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at two
  change (expressionTracker s.toBase).global.nextPointerTag.value.toNat=(held s.toBase).global.nextPointerTag.value.toNat+1 at three
  change (mutableTag s.toInitial).value.toNat=(expressionTracker s.toBase).global.nextPointerTag.value.toNat+1 at four
  change (ReferenceBorrowDriver.allocatedTracker (lenEnded s.toInitial) s.mutableFresh).global.nextPointerTag.value.toNat=(mutableTag s.toInitial).value.toNat+1 at five
  omega
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedNumerics
