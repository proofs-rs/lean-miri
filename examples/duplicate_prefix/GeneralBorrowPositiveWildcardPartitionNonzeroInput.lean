import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionOriginalInput
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionFunctionRuntime
import duplicate_prefix.GeneralBorrowExposedScopedLenCallReturnReadWriteReady
import duplicate_prefix.GeneralBorrowPositiveWildcardVacantClean
import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafVacantClean
import duplicate_prefix.GenericFunctionEntryNumerics
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionNonzeroInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
noncomputable section
abbrev held (s : GeneralBorrowPositiveWildcardPartitionOriginalInput.Base) :=
  GeneralBorrowPositiveWildcardPartitionFunctionState.held s.tracker s.fresh s.slotFresh
abbrev expressionTracker (s : GeneralBorrowPositiveWildcardPartitionOriginalInput.Base) :=
  ReferenceBorrowDriver.allocatedTracker (held s) s.sharedFresh
abbrev helperTag (s : GeneralBorrowPositiveWildcardPartitionOriginalInput.Base) := (expressionTracker s).global.nextPointerTag
set_option autoImplicit false in
/-- Additional raw initial reserves for the positive-count source prefix.
All data concern the original caller; no constructed resource or success field. -/
structure Initial extends GeneralBorrowPositiveWildcardPartitionOriginalInput.Base where
  countPositive : (0 : UInt64) < count
  budget : Nat
  dispatchFuel : limits.callDispatch=budget+1
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  helperMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (helperTag toBase)
  helperFresh : (helperTag toBase).value < 18446744073709551615
  expressionUnheld : tracker.global.protectedTags.contains (held toBase).global.nextPointerTag=false
  helperUnheld : tracker.global.protectedTags.contains (helperTag toBase)=false
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionNonzeroInput
