import duplicate_prefix.GeneralBorrowPositiveConcreteWindowInputGeometry
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalInput
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFunctionRuntime
import duplicate_prefix.GeneralBorrowExposedScopedLenCallReturnReadWriteReady
import duplicate_prefix.GeneralBorrowPositiveWildcardVacantClean
import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafVacantClean
import duplicate_prefix.GenericFunctionEntryNumerics
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowNonzeroInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
noncomputable section
abbrev held {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) :=
  GenericFunctionEntryState.held s.tracker s.fresh s.slotFresh
abbrev expressionTracker {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) :=
  ReferenceBorrowDriver.allocatedTracker (held s) s.sharedFresh
abbrev helperTag {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) := (expressionTracker s).global.nextPointerTag
set_option autoImplicit false in
/-- Additional raw initial reserves for the positive-count source prefix.
All data concern the original caller; no constructed resource or success field. -/
structure InitialFor (profileMode : ProfileMode) extends toBase : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode where
  countPositive : (0 : UInt64) < count
  budget : Nat
  dispatchFuel : limits.callDispatch=budget+1
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  helperMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (helperTag toBase)
  helperFresh : (helperTag toBase).value < 18446744073709551615
  expressionUnheld : tracker.global.protectedTags.contains (held toBase).global.nextPointerTag=false
  helperUnheld : tracker.global.protectedTags.contains (helperTag toBase)=false
/-- Legacy global caller contract; window callers use InitialFor .window. -/
abbrev Initial := InitialFor .global
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowNonzeroInput
