import duplicate_prefix.GeneralBorrowPositiveWildcardFamilyInput
import duplicate_prefix.GeneralBorrowPositiveWildcardAllCountSafety
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardFamilyAllCount
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveWildcardFamilyPhysical
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {capacity : UInt64} {global : GlobalState} {tree : BorrowTree} {location : LocationTree} {roots : List UniIndex}
/-- Generated family and callback-derived vacancy form every raw all-count
borrow premise. The remaining Caller describes physical storage and settings. -/
def input (p : Caller capacity global tree)
    (family : GeneralBorrowExposedUniqueRootFamilySeed.Family capacity global tree location roots)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    @GeneralBorrowPositiveWildcardAllCountInput.Initial (scope roots) := by
  letI : GeneralBorrowExposedKnownRootState.Scope:=scope roots
  let b:=GeneralBorrowPositiveWildcardFamilyInput.base p family
  let t:=tags p
  have unheld (tag : BorTag) : p.tracker.global.protectedTags.contains tag=false := by
    rw [p.trackerGlobal,family.emptyProtections]
    rfl
  exact {
    toBase:=b,statementFuel:=p.statementFuel,budget:=p.budget,dispatchFuel:=p.dispatchFuel,
    vacantClean:=by change GeneralBorrowGcVacantClean.VacantClean p.entry.allocation.extra;simpa only [p.entryTree] using clean,
    helperMapFresh:=GeneralBorrowPositiveWildcardFamilyInput.future_fresh p family _
      (UInt64.le_iff_toNat_le.mpr (by change p.tracker.global.nextPointerTag.value.toNat≤(GeneralBorrowPositiveWildcardFamilyTags.expression p.tracker t.fresh t.slotFresh t.sharedFresh).global.nextPointerTag.value.toNat;have n:=t.helperValue;omega)),
    helperFresh:=t.helperFresh,expressionUnheld:=unheld _,helperUnheld:=unheld _,
    mutableFresh:=t.mutableFresh,mutableHelperFresh:=t.mutableHelperFresh,
    mutableMapFresh:=GeneralBorrowPositiveWildcardFamilyInput.future_fresh p family _
      (UInt64.le_iff_toNat_le.mpr (by change p.tracker.global.nextPointerTag.value.toNat≤(GeneralBorrowPositiveWildcardFamilyTags.ended p.tracker t.fresh t.slotFresh t.sharedFresh t.helperFresh p.id).global.nextPointerTag.value.toNat;have n:=t.mutableValue;omega)),
    mutableHelperMapFresh:=GeneralBorrowPositiveWildcardFamilyInput.future_fresh p family _
      (UInt64.le_iff_toNat_le.mpr (by change p.tracker.global.nextPointerTag.value.toNat≤(ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardFamilyTags.ended p.tracker t.fresh t.slotFresh t.sharedFresh t.helperFresh p.id) t.mutableFresh).global.nextPointerTag.value.toNat;have n:=t.mutableHelperValue;omega)),
    mutableUnheld:=unheld _,mutableHelperUnheld:=unheld _,
    bufferStorage:=p.bufferStorage,bufferMaskValid:=p.bufferMaskValid,bufferMaskLength:=p.bufferMaskLength,
    bufferInitialized:=p.bufferInitialized,bufferProvenance:=p.bufferProvenance,bufferStorageFits:=p.bufferStorageFits,
    bufferMutable:=p.bufferMutable,bufferExtras:=p.bufferExtras }

/-- The generated-row adapter reaches the actual original invocation and
physical terminal return for every count, with finite-prefix NoUB. -/
theorem invoke (p : Caller capacity global tree)
    (family : GeneralBorrowExposedUniqueRootFamilySeed.Family capacity global tree location roots)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    @GeneralBorrowPositiveWildcardAllCountResult.Result (scope roots)
      (GeneralBorrowPositiveWildcardFamilyInput.base p family) := by
  letI : GeneralBorrowExposedKnownRootState.Scope:=scope roots
  exact GeneralBorrowPositiveWildcardAllCountSafety.invoke (input p family clean)
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardFamilyAllCount
