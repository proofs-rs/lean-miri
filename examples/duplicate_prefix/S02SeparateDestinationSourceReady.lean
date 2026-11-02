import duplicate_prefix.S02SeparateDestinationSourcePositive
import duplicate_prefix.GeneralBorrowForestTagHighWaterHistory

namespace DuplicatePrefix.S02SeparateDestinationSourceReady
open Miri Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Current source runtime facts supply destination-tag freshness, so a
distinct destination's exact retag/uninit preserves the source Positive
capability without a separate freshness assumption. -/
theorem source_positive_after_protect
    (current : Before) (place : MPlaceTy Provenance)
    (destination : DuplicatePrefixReturnPlaceInput.Input current place)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (fresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (sourceId : AllocId) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (different : destination.id ≠ sourceId)
    (sourceLive : current.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra destination.tracker.global)
    (source selected : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
      destination.tracker.global.protectedTags source selected maximum offset len) :
    let after := S04ProtectUninit.finished current place destination frames frame borrowFrame fresh tree updated
    ∃ tracker : MachineHooks.BorrowState,
      after.machine.borrowTracker = some tracker ∧
      after.machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
        tracker.global.protectedTags source selected maximum offset len) := by
  have complete := GeneralBorrowForestTagHighWater.complete sourceEntry.allocation.extra _ _
    runtime.below runtime.formed.allocator.nodeTags
  have freshTag := (GenericFunctionTagFormation.fresh_above sourceEntry.allocation.extra
    destination.tracker.global.protectedTags destination.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag complete (Nat.le_refl _)).2.1
  exact S02SeparateDestinationSourcePositive.source_positive_after_protect current place destination
    frames frame borrowFrame fresh tree updated sourceId sourceEntry different sourceLive freshTag
    source selected maximum offset len positive

end
end DuplicatePrefix.S02SeparateDestinationSourceReady

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourceReady.source_positive_after_protect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination source-ready dependency {dependency}"
