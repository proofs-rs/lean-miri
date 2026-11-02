import duplicate_prefix.S02SeparateDestinationSourceLive
import duplicate_prefix.GeneralBorrowFreshRegistration

namespace DuplicatePrefix.S02SeparateDestinationSourcePositive
open Miri Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The exact distinct-destination protect+uninit operation preserves a
source tree's full Positive read authorization. This operational transport
expects the source capability and fresh-tag fact at the pre-protect state;
forming those facts from the initial call contract is separate. -/
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
    (freshTag : GeneralBorrowProtector.Fresh sourceEntry.allocation.extra
      destination.tracker.global.nextPointerTag)
    (source selected : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
      destination.tracker.global.protectedTags source selected maximum offset len) :
    let after := S04ProtectUninit.finished current place destination frames frame borrowFrame fresh tree updated
    ∃ tracker : MachineHooks.BorrowState,
      after.machine.borrowTracker = some tracker ∧
      after.machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
        tracker.global.protectedTags source selected maximum offset len) := by
  let afterTracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker fresh)
    destination.tracker.global.nextPointerTag
  have trackerEq : (S04ProtectUninit.finished current place destination frames frame borrowFrame fresh tree updated).machine.borrowTracker =
      some afterTracker := rfl
  have liveEq := S02SeparateDestinationSourceLive.source_live_after_protect current place destination
    frames frame borrowFrame fresh tree updated sourceId different
  obtain ⟨afterPositive⟩ := GeneralBorrowFreshRegistration.positive sourceEntry.allocation.extra
    destination.tracker.global.protectedTags destination.tracker.global.nextPointerTag
    .StrongProtector freshTag source selected maximum offset len positive
  refine ⟨afterTracker,trackerEq,liveEq.trans sourceLive,?_⟩
  exact ⟨by simpa only [afterTracker,TypedBorrowSteps.registeredTracker,
    TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedTracker] using afterPositive⟩

end
end DuplicatePrefix.S02SeparateDestinationSourcePositive

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourcePositive.source_positive_after_protect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination source-positive dependency {dependency}"
