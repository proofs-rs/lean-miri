import duplicate_prefix.S02SeparateDestinationSourceReady
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime

namespace DuplicatePrefix.S02SeparateDestinationSourceRuntime
open Miri Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The second (destination) protector advances the global counter and inserts
its fresh tag without changing RuntimeFacts of a distinct source tree. -/
theorem runtime_after_protect
    (current : Before) (place : MPlaceTy Provenance)
    (destination : DuplicatePrefixReturnPlaceInput.Input current place)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (fresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (sourceId : AllocId) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (different : destination.id ≠ sourceId)
    (sourceLive : current.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra destination.tracker.global) :
    let after := S04ProtectUninit.finished current place destination frames frame borrowFrame fresh tree updated
    ∃ tracker : MachineHooks.BorrowState,
      after.machine.borrowTracker = some tracker ∧
      after.machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global := by
  let afterTracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker fresh)
    destination.tracker.global.nextPointerTag
  have trackerEq : (S04ProtectUninit.finished current place destination frames frame borrowFrame fresh tree updated).machine.borrowTracker =
      some afterTracker := rfl
  have liveEq := S02SeparateDestinationSourceLive.source_live_after_protect current place destination
    frames frame borrowFrame fresh tree updated sourceId different
  obtain ⟨_,_,_,afterRuntime,_,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    sourceEntry.allocation.extra destination.tracker.global borrowFrame destination.id fresh runtime
  refine ⟨afterTracker,trackerEq,liveEq.trans sourceLive,?_⟩
  simpa only [afterTracker,TypedBorrowSteps.registeredTracker,TypedBorrowSteps.registeredGlobal,
    ReferenceBorrowDriver.allocatedTracker,GeneralBorrowFnEntryRegistration.registered,
    GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector]
    using afterRuntime

end
end DuplicatePrefix.S02SeparateDestinationSourceRuntime

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourceRuntime.runtime_after_protect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination source-runtime dependency {dependency}"
