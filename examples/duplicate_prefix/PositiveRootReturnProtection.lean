import duplicate_prefix.PositiveRootSuccessMasks
import duplicate_prefix.AsMutRootOutput

namespace DuplicatePrefix.PositiveRootReturnProtection
open Miri Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

set_option autoImplicit false in
/-- A helper's temporary strong protector is removed on return, so a tag
that was free before that helper is still free afterwards, including when it
coincides with the helper's temporary tag. -/
theorem after_len_free (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (target : BorTag)
    (free : tracker.global.protectedTags.contains target = false) :
    (PositiveLenPost.trackerAfter tracker fresh id).global.protectedTags.contains target = false := by
  by_cases same : target = tracker.global.nextPointerTag
  · subst target
    unfold PositiveLenPost.trackerAfter
    rw [StackPopRelease.end_call_contains]
    simp [FrameState.addProtector]
  · rw [PositiveRootSuccessMasks.other_after_len tracker fresh id target same]
    exact free

set_option autoImplicit false in
theorem two_helpers_free (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId)
    (fresh2 : (PositiveLenPost.trackerAfter tracker fresh id).global.nextPointerTag.value < 18446744073709551615)
    (fresh3 : (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter tracker fresh id) fresh2).global.nextPointerTag.value < 18446744073709551615)
    (target : BorTag) (free : tracker.global.protectedTags.contains target = false) :
    (AsMutRootOutput.held (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter tracker fresh id) fresh2)
      fresh3 id).global.protectedTags.contains target = false := by
  exact after_len_free _ fresh3 id target (after_len_free tracker fresh id target free)

set_option autoImplicit false in
/-- Existing caller protectors survive both helper calls when their tags are
not either temporary tag. Allocation of an intervening unprotected tag does
not alter the protection map. -/
theorem two_helpers_other (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId)
    (fresh2 : (PositiveLenPost.trackerAfter tracker fresh id).global.nextPointerTag.value < 18446744073709551615)
    (fresh3 : (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter tracker fresh id) fresh2).global.nextPointerTag.value < 18446744073709551615)
    (target : BorTag) (different : target ≠ tracker.global.nextPointerTag)
    (different2 : target ≠ (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter tracker fresh id) fresh2).global.nextPointerTag) :
    (AsMutRootOutput.held (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter tracker fresh id) fresh2)
      fresh3 id).global.protectedTags.contains target = tracker.global.protectedTags.contains target := by
  exact (PositiveRootSuccessMasks.other_after_len _ fresh3 id target different2).trans
    (PositiveRootSuccessMasks.other_after_len tracker fresh id target different)

end DuplicatePrefix.PositiveRootReturnProtection
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.PositiveRootReturnProtection.after_len_free,
      ``DuplicatePrefix.PositiveRootReturnProtection.two_helpers_free,
      ``DuplicatePrefix.PositiveRootReturnProtection.two_helpers_other] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved caller protection preservation dependency {dependency}"
