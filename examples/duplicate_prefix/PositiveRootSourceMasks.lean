import duplicate_prefix.PositiveRootInvocationState
import duplicate_prefix.PositiveLenPost
namespace DuplicatePrefix.PositiveRootSourceMasks
open Miri Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem stage2 (tags : Fin 6 → BorTag) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (child : tracker.global.nextPointerTag = tags 1)
    (different : tags 0 ≠ tracker.global.nextPointerTag)
    (different2 : tags 0 ≠ (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag)
    (free : tracker.global.protectedTags.contains (tags 0) = false) :
    ProtectedStages.StageMask tags (PositiveRootInvocationState.held tracker fresh fresh2).global.protectedTags 2 false := by
  intro i inside
  have choices : i = 0 ∨ i = 1 := by
    have val : i.val = 0 ∨ i.val = 1 := by omega
    rcases val with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases choices with h|h
  · subst i
    change _ = false
    exact PositiveRootInvocationState.buffer_root_free tracker fresh fresh2 (tags 0) different different2 free
  · subst i
    change _ = true
    rw [←child]
    exact PositiveRootInvocationState.buffer_child_held tracker fresh fresh2

theorem stage3 (tags : Fin 6 → BorTag) (tracker : MachineHooks.BorrowState)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 2 false)
    (unprotected : tracker.global.protectedTags.contains (tags 2) = false) :
    ProtectedStages.StageMask tags tracker.global.protectedTags 3 false := by
  intro i inside
  by_cases new : i = 2
  · subst i
    exact unprotected
  · exact mask i (by have not2 : i.val ≠ 2 := fun h => new (Fin.ext h);omega)
end DuplicatePrefix.PositiveRootSourceMasks
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.PositiveRootSourceMasks.stage2,``DuplicatePrefix.PositiveRootSourceMasks.stage3] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved positive root initial stage mask dependency {dependency}"
