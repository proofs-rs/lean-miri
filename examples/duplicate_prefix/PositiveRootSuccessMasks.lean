import duplicate_prefix.PositiveLenPost
namespace DuplicatePrefix.PositiveRootSuccessMasks
open Miri Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxHeartbeats 4000000

theorem stage5 (tags : Fin 6→BorTag) (protections : ProtectedTags)
    (before : ProtectedStages.StageMask tags protections 4 false)
    (free4 : protections.contains (tags 4)=false) : ProtectedStages.StageMask tags protections 5 false := by
  intro i inside
  by_cases last : i=4
  · subst i
    exact free4
  · exact before i (by have ne4 : i.val≠4 := fun h=>last (Fin.ext h);omega)

theorem other_after_len (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) (id : AllocId) (tag : BorTag)
    (different : tag≠tracker.global.nextPointerTag) :
    (PositiveLenPost.trackerAfter tracker fresh id).global.protectedTags.contains tag=tracker.global.protectedTags.contains tag := by
  unfold PositiveLenPost.trackerAfter
  rw [StackPopRelease.end_call_contains]
  have absent : tag∉(({}:FrameState).addProtector id tracker.global.nextPointerTag).protectedTags.toList.map Prod.snd := by
    simp [FrameState.addProtector,different]
  rw [if_neg absent]
  change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains tag=_
  exact ProtectorInsertion.contains_other _ _ _ _ different

theorem after_len_stage5 (tags : Fin 6→BorTag) (distinct : Function.Injective tags)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615) (id : AllocId)
    (next : tracker.global.nextPointerTag=tags 3)
    (before : ProtectedStages.StageMask tags tracker.global.protectedTags 3 false)
    (free4 : tracker.global.protectedTags.contains (tags 4)=false) :
    ProtectedStages.StageMask tags (PositiveLenPost.trackerAfter tracker fresh id).global.protectedTags 5 false := by
  apply stage5 tags _ (PositiveLenPost.mask_after tags distinct tracker fresh id next before)
  have different : tags 4≠tracker.global.nextPointerTag := by
    rw [next]
    intro same
    have equal := distinct same
    have impossible : (4:Fin 6)≠3 := by decide
    exact impossible equal
  rw [other_after_len tracker fresh id (tags 4) different]
  exact free4

#print axioms after_len_stage5
end DuplicatePrefix.PositiveRootSuccessMasks
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootSuccessMasks.after_len_stage5) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved positive root success masks dependency {dependency}"
