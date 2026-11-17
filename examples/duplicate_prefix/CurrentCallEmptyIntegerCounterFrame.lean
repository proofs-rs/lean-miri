import duplicate_prefix.CurrentCallEmptyUnlocatedCopy
namespace DuplicatePrefix.CurrentCallEmptyIntegerCounterFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
/-- The actual empty-integer helper body changes only the allocation counter.
The current Bool family and its current permissions therefore remain exact. -/
theorem window {before tracker data owner id offset}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (post : Before) (next : MachineHooks.BorrowState) (memory : post.memory=before.memory)
    (global : next.global={tracker.global with nextPointerTag:=next.global.nextPointerTag})
    (monotone : tracker.global.nextPointerTag.value.toNat≤next.global.nextPointerTag.value.toNat) :
    ∃ Q : UniformWindow post next data owner id offset 1 .ret,
      Q.pointer=B.pointer ∧Q.allocation=B.allocation ∧Q.precise=B.precise ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra next.global := by
  have present : Present (ActualWorld post) id B.allocation := by simpa only [ActualWorld,memory] using B.present
  have issued:=CurrentCallAllocationLicense.spatial B.issued post next B.allocation present
    (by rw [global];rfl) rfl rfl rfl (by intro position root found;exact found)
    (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
    B.precise.completion (by intro first second edge;exact edge)
  let Q : UniformWindow post next data owner id offset 1 .ret := {
    loan:=B.loan,pointer:=B.pointer,allocation:=B.allocation,precise:=B.precise,
    loanAt:=B.loanAt,pointerAt:=B.pointerAt,pointerId:=B.pointerId,present:=present,preciseAt:=B.preciseAt,
    binding:=B.binding,issued:=issued,parents:=B.parents,window:=by
      intro byte inside
      obtain ⟨bound,embedding⟩:=B.window byte inside
      refine ⟨bound,?_⟩
      rw [global]
      exact embedding }
  refine ⟨Q,rfl,rfl,rfl,?_⟩
  change DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra next.global
  have flags : next.global.protectedTags=tracker.global.protectedTags := by rw [global]
  refine ⟨?_,?_,?_,?_⟩
  · rw [flags];exact runtime.formed
  · rw [flags];exact runtime.coherent
  · exact runtime.possible
  · rw [flags]
    exact GeneralBorrowForestTagHighWaterHistory.weaken _ _ _ _ runtime.below monotone
end
end DuplicatePrefix.CurrentCallEmptyIntegerCounterFrame
