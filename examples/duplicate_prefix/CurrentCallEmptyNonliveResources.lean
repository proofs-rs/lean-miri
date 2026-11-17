import duplicate_prefix.CurrentCallEmptyConcreteResources
namespace DuplicatePrefix.CurrentCallEmptyNonliveResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- A real metadata-backed nonlive source registers its fresh protector but
creates no source tree. The existing Bool family is transported on the actual
unchanged heap; no source allocation or source grant is fabricated. -/
theorem registered {before tracker data owner id offset}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (frame : FrameState) (sourceId : AllocId)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (post : Before) (memory : post.memory=before.memory) :
    ∃Q : UniformWindow post
      {tracker with global:=(GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId fresh).1}
      data owner id offset 1 .ret,
      Q.pointer=B.pointer ∧Q.allocation=B.allocation ∧Q.precise=B.precise ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
        (GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId fresh).1 := by
  have present : Present (ActualWorld post) id B.allocation := by simpa only [ActualWorld,memory] using B.present
  let next:={tracker with global:=(GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId fresh).1}
  have issued:=CurrentCallAllocationLicense.spatial B.issued post next B.allocation present rfl rfl rfl rfl
    (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
    B.precise.completion (by intro first second edge;exact edge)
  let Q : UniformWindow post next data owner id offset 1 .ret:={B with
    present:=present,issued:=issued,window:=by
      intro byte inside
      obtain ⟨bound,embedding⟩:=B.window byte inside
      exact ⟨bound,CurrentCallEmptyConcreteResources.registered_embeds B.allocation tracker.global runtime frame sourceId fresh
        B.precise.completion B.pointer.grant byte.2 _ embedding⟩}
  exact ⟨Q,rfl,rfl,rfl,(GeneralBorrowFnEntryRegistrationRuntime.prepare B.allocation.extra tracker.global frame sourceId fresh runtime).2.2.2.1⟩
end
end DuplicatePrefix.CurrentCallEmptyNonliveResources
