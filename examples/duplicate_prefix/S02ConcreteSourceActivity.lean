import duplicate_prefix.S02ConcreteSourceFormation

namespace DuplicatePrefix.S02ConcreteSourceActivity
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The positive argument constructor's exact typed result carries its
owned-window activity profile. This is the profile needed for the real active
protector release at return, rather than Quiescent. -/
theorem exact_source_activity (tree : BorrowTree) (global : GlobalState)
    (frame : FrameState) (id : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (input : GeneralBorrowRawFnEntry.Input tree global) :
    let resultTree := GeneralBorrowRawFnEntryArgument.finalTree tree
      ⟨global,.FnEntry⟩ input.parentTag input.offset input.len
    ∃ child,
      resultTree.indexOfTag global.nextPointerTag = some child ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin resultTree child .Write
        input.offset (input.offset+input.len) := by
  obtain ⟨output,actual,tag,_globalEq,_frameEq,_read,_child,_afterRuntime,_capacity,_growth,
      child,lookup,_roots,_positive,active⟩ :=
    GeneralBorrowRawFnEntry.invoke_positive tree global frame id runtime input
  have allocated := (GeneralBorrowFnEntryRegistration.prepare tree global frame id input.tagRoom runtime
    input.parent input.selected input.maximum input.offset input.len input.positive).1
  let registered := GeneralBorrowFnEntryRegistration.registered global frame id input.tagRoom
  let read := tree.performBorrowAccessRange (.concrete input.parentTag)
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read registered.1.protectedTags
    .VisitChildrenOfAccessed
  have outputEq : output = ⟨registered.1,registered.2,global.nextPointerTag,read,
      read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
        (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside)
        (.ReservedFrz false) true⟩ := by
    unfold GeneralBorrowForestFnEntry.operation at actual
    rw [allocated] at actual
    simp only [Except.bind,Except.pure] at actual
    exact (Except.ok.inj actual).symm
  have treeEq : output.child.tree = GeneralBorrowRawFnEntryArgument.finalTree tree
      ⟨global,.FnEntry⟩ input.parentTag input.offset input.len := by
    rw [outputEq]
    rfl
  refine ⟨child,?_,?_⟩
  · rw [←treeEq]
    simpa only [tag] using lookup
  · rw [←treeEq]
    exact active

end
end DuplicatePrefix.S02ConcreteSourceActivity

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceActivity.exact_source_activity) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete source activity dependency {dependency}"
