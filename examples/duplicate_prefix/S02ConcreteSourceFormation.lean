import duplicate_prefix.S02SeparateDestinationSourceReady
import duplicate_prefix.GeneralBorrowRawFnEntry
import duplicate_prefix.GeneralBorrowRawFnEntryArgument

namespace DuplicatePrefix.S02ConcreteSourceFormation
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The raw FnEntry output's positive source tree is the exact tree installed
in the typed MIR argument result, with its exact next global tracker. -/
theorem exact_source_tree (tree : BorrowTree) (global : GlobalState)
    (frame : FrameState) (id : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (input : GeneralBorrowRawFnEntry.Input tree global) :
    let resultTree := GeneralBorrowRawFnEntryArgument.finalTree tree
      ⟨global,.FnEntry⟩ input.parentTag input.offset input.len
    ∃ child,
      DuplicatePrefixBorrowContract.RuntimeFacts resultTree
        (TypedRetagGeneric.protectedGlobal global input.tagRoom) ∧
      resultTree.indexOfTag global.nextPointerTag = some child ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive resultTree
        (TypedRetagGeneric.protectedGlobal global input.tagRoom).protectedTags
        (some child) (some input.selected) input.maximum input.offset input.len) := by
  obtain ⟨output,actual,tag,globalEq,_frameEq,_read,_child,afterRuntime,_capacity,_growth,
      child,lookup,_roots,positive,_active⟩ :=
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
  have globalExact : output.global = TypedRetagGeneric.protectedGlobal global input.tagRoom := by
    rw [globalEq]
    rfl
  refine ⟨child,?_,?_,?_⟩
  · rw [←treeEq,←globalExact]
    exact afterRuntime
  · rw [←treeEq]
    simpa only [tag] using lookup
  · rw [←treeEq,←globalExact]
    simpa only [tag] using positive

end
end DuplicatePrefix.S02ConcreteSourceFormation

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceFormation.exact_source_tree) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete source formation dependency {dependency}"
