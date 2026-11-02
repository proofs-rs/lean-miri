import duplicate_prefix.S02ConcreteSourceActivity
import duplicate_prefix.GeneralBorrowProtectedChildMetadata

namespace DuplicatePrefix.S02ConcreteSourceHidden
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The actual positive FnEntry child in the typed result tree is present,
tagged, and unexposed, for either allocator append or reuse. -/
theorem exact_source_hidden (tree : BorrowTree) (global : GlobalState)
    (frame : FrameState) (id : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (input : GeneralBorrowRawFnEntry.Input tree global) :
    let resultTree := GeneralBorrowRawFnEntryArgument.finalTree tree
      ⟨global,.FnEntry⟩ input.parentTag input.offset input.len
    ∃ child node,
      resultTree.indexOfTag global.nextPointerTag = some child ∧
      resultTree.nodeAt child = some node ∧ node.tag = global.nextPointerTag ∧ node.isExposed = false := by
  obtain ⟨_allocated,_held,_frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare tree global frame id input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered global frame id input.tagRoom
  let read := tree.performBorrowAccessRange (.concrete input.parentTag)
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read registration.1.protectedTags
    .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ :=
    GeneralBorrowConcreteRowReadRange.access_runtime tree registration.1 registeredRuntime
      input.parentTag input.parent input.selected input.maximum input.tagged
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed
      input.offset input.len registeredPositive input.distinct input.order input.short
      (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent input.parent rfl
  have tagged : read.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping global.nextPointerTag := by
    rw [contract.tags]
    exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by
    rw [contract.nodes]
    exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by
    intro zero
    have positive := input.positive.positive
    rw [zero] at positive
    contradiction
  obtain ⟨child,lookup,⟨node,present,taggedNode,hidden⟩,_attach,_old⟩ :=
    GeneralBorrowProtectedChildMetadata.construct read.tree registration.1 afterRuntime
      input.parentTag global.nextPointerTag input.parent parentNode tagged parentPresent
      freshAfter room input.offset input.len nonzero afterPositive.bounds
  refine ⟨child,node,?_,?_,taggedNode,hidden⟩
  · exact lookup
  · exact present

end
end DuplicatePrefix.S02ConcreteSourceHidden

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceHidden.exact_source_hidden) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete source hidden dependency {dependency}"
