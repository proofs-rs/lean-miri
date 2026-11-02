import duplicate_prefix.S02ConcreteSourceHidden
import duplicate_prefix.GeneralBorrowRawFnEntryOrder

namespace DuplicatePrefix.S02ConcreteSourceReleasePacket
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Exact typed FnEntry source tree packet needed for active source-protector
release: its child may have accessed bytes and is not Quiescent. -/
theorem release_ready (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (frame : FrameState) (id : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (headroom : tree.nodes.size+1 < 65536) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let fullGlobal := TypedBorrowSteps.registeredGlobal
      (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
    ∃ child node,
      finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      finalTree.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧
      node.isExposed = false ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree fullGlobal ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree fullGlobal.protectedTags
        (some child) (some input.selected) input.maximum input.offset input.len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree child .Write
        input.offset (input.offset+input.len) ∧
      finalTree.roots.toList.Nodup ∧
      (∀ valid : 0 < finalTree.roots.size, input.selected ≠ finalTree.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree) ∧
      finalTree.nodes.size < 65536 := by
  obtain ⟨afterRuntime,_capacity,_growth,roots,_held,_frame,_fresh,child,lookup,⟨positive⟩,active⟩ :=
    GeneralBorrowRawFnEntryResources.resources tree tracker frame id runtime input
  obtain ⟨hiddenChild,node,hiddenLookup,present,tag,hidden⟩ :=
    S02ConcreteSourceHidden.exact_source_hidden tree tracker.global frame id runtime input
  have childEq : hiddenChild = child := Option.some.inj (hiddenLookup.symm.trans lookup)
  subst hiddenChild
  obtain ⟨order,short⟩ := GeneralBorrowRawFnEntryOrder.conditional tree tracker frame id runtime input headroom
  refine ⟨child,node,lookup,present,tag,hidden,afterRuntime,⟨positive⟩,active,?_,order,short⟩
  rw [roots]
  exact input.distinct

end
end DuplicatePrefix.S02ConcreteSourceReleasePacket

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceReleasePacket.release_ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete source release packet dependency {dependency}"
