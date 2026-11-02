import duplicate_prefix.GeneralBorrowFreshProtectedSlotOther
import duplicate_prefix.GeneralBorrowRawFnEntryArgument

namespace DuplicatePrefix.S02FnEntryOldOther
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Every old node other than the actual reborrow parent retains its children
as well as tag, parent and hidden flag on the exact typed FnEntry tree. -/
theorem preserved (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (query : UniIndex) (oldNode : TreeNode) (present : tree.nodeAt query = some oldNode) (different : query ≠ input.parent) :
    ∃ next, (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len).nodeAt query = some next ∧
      next.tag = oldNode.tag ∧ next.parent = oldNode.parent ∧ next.children = oldNode.children ∧ next.isExposed = oldNode.isExposed := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare tree tracker.global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent input.parent rfl
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  let depth := GeneralBorrowStructuralHistoryMutable.depth accessed.tree afterRuntime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot accessed.tree afterRuntime.formed.toState input.parent parentNode parentPresent room
  have oldPresent : accessed.tree.nodeAt query = some oldNode := by
    change accessed.tree.nodes.get query = some oldNode
    rw [contract.nodes]
    exact present
  obtain ⟨next,found,tag,parent,children,_permission,hidden⟩ := GeneralBorrowFreshProtectedSlotOther.of_slot accessed.tree depth
    afterRuntime.formed.children afterRuntime.formed.covered input.parentTag tracker.global.nextPointerTag input.parent parentNode
    tagged parentPresent freshAfter slot input.offset input.len nonzero afterRuntime.formed.well afterPositive.bounds
    query oldNode oldPresent different
  exact ⟨next,found,tag,parent,children,hidden⟩

end DuplicatePrefix.S02FnEntryOldOther

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02FnEntryOldOther.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
