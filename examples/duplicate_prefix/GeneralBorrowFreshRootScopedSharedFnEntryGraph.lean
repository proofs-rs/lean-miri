import duplicate_prefix.GeneralBorrowSharedChildGraph
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntryResources
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedFnEntryGraph
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exact parent edges, tags and hidden flags on the literal typed shared
FnEntry tree. They follow from real parent Read, actual arbitrary-slot shared
construction and SIFA, and are never assumed as future initializer facts. -/
theorem graph (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input tree tracker.global) :
    let finalTree := GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    ∃ child, finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      (∃ node, finalTree.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧
        node.parent = some input.parent ∧ node.isExposed = false) ∧
      (∀ query oldNode, tree.nodeAt query = some oldNode →
        ∃ next, finalTree.nodeAt query = some next ∧ next.tag = oldNode.tag ∧
          next.parent = oldNode.parent ∧ next.isExposed = oldNode.isExposed) := by
  obtain ⟨_,_,_,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFreshRootScopedRegistration.read_prepare tree tracker.global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowFreshRootScopedReadRange.access tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.base.sourcePresent
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p:=input.positive.base.positive;rw [zero] at p;contradiction
  obtain ⟨child,lookup,node,old⟩ := GeneralBorrowSharedChildGraph.construct accessed.tree registration.1 afterRuntime
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room true
    input.offset input.len nonzero afterPositive.base.bounds
  refine ⟨child,lookup,node,?_⟩
  intro query oldNode present
  have afterRead : accessed.tree.nodeAt query = some oldNode := by
    change accessed.tree.nodes.get query = some oldNode
    rw [contract.nodes]
    exact present
  exact old query oldNode afterRead
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedFnEntryGraph
