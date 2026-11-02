import duplicate_prefix.GeneralBorrowRawSharedExpression
import duplicate_prefix.GeneralBorrowSharedChildGraph
namespace DuplicatePrefix.GeneralBorrowRawSharedOldGraph
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Every old node retains tag, parent and exposure on the literal actual
shared-expression result. The preliminary parent Read is included; allocator
append/reuse and ancestor SIFA are derived, not supplied as a graph equation. -/
theorem frame (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (input : GeneralBorrowRawShared.Input tree global) :
    let actual := GeneralBorrowRawSharedExpression.child tree global.protectedTags input.parentTag global.nextPointerTag
      input.offset input.len .VisitChildrenOfAccessed
    ∀ query oldNode, tree.nodeAt query = some oldNode →
      ∃ node, actual.tree.nodeAt query = some node ∧ node.tag = oldNode.tag ∧
        node.parent = oldNode.parent ∧ node.isExposed = oldNode.isExposed := by
  obtain ⟨allocated,advancedRuntime,⟨advancedPositive⟩,fresh,unheld⟩ := GeneralBorrowReadTagAllocation.prepare tree global input.tagRoom runtime
    input.parent input.selected input.maximum input.offset input.len input.positive
  let advanced := GeneralBorrowFnEntryRegistration.advanced global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read advanced.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree advanced advancedRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len advancedPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have h:=input.positive.positive;rw [zero] at h;contradiction
  obtain ⟨child,lookup,node,oldNodes⟩ := GeneralBorrowSharedChildGraph.construct accessed.tree advanced afterRuntime
    input.parentTag global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room false
    input.offset input.len nonzero afterPositive.bounds
  dsimp only
  intro query oldNode present
  have readPresent : accessed.tree.nodeAt query = some oldNode := by
    change accessed.tree.nodes.get query = some oldNode
    rw [contract.nodes]
    exact present
  exact oldNodes query oldNode readPresent
end DuplicatePrefix.GeneralBorrowRawSharedOldGraph
