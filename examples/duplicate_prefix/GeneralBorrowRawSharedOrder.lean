import duplicate_prefix.GeneralBorrowRawSharedResources
import duplicate_prefix.GeneralBorrowSharedChildParentTagOrder
namespace DuplicatePrefix.GeneralBorrowRawSharedOrder
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Hidden-child metadata on the literal typed FnEntry tree follows from the
actual allocator append/reuse constructor; it is not a caller restriction. -/
theorem order (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global) :
    let finalTree := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    ∀ valid : 0 < finalTree.roots.size, input.selected ≠ finalTree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
  dsimp only
  intro valid different
  obtain ⟨_,_,_,_,roots,_,_⟩ := GeneralBorrowRawSharedResources.resources tree tracker.global runtime input
  have rootsExact : (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree.roots = tree.roots := roots
  have oldOrder := input.order (by simpa only [rootsExact] using valid) (by simpa only [rootsExact] using different)
  obtain ⟨allocated,registeredRuntime,⟨registeredPositive⟩,fresh,unheld⟩ :=
    GeneralBorrowReadTagAllocation.prepare tree tracker.global input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree registration registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  have accessedNodes : accessed.tree.nodes = tree.nodes := contract.nodes
  have accessedOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder accessed.tree := by
    simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,accessedNodes] using oldOrder
  have originalParent : tree.nodeAt input.parent = some parentNode := by
    change tree.nodes.get input.parent = some parentNode
    change accessed.tree.nodes.get input.parent = some parentNode at parentPresent
    simpa only [accessedNodes] using parentPresent
  have mapped := runtime.formed.allocator.nodeTags input.parent parentNode originalParent
  have below := GeneralBorrowForestTagHighWater.mapped tree tracker.global.protectedTags tracker.global.nextPointerTag parentNode.tag
    runtime.below input.parent mapped
  have parentOrder : parentNode.tag.value ≤ tracker.global.nextPointerTag.value := UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt below)
  exact GeneralBorrowSharedChildParentTagOrder.construct accessed.tree registration afterRuntime
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room
    false input.offset input.len nonzero afterPositive.bounds accessedOrder parentOrder
end DuplicatePrefix.GeneralBorrowRawSharedOrder
