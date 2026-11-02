import duplicate_prefix.GeneralBorrowRawDefaultExpression
import duplicate_prefix.GeneralBorrowDefaultChildOrder
namespace DuplicatePrefix.GeneralBorrowRawDefaultOrder
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Existing graph order survives the literal Default allocation, parent Read
and unprotected reservation construction, for actual append or reuse. -/
theorem order (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (initialOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree) :
    let finalTree := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
  obtain ⟨allocated,registeredRuntime,⟨registeredPositive⟩,fresh,unheld⟩ :=
    GeneralBorrowDefaultTagAllocation.prepare tree tracker.global input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration registeredRuntime
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
  have nodeOld : tree.nodeAt input.parent = some parentNode := by
    change tree.nodes.get input.parent = some parentNode
    change accessed.tree.nodes.get input.parent = some parentNode at parentPresent
    rw [contract.nodes] at parentPresent
    exact parentPresent
  have tagBelow := GeneralBorrowForestTagHighWater.mapped tree tracker.global.protectedTags tracker.global.nextPointerTag
    parentNode.tag runtime.below input.parent (runtime.formed.allocator.nodeTags input.parent parentNode nodeOld)
  have freshOrder : parentNode.tag.value ≤ tracker.global.nextPointerTag.value := by
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt tagBelow)
  have readOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder accessed.tree := by
    unfold GeneralBorrowWildcardParentTagOrder.ParentTagOrder
    rw [contract.nodes]
    exact initialOrder
  exact GeneralBorrowDefaultChildOrder.construct accessed.tree registration afterRuntime readOrder
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room freshOrder
    input.offset input.len nonzero afterPositive.bounds
end DuplicatePrefix.GeneralBorrowRawDefaultOrder
