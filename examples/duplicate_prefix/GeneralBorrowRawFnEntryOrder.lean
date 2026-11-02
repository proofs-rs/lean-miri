import duplicate_prefix.GeneralBorrowRawFnEntryResources
import duplicate_prefix.GeneralBorrowProtectedChildOrder
namespace DuplicatePrefix.GeneralBorrowRawFnEntryOrder
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Hidden-child metadata on the literal typed FnEntry tree follows from the
actual allocator append/reuse constructor; it is not a caller restriction. -/
theorem order (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (initialOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
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
  exact GeneralBorrowProtectedChildOrder.construct accessed.tree registration.1 afterRuntime readOrder
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room freshOrder
    input.offset input.len nonzero afterPositive.bounds
/-- A single real child allocation consumes at most one node of explicit
initial headroom; conditional root order is carried from the original packet. -/
theorem conditional (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (headroom : tree.nodes.size+1 < 65536) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    (∀ valid : 0 < finalTree.roots.size, input.selected ≠ finalTree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree) ∧ finalTree.nodes.size < 65536 := by
  obtain ⟨_,_,growth,roots,_,_,_,rest⟩ := GeneralBorrowRawFnEntryResources.resources tree tracker frame allocation runtime input
  constructor
  · intro valid different
    have oldValid : 0 < tree.roots.size := by simpa only [roots] using valid
    have oldDifferent : input.selected ≠ tree.roots[0] := by simpa only [roots] using different
    exact order tree tracker frame allocation runtime input (input.order oldValid oldDifferent)
  · omega
end DuplicatePrefix.GeneralBorrowRawFnEntryOrder
