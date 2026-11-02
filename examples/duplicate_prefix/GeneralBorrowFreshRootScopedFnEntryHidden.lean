import duplicate_prefix.GeneralBorrowFreshRootScopedFnEntryResources
import duplicate_prefix.GeneralBorrowProtectedChildMetadata
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedFnEntryHidden
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Hidden-child metadata on the literal typed FnEntry tree follows from the
actual allocator append/reuse constructor; it is not a caller restriction. -/
theorem hidden (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedFnEntry.Input tree tracker.global) :
    let finalTree := GeneralBorrowFreshRootScopedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    ∃ child node, finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      finalTree.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧ node.isExposed = false := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFreshRootScopedRegistration.prepare tree tracker.global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.base.sourcePresent input.parent rfl
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.base.positive;rw [zero] at p;contradiction
  obtain ⟨child,lookup,⟨node,present,sameTag,hidden⟩,attach,old⟩ :=
    GeneralBorrowProtectedChildMetadata.construct accessed.tree registration.1 afterRuntime
      input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room
      input.offset input.len nonzero afterPositive.base.bounds
  exact ⟨child,node,lookup,present,sameTag,hidden⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedFnEntryHidden
