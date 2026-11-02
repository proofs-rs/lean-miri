import duplicate_prefix.GeneralBorrowRawFnEntryResources
import duplicate_prefix.GeneralBorrowFreshChildEdges
namespace DuplicatePrefix.GeneralBorrowRawFnEntryEdges
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Hidden-child metadata on the literal typed FnEntry tree follows from the
actual allocator append/reuse constructor; it is not a caller restriction. -/
theorem edges (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
 :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    (∃ child node, finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      finalTree.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧ node.parent = some input.parent) ∧
    (∀ query old, tree.nodeAt query = some old → ∃ node, finalTree.nodeAt query = some node ∧
      node.tag = old.tag ∧ node.parent = old.parent) := by
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
  obtain ⟨newEdge,oldFields⟩ := GeneralBorrowFreshChildEdges.protected_child accessed.tree registration.1 afterRuntime
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room
    input.offset input.len nonzero afterPositive.bounds
  refine ⟨newEdge,?_⟩
  intro query old oldPresent
  apply oldFields query old
  change accessed.tree.nodes.get query = some old
  rw [contract.nodes]
  exact oldPresent
end DuplicatePrefix.GeneralBorrowRawFnEntryEdges
