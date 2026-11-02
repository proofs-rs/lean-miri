import duplicate_prefix.GeneralBorrowRawSharedOrder
namespace DuplicatePrefix.GeneralBorrowRawSharedNext
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- Initial finite allocator/tag headroom suffices to form the next helper's
raw input on the actual shared-expression tree. No next permission is assumed. -/
theorem next_input (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global)
    (shortRoom : tree.nodes.size+1 < 65536) (nodeRoom : tree.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615) :
    let finalTree := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag
      input.offset input.len .VisitChildrenOfAccessed).tree
    let next := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    DuplicatePrefixBorrowContract.RuntimeFacts finalTree next.global ∧
    finalTree.locations.size = tree.locations.size ∧
    ∃ raw : GeneralBorrowRawSharedFnEntry.Input finalTree next.global,
      raw.parentTag = tracker.global.nextPointerTag ∧ raw.selected = input.selected ∧ raw.maximum = input.maximum ∧
      raw.offset = input.offset ∧ raw.len = input.len := by
  obtain ⟨readDone,childDone,capacity,growth,roots,afterRuntime,child,lookup,⟨positive⟩⟩ :=
    GeneralBorrowRawSharedResources.resources tree tracker.global runtime input
  let finalTree := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag
      input.offset input.len .VisitChildrenOfAccessed).tree
  have rootsExact : finalTree.roots = tree.roots := roots
  let next := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag input.tagRoom
  have nextTagRoom : next.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag input.tagRoom).value.toNat < _
    rw [successor]
    exact tagRoom
  let raw : GeneralBorrowRawSharedFnEntry.Input finalTree next.global := {
    parentTag := tracker.global.nextPointerTag,parent := child,selected := input.selected,maximum := input.maximum,
    offset := input.offset,len := input.len,tagged := lookup,positive := positive,
    distinct := by rw [rootsExact];exact input.distinct,
    order := GeneralBorrowRawSharedOrder.order tree tracker runtime input,
    short := Nat.lt_of_le_of_lt growth shortRoom,
    nodeRoom := by have h : finalTree.nodes.size ≤ tree.nodes.size+1 := growth;omega,
    tagRoom := nextTagRoom}
  exact ⟨afterRuntime,capacity,raw,rfl,rfl,rfl,rfl,rfl⟩
end
end DuplicatePrefix.GeneralBorrowRawSharedNext
