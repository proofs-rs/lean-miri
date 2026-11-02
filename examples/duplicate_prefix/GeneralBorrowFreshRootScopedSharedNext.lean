import duplicate_prefix.GeneralBorrowFreshRootScopedSharedExpression
import duplicate_prefix.GeneralBorrowFreshRootScopedReferenceNextInput
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedNext
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- Initial finite allocator/tag headroom suffices to form the next helper's
raw input on the actual shared-expression tree. No next permission is assumed. -/
theorem next_input (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedShared.Input tree tracker.global)
    (shortRoom : tree.nodes.size+1 < 65536) (nodeRoom : tree.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615) :
    let finalTree := (GeneralBorrowFreshRootScopedSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag
      input.offset input.len .VisitChildrenOfAccessed).tree
    let next := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    DuplicatePrefixBorrowContract.RuntimeFacts finalTree next.global ∧
    finalTree.locations.size = tree.locations.size ∧
    ∃ raw : GeneralBorrowFreshRootScopedSharedFnEntry.Input finalTree next.global,
      raw.parentTag = tracker.global.nextPointerTag ∧ raw.selected = input.selected ∧ raw.maximum = input.maximum ∧
      raw.offset = input.offset ∧ raw.len = input.len := by
  obtain ⟨output,actual,tagEq,globalEq,protections,readDone,childDone,afterRuntime,capacity,growth,child,lookup,roots,⟨positive⟩⟩ :=
    GeneralBorrowFreshRootScopedShared.invoke_positive tree tracker.global runtime input
  have outputEq : output = (⟨GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom,tracker.global.nextPointerTag,
    tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed,
    (GeneralBorrowFreshRootScopedSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed)⟩ : GeneralBorrowRawShared.Output) := by
    have equation := actual
    simp only [GeneralBorrowRawShared.operation,TypedRetagEmpty.allocate_tag tracker.global input.tagRoom,Except.bind,Except.pure,bind,pure] at equation
    exact (Except.ok.inj equation).symm
  subst output
  let finalTree := (GeneralBorrowFreshRootScopedSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag
      input.offset input.len .VisitChildrenOfAccessed).tree
  have rootsExact : finalTree.roots = tree.roots := roots
  let next := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag input.tagRoom
  have nextTagRoom : next.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag input.tagRoom).value.toNat < _
    rw [successor]
    exact tagRoom
  let raw : GeneralBorrowFreshRootScopedSharedFnEntry.Input finalTree next.global := {
    parentTag := tracker.global.nextPointerTag,parent := child,selected := input.selected,maximum := input.maximum,
    offset := input.offset,len := input.len,tagged := lookup,positive := positive,
    distinct := by rw [rootsExact];exact input.distinct,
    short := Nat.lt_of_le_of_lt growth shortRoom,
    nodeRoom := by have h : finalTree.nodes.size ≤ tree.nodes.size+1 := growth;omega,
    tagRoom := nextTagRoom}
  exact ⟨afterRuntime,capacity,raw,rfl,rfl,rfl,rfl,rfl⟩
end
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedNext
