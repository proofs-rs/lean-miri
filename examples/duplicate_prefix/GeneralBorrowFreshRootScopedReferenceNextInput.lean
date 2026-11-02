import duplicate_prefix.GeneralBorrowFreshRootScopedReferences
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedReferenceNextInput
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- The real Shared constructor forms the next helper input internally.
Only initial numerical headroom is added; no future Input or tag ordering. -/
theorem shared (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : GeneralBorrowFreshRootScopedShared.Input tree global)
    (nodeHeadroom : tree.nodes.size+1 < 65536)
    (tagHeadroom : global.nextPointerTag.value.toNat+1 < 18446744073709551615) :
    ∃ output,GeneralBorrowRawShared.operation tree global input.parentTag input.offset input.len .VisitChildrenOfAccessed = .ok output ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ next : GeneralBorrowFreshRootScopedSharedFnEntry.Input output.child.tree output.global,
        next.parentTag = output.tag ∧ next.selected = input.selected ∧ next.maximum = input.maximum ∧
        next.offset = input.offset ∧ next.len = input.len := by
  obtain ⟨output,run,tagEq,globalEq,protections,readDone,childDone,afterRuntime,capacity,growth,child,lookup,roots,⟨positive⟩⟩ :=
    GeneralBorrowFreshRootScopedShared.invoke_positive tree global runtime input
  have nextShort : output.child.tree.nodes.size < 65536 := by omega
  have nextRoom : output.global.nextPointerTag.value < 18446744073709551615 := by
    rw [globalEq]
    change (TypedRetagEmpty.successorTag global.nextPointerTag input.tagRoom).value < 18446744073709551615
    apply UInt64.lt_iff_toNat_lt.mpr
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag input.tagRoom
    change (TypedRetagEmpty.successorTag global.nextPointerTag input.tagRoom).value.toNat < 18446744073709551615
    omega
  let next : GeneralBorrowFreshRootScopedSharedFnEntry.Input output.child.tree output.global := {
    parentTag := output.tag,parent := child,selected := input.selected,maximum := input.maximum,
    offset := input.offset,len := input.len,tagged := lookup,positive := positive,
    distinct := by rw [roots];exact input.distinct
    short := nextShort,nodeRoom := by omega,tagRoom := nextRoom }
  exact ⟨output,run,afterRuntime,next,rfl,rfl,rfl,rfl,rfl⟩

/-- The real Default constructor forms the next helper input internally.
Only initial numerical headroom is added; no future Input or tag ordering. -/
theorem default (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : GeneralBorrowFreshRootScopedDefault.Input tree global)
    (nodeHeadroom : tree.nodes.size+1 < 65536)
    (tagHeadroom : global.nextPointerTag.value.toNat+1 < 18446744073709551615) :
    ∃ output,GeneralBorrowRawDefault.operation tree global input.parentTag input.offset input.len .VisitChildrenOfAccessed = .ok output ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ next : GeneralBorrowFreshRootScopedFnEntry.Input output.child.tree output.global,
        next.parentTag = output.tag ∧ next.selected = input.selected ∧ next.maximum = input.maximum ∧
        next.offset = input.offset ∧ next.len = input.len := by
  obtain ⟨output,run,tagEq,globalEq,protections,readDone,childDone,afterRuntime,capacity,growth,child,lookup,roots,⟨positive⟩⟩ :=
    GeneralBorrowFreshRootScopedDefault.invoke_positive tree global runtime input
  have nextShort : output.child.tree.nodes.size < 65536 := by omega
  have nextRoom : output.global.nextPointerTag.value < 18446744073709551615 := by
    rw [globalEq]
    change (TypedRetagEmpty.successorTag global.nextPointerTag input.tagRoom).value < 18446744073709551615
    apply UInt64.lt_iff_toNat_lt.mpr
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag input.tagRoom
    change (TypedRetagEmpty.successorTag global.nextPointerTag input.tagRoom).value.toNat < 18446744073709551615
    omega
  let next : GeneralBorrowFreshRootScopedFnEntry.Input output.child.tree output.global := {
    parentTag := output.tag,parent := child,selected := input.selected,maximum := input.maximum,
    offset := input.offset,len := input.len,tagged := lookup,positive := positive,
    distinct := by rw [roots];exact input.distinct
    short := nextShort,nodeRoom := by omega,tagRoom := nextRoom }
  exact ⟨output,run,afterRuntime,next,rfl,rfl,rfl,rfl,rfl⟩

end DuplicatePrefix.GeneralBorrowFreshRootScopedReferenceNextInput
