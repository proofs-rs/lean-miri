import duplicate_prefix.GeneralBorrowFreshRootScopedDefaultExpression
import duplicate_prefix.GeneralBorrowFreshRootScopedFnEntry
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedDefaultResources
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- Full raw resources for the next actual mutable helper, formed from the
unprotected Default retag. The current packet has Both capabilities; no
successor packet or permission outcome is supplied. Headroom accounts for this
child and the following helper child. -/
theorem resources (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615) :
    let finalTree := (GeneralBorrowFreshRootScopedDefaultExpression.child tree tracker.global.protectedTags
      input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    let advanced := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    DuplicatePrefixBorrowContract.RuntimeFacts finalTree advanced.global ∧
    finalTree.locations.size = tree.locations.size ∧ finalTree.nodes.size+1 < 65536 ∧
    ∃ next : GeneralBorrowFreshRootScopedFnEntry.Input finalTree advanced.global,
      next.parentTag = tracker.global.nextPointerTag ∧ next.selected = input.selected ∧
      next.maximum = input.maximum ∧ next.offset = input.offset ∧ next.len = input.len := by
  obtain ⟨output,actual,tag,advanced,protections,readDone,childDone,afterRuntime,capacity,growth,index,lookup,roots,⟨positive⟩⟩ :=
    GeneralBorrowFreshRootScopedDefault.invoke_positive tree tracker.global runtime input
  have equation : Except.ok (ε := GlobalStateError) (⟨GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom,tracker.global.nextPointerTag,
      tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
        .Read tracker.global.protectedTags .VisitChildrenOfAccessed,
      (tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
        .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) tracker.global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false⟩ : GeneralBorrowRawDefault.Output) = .ok output := by
    simpa only [GeneralBorrowRawDefault.operation,GeneralBorrowFnEntryRegistration.advanced,TypedRetagEmpty.allocate_tag tracker.global input.tagRoom,Except.bind,Except.pure,bind,pure] using actual
  have outputEq := Except.ok.inj equation
  subst output
  let finalTree := (GeneralBorrowFreshRootScopedDefaultExpression.child tree tracker.global.protectedTags
    input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
  let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have short : finalTree.nodes.size+1 < 65536 := by change finalTree.nodes.size ≤ tree.nodes.size+1 at growth;omega
  have afterTagRoom : allocated.global.nextPointerTag.value < 18446744073709551615 := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag input.tagRoom
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag input.tagRoom).value < _
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag input.tagRoom).value.toNat < 18446744073709551615
    rw [successor]
    exact tagRoom
  let next : GeneralBorrowFreshRootScopedFnEntry.Input finalTree allocated.global := {
    parentTag := tracker.global.nextPointerTag,parent := index,selected := input.selected,maximum := input.maximum,
    offset := input.offset,len := input.len,tagged := lookup,positive := positive,
    distinct := by rw [show finalTree.roots = tree.roots from roots];exact input.distinct,
    short := by omega,nodeRoom := by omega,tagRoom := afterTagRoom }
  exact ⟨afterRuntime,capacity,short,next,rfl,rfl,rfl,rfl,rfl⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedDefaultResources
