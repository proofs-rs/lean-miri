import duplicate_prefix.GeneralBorrowFreshRootScopedFnEntryArgument
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedFnEntryResources
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Raw mutable resources on the exact typed FnEntry result tree and full
advanced registered global. The actual allocator supplies the child index. -/
theorem resources (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedFnEntry.Input tree tracker.global) :
    let finalTree := GeneralBorrowFreshRootScopedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom)
      tracker.global.nextPointerTag
    DuplicatePrefixBorrowContract.RuntimeFacts finalTree fullGlobal ∧
    finalTree.locations.size = tree.locations.size ∧ finalTree.nodes.size ≤ tree.nodes.size+1 ∧
    finalTree.roots = tree.roots ∧ fullGlobal.protectedTags.get tracker.global.nextPointerTag = some .StrongProtector ∧
    (GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom).2.protectedTags =
      frame.protectedTags.push (allocation,tracker.global.nextPointerTag) ∧
    GeneralBorrowTagMap.Fresh tree.tagMapping tracker.global.nextPointerTag ∧
    ∃ child, finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive finalTree fullGlobal.protectedTags
        child input.selected input.maximum input.offset input.len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree child .Write input.offset (input.offset+input.len) := by
  obtain ⟨output,actual,tag,global,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    child,lookup,roots,childPositive,activity⟩ :=
    GeneralBorrowFreshRootScopedFnEntry.invoke_positive tree tracker.global frame allocation runtime input
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let read := GeneralBorrowForestProtected.read tree registration.1.protectedTags input.parentTag input.offset input.len .VisitChildrenOfAccessed
  let constructed := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) tracker.global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  let expected : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,tracker.global.nextPointerTag,read,constructed⟩
  have operation : GeneralBorrowForestFnEntry.operation tree tracker.global frame allocation input.parentTag input.offset input.len
      .VisitChildrenOfAccessed = .ok expected := by
    simp only [GeneralBorrowForestFnEntry.operation,TypedRetagEmpty.allocate_tag tracker.global input.tagRoom,
      Except.bind,Except.pure,bind,pure]
    rfl
  have equal : output = expected := Except.ok.inj (actual.symm.trans operation)
  rw [equal] at afterRuntime capacity growth lookup roots childPositive activity
  obtain ⟨_,held,framePush,_,_,fresh⟩ := GeneralBorrowFreshRootScopedRegistration.prepare tree tracker.global frame allocation input.tagRoom
    runtime input.parent input.selected input.maximum input.offset input.len input.positive
  exact ⟨afterRuntime,capacity,growth,roots,held,framePush,fresh,child,lookup,childPositive,activity⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedFnEntryResources
