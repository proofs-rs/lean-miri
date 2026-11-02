import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntryArgument
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedFnEntryResources
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Full raw resources on the exact tree and advanced registered GlobalState
installed by actual typed shared FnEntry validation. No future capability is
assumed; all fields project the actual borrowing invocation. -/
theorem resources (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input tree tracker.global) :
    let finalTree := GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom)
      tracker.global.nextPointerTag
    DuplicatePrefixBorrowContract.RuntimeFacts finalTree fullGlobal ∧
    finalTree.locations.size = tree.locations.size ∧ finalTree.nodes.size ≤ tree.nodes.size+1 ∧
    finalTree.roots = tree.roots ∧
    fullGlobal.protectedTags.get tracker.global.nextPointerTag = some .StrongProtector ∧
    GeneralBorrowTagMap.Fresh tree.tagMapping tracker.global.nextPointerTag ∧
    ∃ child,finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive finalTree fullGlobal.protectedTags
        input.parent input.selected input.maximum input.offset input.len) ∧
      Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive finalTree fullGlobal.protectedTags
        child input.selected input.maximum input.offset input.len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree child .Read input.offset (input.offset+input.len) := by
  obtain ⟨output,actual,tag,global,held,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    child,lookup,roots,parentPositive,childPositive,activity⟩ :=
    GeneralBorrowFreshRootScopedSharedFnEntry.invoke tree tracker.global frame allocation runtime input
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let read := GeneralBorrowForestProtected.read tree registration.1.protectedTags input.parentTag input.offset input.len .VisitChildrenOfAccessed
  let constructed := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) tracker.global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
  let expected : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,tracker.global.nextPointerTag,read,constructed⟩
  have operation : GeneralBorrowRawSharedFnEntry.operation tree tracker.global frame allocation input.parentTag input.offset input.len
      .VisitChildrenOfAccessed = .ok expected := by
    simp only [GeneralBorrowRawSharedFnEntry.operation,TypedRetagEmpty.allocate_tag tracker.global input.tagRoom,
      Except.bind,Except.pure,bind,pure]
    rfl
  have equal : output = expected := Except.ok.inj (actual.symm.trans operation)
  rw [equal] at held afterRuntime capacity growth lookup roots parentPositive childPositive activity
  obtain ⟨_,_,_,_,_,fresh⟩ := GeneralBorrowFreshRootScopedRegistration.read_prepare tree tracker.global frame allocation input.tagRoom
    runtime input.parent input.selected input.maximum input.offset input.len input.positive
  exact ⟨afterRuntime,capacity,growth,roots,held,fresh,child,lookup,parentPositive,childPositive,activity⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedFnEntryResources
