import duplicate_prefix.GeneralBorrowFreshRootScopedObserverSharedFnEntryVirtual
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntryResources
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedObserverSharedFnEntryResources
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralRangeMapOrigins
open GeneralBorrowObserverReadRange (Observer)
open GeneralBorrowObserverReadRow (virtual)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Derived mutable observer resources on the EXACT BorrowTree and full global
installed by actual typed shared FnEntry argument validation. All inputs describe
BEFORE tag allocation; source Read alone drives the shared helper operations. -/
theorem resources (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input tree tracker.global)
    (parentNode observerNode : TreeNode) (observer : UniIndex)
    (parentPresent : tree.nodeAt input.parent = some parentNode) (edge : parentNode.parent = some observer)
    (parentHidden : parentNode.isExposed = false) (parentUnprotected : tracker.global.protectedTags.contains parentNode.tag = false)
    (observerPresent : tree.nodeAt observer = some observerNode)
    (observerPath : ((source_normal_projection tree default tracker.global.protectedTags).topology.ancestorPath observer.toNat).getLast? = some input.selected.toNat)
    (observerOwned : OwnedOn (Observer tree tracker.global.protectedTags observer) input.offset (input.offset+input.len) tree.locations)
    (observerActivity : GeneralBorrowFreshActiveWithin.ActiveWithin tree observer .Write input.offset (input.offset+input.len)) :
    let finalTree := GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom)
      tracker.global.nextPointerTag
    DuplicatePrefixBorrowContract.RuntimeFacts finalTree fullGlobal ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin finalTree observer .Write input.offset (input.offset+input.len) ∧
    ∃ child,finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive finalTree fullGlobal.protectedTags
        child input.selected input.maximum input.offset input.len) ∧
      OwnedOn (Observer finalTree (virtual fullGlobal allocation tracker.global.nextPointerTag parentNode.tag) observer)
        input.offset (input.offset+input.len) finalTree.locations := by
  obtain ⟨output,actual,tag,global,readDone,childDone,afterRuntime,activity,
    child,lookup,childPositive,observerRows⟩ :=
    GeneralBorrowFreshRootScopedObserverSharedFnEntryVirtual.invoke tree tracker.global frame allocation runtime input parentNode observerNode observer
      parentPresent edge parentHidden parentUnprotected observerPresent observerPath observerOwned observerActivity
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
  rw [equal] at afterRuntime activity lookup childPositive observerRows
  exact ⟨afterRuntime,activity,child,lookup,childPositive,observerRows⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedObserverSharedFnEntryResources
