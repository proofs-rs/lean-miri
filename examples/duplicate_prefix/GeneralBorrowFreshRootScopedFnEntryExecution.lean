import duplicate_prefix.GeneralBorrowFreshRootScopedFnEntry
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedFnEntryExecution
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Actual parent Read and protected child completion, projected only from the
raw S01/runtime FnEntry theorem. This packet has no future-operation field. -/
theorem completed (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : GeneralBorrowFreshRootScopedFnEntry.Input tree global) :
    let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read (global.protectedTags.insert global.nextPointerTag .StrongProtector) .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status = .Completed ∧ child.outcome = .ok () := by
  obtain ⟨output,actual,_,_,_,readDone,childDone,_⟩ := GeneralBorrowFreshRootScopedFnEntry.invoke_positive tree global frame allocation runtime input
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom
  let read := GeneralBorrowForestProtected.read tree registration.1.protectedTags input.parentTag input.offset input.len .VisitChildrenOfAccessed
  let child := GeneralBorrowForestProtected.child tree registration.1.protectedTags input.parentTag global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed
  let expected : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,read,child⟩
  have operation : GeneralBorrowForestFnEntry.operation tree global frame allocation input.parentTag input.offset input.len .VisitChildrenOfAccessed = .ok expected := by
    simp only [GeneralBorrowForestFnEntry.operation,TypedRetagEmpty.allocate_tag global input.tagRoom,Except.bind,Except.pure,bind,pure]
    rfl
  have equal : output = expected := Except.ok.inj (actual.symm.trans operation)
  rw [equal] at readDone childDone
  exact ⟨readDone,childDone⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedFnEntryExecution
