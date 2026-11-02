import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedTargetTag
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowFnEntryActivity
import duplicate_prefix.GeneralBorrowScopedWindowLenTargetActivity
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedInitialActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open GeneralBorrowFreshActiveWithin
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The original window constructor and actual shared/len helper execution
supply the accepted expression's original-target release confinement. Every
activity fact is derived from the initial source and its physical Origins. -/
theorem source (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input)
    (stage : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Initial)
    (expression : GeneralBorrowExposedScopedWindowWritableAcceptedExpression.Input)
    (origin : GeneralBorrowPositiveWildcardWindowAcceptedAfterLen.Origin s updated i stage)
    (expressionOrigin : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Origin stage expression)
    (firstOffset : i.first.offset=s.offset) (firstLen : i.first.len=s.len) :
    ActiveWithin expression.entry.allocation.extra expression.data.input.parent .Write
      expression.offset (expression.offset+expression.len) := by
  have initial:=GeneralBorrowPositiveWildcardWindowFnEntryActivity.source s.toInitial.toBase s.vacantClean
  have firstActive : ActiveWithin i.first.tree i.first.parent .Write i.offset (i.offset+i.len) := by
    rw [origin.lenOrigin.firstTree,origin.lenOrigin.target,origin.lenOrigin.offset,origin.lenOrigin.len]
    exact initial
  have active:=GeneralBorrowScopedWindowLenTargetActivity.source i
    (firstOffset.trans origin.lenOrigin.offset.symm) (firstLen.trans origin.lenOrigin.len.symm) firstActive
  have actual : GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.released i =
      ((GeneralBorrowExposedScopedSharedArgumentCopy.finalTree i.entry.allocation.extra i.tracker i.exprTag i.offset i.len).releaseProtector
        i.tracker.global.nextPointerTag (GeneralBorrowScopedWindowLenTargetActivity.held i).global.protectedTags).tree := by
    simp only [GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.released,
      GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.held,GeneralBorrowScopedWindowLenTargetActivity.held,
      GeneralBorrowExposedScopedSharedPathMetadata.child,i.treeEq,i.parentTagEq,i.tagEq,i.offsetEq,i.lenEq,i.protectedEq,
      GeneralBorrowExposedScopedSharedArgumentCopy.finalTree]
    rfl
  dsimp only at active
  rw [←actual] at active
  have parent:=(GeneralBorrowPositiveWildcardWindowAcceptedTargetTag.source s updated i stage expression origin expressionOrigin).2
  rw [parent]
  rw [expressionOrigin.entry,origin.entry,expressionOrigin.offset,origin.offset,
    expressionOrigin.len,origin.len]
  rw [origin.lenOrigin.offset,origin.lenOrigin.len] at active
  exact active
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedInitialActivity
