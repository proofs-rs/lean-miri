import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAcceptedAfterLen
import duplicate_prefix.GeneralBorrowScopedWritableLenTargetMetadata
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedTargetTag
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
 theorem source (s : GeneralBorrowPositiveWildcardSparseAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedWritableLenCallInput.Input) (stage : GeneralBorrowExposedScopedWritableAcceptedAfterLen.Initial)
    (expression : GeneralBorrowExposedScopedWritableAcceptedExpression.Input)
    (origin : GeneralBorrowPositiveWildcardSparseAcceptedAfterLen.Origin s updated i stage)
    (expressionOrigin : GeneralBorrowExposedScopedWritableAcceptedAfterLen.Origin stage expression) :
    expression.data.input.parentNode.tag=s.tracker.global.nextPointerTag ∧ expression.data.input.parent=i.first.parent := by
  have sourceTree : expression.data.input.tree=GeneralBorrowScopedWritableLenTargetMetadata.tree i := by
    rw [expression.data.treeEq,expressionOrigin.entry,origin.entry]
    simp only [GeneralBorrowPositiveWildcardSparseAcceptedDefaultData.released,GeneralBorrowExposedScopedSharedPathMetadata.child,
      GeneralBorrowPositiveWildcardSparseAcceptedDefaultData.held,GeneralBorrowScopedWritableLenTargetMetadata.tree,GeneralBorrowScopedWritableLenTargetMetadata.held,
      GeneralBorrowExposedScopedSharedArgumentCopy.finalTree,i.treeEq,i.parentTagEq,i.tagEq,i.offsetEq,i.lenEq,i.protectedEq]
    rfl
  obtain ⟨node,present,tag,hidden⟩ := (GeneralBorrowScopedWritableLenTargetMetadata.source i).1
  have tagEq := tag.trans origin.lenOrigin.parentNodeTag
  have parentTagEq := expression.data.parentTagEq.trans (expressionOrigin.parentTag.trans origin.parentTag)
  have nodePresent : expression.entry.allocation.extra.nodeAt i.first.parent=some node := by
    rw [←expression.data.treeEq,sourceTree]
    exact present
  have mapped := expression.data.nodeTags i.first.parent node nodePresent
  have parentMapped : expression.entry.allocation.extra.indexOfTag expression.data.input.parentTag=some expression.data.input.parent := by
    simpa only [expression.data.treeEq,BorrowTree.indexOfTag] using expression.data.input.parentTagPresent
  rw [tagEq] at mapped
  rw [parentTagEq] at parentMapped
  have parentEq : expression.data.input.parent=i.first.parent := Option.some.inj (parentMapped.symm.trans mapped)
  have sameNode : expression.data.input.parentNode=node := by
    have initial:=expression.data.input.parentPresent
    rw [sourceTree,parentEq] at initial
    exact Option.some.inj (initial.symm.trans present)
  exact ⟨sameNode ▸ tagEq,parentEq⟩
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedTargetTag
