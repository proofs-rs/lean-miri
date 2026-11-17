import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedAfterLen
import duplicate_prefix.GeneralBorrowScopedConcreteWritableLenTargetMetadata
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFnEntryNode
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedTargetTag
variable {profileMode : ProfileMode}
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
 theorem source (s : GeneralBorrowPositiveConcreteWindowAcceptedInput.InitialFor profileMode) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode) (stage : GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.InitialFor profileMode)
    (expression : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode)
    (origin : GeneralBorrowPositiveConcreteWindowAcceptedAfterLen.Origin s updated i stage)
    (expressionOrigin : GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.Origin stage expression) :
    expression.data.input.parentNode.tag=s.tracker.global.nextPointerTag ∧ expression.data.input.parent=i.first.parent ∧ expression.data.input.parentNode.isExposed=false := by
  have sourceTree : expression.data.input.tree=GeneralBorrowScopedConcreteWritableLenTargetMetadata.tree i := by
    rw [expression.data.treeEq,expressionOrigin.entry,origin.entry]
    simp only [GeneralBorrowPositiveConcreteWindowAcceptedDefaultData.released,GeneralBorrowExposedScopedSharedPathMetadata.child,
      GeneralBorrowPositiveConcreteWindowAcceptedDefaultData.held,GeneralBorrowScopedConcreteWritableLenTargetMetadata.tree,GeneralBorrowScopedConcreteWritableLenTargetMetadata.held,
      GeneralBorrowExposedScopedSharedArgumentCopy.finalTree,i.treeEq,i.parentTagEq,i.tagEq,i.offsetEq,i.lenEq,i.protectedEq]
    rfl
  have initialHidden : i.first.parentNode.isExposed=false := by
    obtain ⟨node,present,tag,hidden⟩:=GeneralBorrowPositiveConcreteWindowFnEntryNode.source s.toInitial.toBase
    have here : i.first.tree.nodeAt i.first.parent=some node := by rw [origin.lenOrigin.firstTree,origin.lenOrigin.target];exact present
    have same:=Option.some.inj (i.first.parentPresent.symm.trans here)
    rw [same]
    exact hidden
  obtain ⟨node,present,tag,hidden⟩ := (GeneralBorrowScopedConcreteWritableLenTargetMetadata.source i initialHidden).1
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
  exact ⟨sameNode ▸ tagEq,parentEq,sameNode ▸ hidden⟩
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedTargetTag
