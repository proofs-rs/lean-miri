import duplicate_prefix.GeneralBorrowExposedScopedWritableAcceptedToAsMut
import duplicate_prefix.GeneralBorrowExposedScopedWritableAcceptedSourceGraph
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableAcceptedGraphMetadata
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Physical source Origins connect the actual ordinary writable expression,
protected as_mut_ptr helper and helper release to the complete three-node graph
and two-child restore prefix. Final graph/path/tag flags are derived. -/
theorem metadata (expression : GeneralBorrowExposedScopedWritableAcceptedExpression.Input)
    (call : GeneralBorrowExposedScopedWritableAsMutCallInput.Input)
    (origin : GeneralBorrowExposedScopedWritableAcceptedToAsMut.Origin expression call) :
    let tree:=GeneralBorrowExposedScopedWritableAsMutCallReturn.released call
    let target:=expression.data.input.parent
    let expr:=GeneralBorrowFreshMetadataChildDefault.index expression.data.input
    let child:=GeneralBorrowFreshMetadataChildMutable.index call.data.input
    GeneralBorrowGcAllocator.NodeTags tree ∧ GeneralBorrowGraph.RootsCover tree ∧ tree.nodes.size<65536 ∧
    tree.nodes.data.size≤4294967296 ∧ tree.indexOfTag call.tracker.global.nextPointerTag=some child ∧ ∃targetNode exprNode childNode,
      tree.nodeAt target=some targetNode ∧ targetNode.tag=expression.data.input.parentNode.tag ∧ targetNode.isExposed=false ∧
      tree.nodeAt expr=some exprNode ∧ exprNode.tag=expression.tracker.global.nextPointerTag ∧ exprNode.isExposed=false ∧
      tree.nodeAt child=some childNode ∧ childNode.tag=call.tracker.global.nextPointerTag ∧ childNode.isExposed=false ∧
      ∀(location : LocationTree)(tags : ProtectedTags),
        (source_normal_projection tree location tags).topology.ancestorPath child.toNat=
          child.toNat::expr.toNat::(source_normal_projection tree location tags).topology.ancestorPath target.toNat ∧
        expr.toNat∉(source_normal_projection tree location tags).topology.ancestorPath target.toNat ∧
        child.toNat∉(source_normal_projection tree location tags).topology.ancestorPath target.toNat := by
  let first:=expression.data.input
  let helper:=call.data.input
  let protections:=(GeneralBorrowExposedScopedWritableAsMutCallInput.held call).global.protectedTags
  have initialTags : GeneralBorrowGcAllocator.NodeTags first.tree := by
    intro query node present
    rw [expression.data.treeEq] at present ⊢
    exact expression.data.nodeTags query node present
  have firstMeta:=GeneralBorrowExposedScopedWritableDefaultGraphMetadata.run first expression.tracker.global.protectedTags expression.selected expression.head expression.tail
    expression.data.resources expression.atBase expression.full initialTags
  have firstChildEq : GeneralBorrowExposedScopedWritableAcceptedSourceGraph.defaultChild first expression.tracker.global.protectedTags=
      GeneralBorrowExposedScopedWritableAcceptedExpression.expressionTree expression := by
    simp only [GeneralBorrowExposedScopedWritableAcceptedSourceGraph.defaultChild,first,
      GeneralBorrowExposedScopedWritableAcceptedExpression.expressionTree,GeneralBorrowExposedScopedDefaultExpression.child,
      GeneralBorrowExposedScopedDefaultExpression.read,expression.data.treeEq,expression.data.parentTagEq,expression.data.newTagEq,
      expression.data.offsetEq,expression.data.lenEq]
  have helperTreeEq : helper.tree=GeneralBorrowExposedScopedWritableAcceptedExpression.expressionTree expression := by
    rw [call.data.treeEq,origin.entry]
    rfl
  have helperTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by
    rw [helperTreeEq,←firstChildEq]
    exact firstMeta.1
  obtain ⟨heldRaw,supportEq⟩:=GeneralBorrowExposedScopedWritableMutableEntryInput.register helper call.tracker.global.protectedTags call.selected call.head call.tail
    call.data.resources helperTags
  have raw : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources helper protections call.selected call.head call.tail := by
    simpa only [helper,protections,GeneralBorrowExposedScopedWritableAsMutCallInput.held,TypedBorrowSteps.registeredTracker,TypedBorrowSteps.registeredGlobal,
      ReferenceBorrowDriver.allocatedTracker,call.data.newTagEq] using heldRaw
  have source:=GeneralBorrowExposedScopedWritableAcceptedSourceGraph.metadata first helper expression.tracker.global.protectedTags protections
    expression.selected expression.head expression.tail call.selected call.head call.tail expression.data.resources raw expression.atBase expression.full call.atBase call.full
    initialTags (helperTreeEq.trans firstChildEq.symm) origin.parent
  have releasedEq : GeneralBorrowExposedScopedWritableAcceptedSourceGraph.released helper protections=
      GeneralBorrowExposedScopedWritableAsMutCallReturn.released call := by
    simp only [GeneralBorrowExposedScopedWritableAcceptedSourceGraph.released,GeneralBorrowExposedScopedWritableAcceptedSourceGraph.mutableChild,
      GeneralBorrowExposedScopedWritableAsMutCallReturn.released,GeneralBorrowExposedScopedWritableAsMutCallInput.childTree,
      GeneralBorrowExposedScopedWritableMutableArgumentRaw.finalTree,helper,
      call.data.treeEq,call.data.parentTagEq,call.data.newTagEq,call.data.offsetEq,call.data.lenEq]
    rfl
  dsimp only [helper,protections] at releasedEq
  dsimp only at source
  rw [releasedEq] at source
  simpa only [first,helper,expression.data.newTagEq,call.data.newTagEq] using source
end DuplicatePrefix.GeneralBorrowExposedScopedWritableAcceptedGraphMetadata
