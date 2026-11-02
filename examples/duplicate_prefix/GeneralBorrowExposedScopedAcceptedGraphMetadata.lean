import duplicate_prefix.GeneralBorrowExposedScopedAcceptedToAsMut
import duplicate_prefix.GeneralBorrowExposedScopedDefaultGraphMetadata
import duplicate_prefix.GeneralBorrowExposedScopedProtectedDefaultGraphMetadata
namespace DuplicatePrefix.GeneralBorrowExposedScopedAcceptedGraphMetadata
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshMetadataChildDefault
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option backward.split false

theorem source_bounds (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources input protections selected head tail)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes) :
    let read:=input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child:=read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    let released:=(child.tree.releaseProtector input.newTag protections).tree
    GeneralBorrowGraph.RootsCover released ∧ released.nodes.size<65536 := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedDefaultLeafRun.prepare input protections selected head tail raw atBase full .VisitChildrenOfAccessed
  let mutable:=GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared
  have metadata:=GeneralBorrowFreshMetadataChildMutable.append mutable
  have childEq : GeneralBorrowFreshMetadataChildMutable.result mutable=
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,mutable,GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  dsimp only
  rw [←childEq]
  have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release (GeneralBorrowFreshMetadataChildMutable.result mutable) protections input.newTag
  rw [frame]
  refine ⟨metadata.certificates.covered,?_⟩
  rw [metadata.size]
  change prepared.tree.nodes.size+1<65536
  have readFrame:=GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  rw [treeEq,readFrame]
  exact raw.room

/-- The actual ordinary mutable expression, protected as_mut_ptr entry and
helper release preserve original target/tag identity and form both fresh nodes'
production ancestor prefix. Every graph fact comes from initial source Inputs
and their physical Origin; no final node/path/lookup premise is required. -/
theorem metadata (expression : GeneralBorrowExposedScopedAcceptedExpression.Input)
    (call : GeneralBorrowExposedScopedAsMutCallInput.Input)
    (origin : GeneralBorrowExposedScopedAcceptedToAsMut.Origin expression call) :
    let tree:=GeneralBorrowExposedScopedAsMutCallReturn.released call
    let target:=expression.data.input.parent
    let expr:=index expression.data.input
    let child:=index call.data.input
    GeneralBorrowGcAllocator.NodeTags tree ∧ GeneralBorrowGraph.RootsCover tree ∧ tree.nodes.size<65536 ∧
    tree.nodes.data.size≤4294967296 ∧ tree.indexOfTag call.tracker.global.nextPointerTag=some child ∧ ∃ targetNode exprNode childNode,
      tree.nodeAt target=some targetNode ∧ targetNode.tag=expression.data.input.parentNode.tag ∧ targetNode.isExposed=false ∧
      tree.nodeAt expr=some exprNode ∧ exprNode.tag=expression.tracker.global.nextPointerTag ∧ exprNode.isExposed=false ∧
      tree.nodeAt child=some childNode ∧ childNode.tag=call.tracker.global.nextPointerTag ∧ childNode.isExposed=false ∧
      ∀ (location : LocationTree) (tags : ProtectedTags),
        (source_normal_projection tree location tags).topology.ancestorPath child.toNat=
          child.toNat::expr.toNat::(source_normal_projection tree location tags).topology.ancestorPath target.toNat ∧
        expr.toNat∉(source_normal_projection tree location tags).topology.ancestorPath target.toNat ∧
        child.toNat∉(source_normal_projection tree location tags).topology.ancestorPath target.toNat := by
  let tree:=GeneralBorrowExposedScopedAsMutCallReturn.released call
  let first:=expression.data.input
  let helper:=call.data.input
  let firstChild:=GeneralBorrowExposedScopedAcceptedExpression.expressionTree expression
  let helperChild:=GeneralBorrowExposedScopedAsMutCallInput.childTree call
  let protections:=(GeneralBorrowExposedScopedAsMutCallInput.held call).global.protectedTags
  have initialTags : GeneralBorrowGcAllocator.NodeTags first.tree := by
    intro query node present
    rw [expression.data.treeEq] at present ⊢
    exact expression.data.nodeTags query node present
  have firstMeta:=GeneralBorrowExposedScopedDefaultGraphMetadata.run first expression.tracker.global.protectedTags expression.selected expression.head expression.tail
    expression.data.resources expression.atBase expression.full initialTags
  have firstChildEq :
      ((first.tree.performBorrowAccessRange (.concrete first.parentTag) (Size.ofBytes first.offset) (Size.ofBytes first.len) .Read expression.tracker.global.protectedTags .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes first.offset) (.concrete first.parentTag) first.newTag
        (DedupRangeMap.new (Size.ofBytes first.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree=firstChild := by
    simp only [first,firstChild,GeneralBorrowExposedScopedAcceptedExpression.expressionTree,GeneralBorrowExposedScopedDefaultExpression.child,
      GeneralBorrowExposedScopedDefaultExpression.read,expression.data.treeEq,expression.data.parentTagEq,expression.data.newTagEq,expression.data.offsetEq,expression.data.lenEq]
  have helperTreeEq : helper.tree=firstChild := by
    rw [call.data.treeEq,origin.entry]
    rfl
  have helperTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by
    rw [helperTreeEq,←firstChildEq]
    exact firstMeta.1
  have freshAbsent : helper.tree.indexOfTag helper.newTag=none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find helper.tree.tagMapping helper.newTag helper.fresh,Option.map_none]
  obtain ⟨heldRaw,supportEq⟩:=GeneralBorrowExposedScopedDefaultLeafProtect.protect helper call.tracker.global.protectedTags helper.newTag call.selected call.head call.tail
    call.data.resources (by
      intro index node present same
      have mapped:=helperTags index node present
      change helper.tree.indexOfTag node.tag=some index at mapped
      rw [same,freshAbsent] at mapped
      cases mapped)
  have raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources helper protections call.selected call.head call.tail := by
    simpa only [helper,protections,GeneralBorrowExposedScopedAsMutCallInput.held,TypedBorrowSteps.registeredTracker,TypedBorrowSteps.registeredGlobal,
      ReferenceBorrowDriver.allocatedTracker,call.data.newTagEq] using heldRaw
  have helperMeta:=GeneralBorrowExposedScopedProtectedDefaultGraphMetadata.run helper protections call.selected call.head call.tail raw call.atBase call.full helperTags
  have helperChildEq :
      ((helper.tree.performBorrowAccessRange (.concrete helper.parentTag) (Size.ofBytes helper.offset) (Size.ofBytes helper.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes helper.offset) (.concrete helper.parentTag) helper.newTag
        (DedupRangeMap.new (Size.ofBytes helper.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree=helperChild := by
    simp only [helper,helperChild,GeneralBorrowExposedScopedAsMutCallInput.childTree,GeneralBorrowExposedScopedMutableArgumentRaw.finalTree,
      call.data.treeEq,call.data.parentTagEq,call.data.newTagEq,call.data.offsetEq,call.data.lenEq]
    rfl
  have resultEq : ((helper.tree.performBorrowAccessRange (.concrete helper.parentTag) (Size.ofBytes helper.offset) (Size.ofBytes helper.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes helper.offset) (.concrete helper.parentTag) helper.newTag
        (DedupRangeMap.new (Size.ofBytes helper.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.releaseProtector helper.newTag protections=
      helperChild.releaseProtector call.tracker.global.nextPointerTag protections := by rw [helperChildEq,call.data.newTagEq]
  dsimp only at helperMeta
  rw [resultEq,helperChildEq] at helperMeta
  change GeneralBorrowGcAllocator.NodeTags helperChild ∧ GeneralBorrowGcAllocator.NodeTags tree ∧ _ at helperMeta
  have bounds:=source_bounds helper protections call.selected call.head call.tail raw call.atBase call.full
  dsimp only at bounds
  rw [resultEq] at bounds
  change GeneralBorrowGraph.RootsCover tree ∧ tree.nodes.size<65536 at bounds
  have tagLookup : tree.indexOfTag call.tracker.global.nextPointerTag=some (index helper) := by
    have present:=helperMeta.2.2.1
    rw [call.data.newTagEq] at present
    exact present
  obtain ⟨targetInFirst,targetAtFirst,targetTag,targetFlag⟩:=firstMeta.2.2.2.2 first.parent first.parentNode first.parentPresent
  rw [firstChildEq] at targetAtFirst
  have firstFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release firstChild expression.tracker.global.protectedTags first.newTag
  rw [firstFrame] at targetAtFirst
  have targetAtHelper : helper.tree.nodeAt first.parent=some targetInFirst := by rw [helperTreeEq];exact targetAtFirst
  obtain ⟨targetNode,targetPresent,targetFinalTag,targetFinalFlag⟩:=helperMeta.2.2.2.2 first.parent targetInFirst targetAtHelper
  obtain ⟨exprNode,exprPresent,exprTag,exprFlag⟩:=helperMeta.2.2.2.2 helper.parent helper.parentNode helper.parentPresent
  rw [origin.parent] at exprPresent
  obtain ⟨childNode,childPresent,childTag,childHidden⟩:=helperMeta.2.2.2.1
  have exprInFirst:=firstMeta.2.2.2.1
  rw [firstChildEq] at exprInFirst
  obtain ⟨sourceExpr,sourceExprPresent,sourceExprTag,sourceExprHidden⟩:=exprInFirst
  rw [firstFrame] at sourceExprPresent
  have parentPresent : firstChild.nodeAt (index first)=some helper.parentNode := by
    rw [←helperTreeEq,←origin.parent]
    exact helper.parentPresent
  have exprSame : sourceExpr=helper.parentNode:=Option.some.inj (sourceExprPresent.symm.trans parentPresent)
  have hiddenTarget : first.parentNode.isExposed=false:=expression.data.resources.hidden first.parent first.parentNode expression.data.resources.component.anchor first.parentPresent
  refine ⟨helperMeta.2.1,bounds.1,bounds.2,(by change tree.nodes.size≤4294967296;omega),tagLookup,targetNode,exprNode,childNode,targetPresent,targetFinalTag.trans targetTag,
    targetFinalFlag.trans (targetFlag.trans hiddenTarget),exprPresent,?_,exprFlag.trans (by rw [←exprSame];exact sourceExprHidden),childPresent,?_,childHidden,?_⟩
  · rw [exprTag,←exprSame,sourceExprTag,expression.data.newTagEq]
  · exact childTag.trans call.data.newTagEq
  · intro location tags
    have one:=GeneralBorrowExposedScopedDefaultGraphMetadata.attach first expression.tracker.global.protectedTags expression.selected expression.head expression.tail
      expression.data.resources expression.atBase expression.full location location tags
    have two:=GeneralBorrowExposedScopedProtectedDefaultGraphMetadata.attach helper protections call.selected call.head call.tail raw call.atBase call.full location location tags
    dsimp only at one two
    rw [firstChildEq] at one
    rw [helperChildEq,helperTreeEq,origin.parent] at two
    have paths:=GeneralBorrowFreshSharedPaths.two_step _ _ _ first.parent.toNat (index first).toNat (index helper).toNat one two
    have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release helperChild protections call.tracker.global.nextPointerTag
    change tree={helperChild with locations:=tree.locations} at frame
    dsimp only [tree] at frame
    rw [frame]
    exact paths
end DuplicatePrefix.GeneralBorrowExposedScopedAcceptedGraphMetadata
