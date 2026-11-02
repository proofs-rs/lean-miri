import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableDefaultGraphMetadata
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableProtectedMutableGraphMetadata
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAcceptedSourceGraph
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def defaultChild (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags) :=
  ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
    (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree

def mutableChild (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) :=
  ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
    (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree

def released (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) :=
  ((mutableChild input protections).releaseProtector input.newTag protections).tree

theorem source_bounds (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources input protections selected head tail)
    :
    GeneralBorrowGraph.RootsCover (released input protections) ∧ (released input protections).nodes.size<65536 := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedWindowWritableProtectedMutableRun.prepare input protections selected head tail raw .VisitChildrenOfAccessed
  have metadata:=GeneralBorrowFreshMetadataChildMutable.append prepared
  have childEq : GeneralBorrowFreshMetadataChildMutable.result prepared=mutableChild input protections := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,mutableChild,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  unfold released
  rw [←childEq]
  have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release (GeneralBorrowFreshMetadataChildMutable.result prepared) protections input.newTag
  rw [frame]
  refine ⟨metadata.certificates.covered,?_⟩
  rw [metadata.size]
  change prepared.tree.nodes.size+1<65536
  have readFrame:=GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  rw [treeEq,readFrame]
  exact raw.room

/-- Actual ordinary expression and protected helper source operations retain
all three node identities and form the production two-child ancestor prefix.
Only initial raw constructor resources and their source aliases are required. -/
theorem metadata (first : GeneralBorrowFreshMetadataChildDefault.Input) (helper : GeneralBorrowFreshMetadataChildMutable.Input)
    (firstTags helperTags : ProtectedTags) (firstSelected firstHead : UniIndex) (firstTail : List UniIndex)
    (selected head : UniIndex) (tail : List UniIndex)
    (firstRaw : GeneralBorrowExposedScopedWritableDefaultConstructor.Resources first firstTags firstSelected firstHead firstTail)
    (helperRaw : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources helper helperTags selected head tail)
    (initialTags : GeneralBorrowGcAllocator.NodeTags first.tree)
    (treeEq : helper.tree=defaultChild first firstTags) (parentEq : helper.parent=GeneralBorrowFreshMetadataChildDefault.index first) :
    let tree:=released helper helperTags
    let target:=first.parent
    let expr:=GeneralBorrowFreshMetadataChildDefault.index first
    let child:=GeneralBorrowFreshMetadataChildMutable.index helper
    GeneralBorrowGcAllocator.NodeTags tree ∧ GeneralBorrowGraph.RootsCover tree ∧ tree.nodes.size<65536 ∧
    tree.nodes.data.size≤4294967296 ∧ tree.indexOfTag helper.newTag=some child ∧ ∃targetNode exprNode childNode,
      tree.nodeAt target=some targetNode ∧ targetNode.tag=first.parentNode.tag ∧ targetNode.isExposed=false ∧
      tree.nodeAt expr=some exprNode ∧ exprNode.tag=first.newTag ∧ exprNode.isExposed=false ∧
      tree.nodeAt child=some childNode ∧ childNode.tag=helper.newTag ∧ childNode.isExposed=false ∧
      ∀(location : LocationTree)(tags : ProtectedTags),
        (source_normal_projection tree location tags).topology.ancestorPath child.toNat=
          child.toNat::expr.toNat::(source_normal_projection tree location tags).topology.ancestorPath target.toNat ∧
        expr.toNat∉(source_normal_projection tree location tags).topology.ancestorPath target.toNat ∧
        child.toNat∉(source_normal_projection tree location tags).topology.ancestorPath target.toNat := by
  let tree:=released helper helperTags
  let firstChild:=defaultChild first firstTags
  let helperChild:=mutableChild helper helperTags
  have firstMeta:=GeneralBorrowExposedScopedWindowWritableDefaultGraphMetadata.run first firstTags firstSelected firstHead firstTail firstRaw initialTags
  have helperNodeTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by
    rw [treeEq]
    exact firstMeta.1
  have helperMeta:=GeneralBorrowExposedScopedWindowWritableProtectedMutableGraphMetadata.run helper helperTags selected head tail helperRaw helperNodeTags
  change GeneralBorrowGcAllocator.NodeTags helperChild ∧ GeneralBorrowGcAllocator.NodeTags tree ∧ _ at helperMeta
  have bounds:=source_bounds helper helperTags selected head tail helperRaw
  change GeneralBorrowGraph.RootsCover tree ∧ tree.nodes.size<65536 at bounds
  obtain ⟨targetInFirst,targetAtFirst,targetTag,targetFlag⟩:=firstMeta.2.2.2.2 first.parent first.parentNode first.parentPresent
  have firstFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release firstChild firstTags first.newTag
  change (firstChild.releaseProtector first.newTag firstTags).tree.nodeAt first.parent=some targetInFirst at targetAtFirst
  rw [firstFrame] at targetAtFirst
  have targetAtHelper : helper.tree.nodeAt first.parent=some targetInFirst := by rw [treeEq];exact targetAtFirst
  obtain ⟨targetNode,targetPresent,targetFinalTag,targetFinalFlag⟩:=helperMeta.2.2.2.2 first.parent targetInFirst targetAtHelper
  obtain ⟨exprNode,exprPresent,exprTag,exprFlag⟩:=helperMeta.2.2.2.2 helper.parent helper.parentNode helper.parentPresent
  rw [parentEq] at exprPresent
  obtain ⟨childNode,childPresent,childTag,childHidden⟩:=helperMeta.2.2.2.1
  obtain ⟨sourceExpr,sourceExprPresent,sourceExprTag,sourceExprHidden⟩:=firstMeta.2.2.2.1
  change (firstChild.releaseProtector first.newTag firstTags).tree.nodeAt (GeneralBorrowFreshMetadataChildDefault.index first)=some sourceExpr at sourceExprPresent
  rw [firstFrame] at sourceExprPresent
  have parentPresent : firstChild.nodeAt (GeneralBorrowFreshMetadataChildDefault.index first)=some helper.parentNode := by
    change (defaultChild first firstTags).nodeAt (GeneralBorrowFreshMetadataChildDefault.index first)=some helper.parentNode
    rw [←treeEq,←parentEq]
    exact helper.parentPresent
  have exprSame : sourceExpr=helper.parentNode:=Option.some.inj (sourceExprPresent.symm.trans parentPresent)
  have hiddenTarget : first.parentNode.isExposed=false:=firstRaw.hidden first.parent first.parentNode firstRaw.component.anchor first.parentPresent
  refine ⟨helperMeta.2.1,bounds.1,bounds.2,(by change tree.nodes.size≤4294967296;omega),helperMeta.2.2.1,
    targetNode,exprNode,childNode,targetPresent,targetFinalTag.trans targetTag,targetFinalFlag.trans (targetFlag.trans hiddenTarget),
    exprPresent,exprTag.trans (by rw [←exprSame];exact sourceExprTag),exprFlag.trans (by rw [←exprSame];exact sourceExprHidden),
    childPresent,childTag,childHidden,?_⟩
  intro location tags
  have one:=GeneralBorrowExposedScopedWindowWritableDefaultGraphMetadata.attach first firstTags firstSelected firstHead firstTail firstRaw location location tags
  have two:=GeneralBorrowExposedScopedWindowWritableProtectedMutableGraphMetadata.attach helper helperTags selected head tail helperRaw location location tags
  change GeneralBorrowFreshSharedPaths.Attach (source_normal_projection first.tree location tags).topology (source_normal_projection firstChild location tags).topology
    first.parent.toNat (GeneralBorrowFreshMetadataChildDefault.index first).toNat at one
  change GeneralBorrowFreshSharedPaths.Attach (source_normal_projection helper.tree location tags).topology (source_normal_projection helperChild location tags).topology
    helper.parent.toNat (GeneralBorrowFreshMetadataChildMutable.index helper).toNat at two
  rw [treeEq,parentEq] at two
  have paths:=GeneralBorrowFreshSharedPaths.two_step _ _ _ first.parent.toNat (GeneralBorrowFreshMetadataChildDefault.index first).toNat
    (GeneralBorrowFreshMetadataChildMutable.index helper).toNat one two
  have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release helperChild helperTags helper.newTag
  change tree={helperChild with locations:=tree.locations} at frame
  dsimp only [tree] at frame
  rw [frame]
  exact paths
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAcceptedSourceGraph
