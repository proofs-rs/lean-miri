import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedPathMetadata
import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedRestore
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedMetadata
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedReadRelease
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableSharedCallReady
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedWindowWritableSharedPathMetadata (child)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- The exact helper Read/child/release source sequence yields its graph
context as well as the range contracts used after the physical helper return. -/
theorem helper_context (input : Input) (global : GlobalState) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input global.protectedTags selected head tail writable)
    :
    Nonempty (GeneralBorrowExposedKnownRootRangeData.Context
      ((child input global.protectedTags .VisitChildrenOfAccessed).releaseProtector input.newTag global.protectedTags).tree (index input) selected head tail) := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedWindowWritableSharedRun.prepare input global.protectedTags selected head tail writable raw .VisitChildrenOfAccessed
  obtain ⟨success,context,owned⟩:=GeneralBorrowExposedScopedWritableSharedConstructor.construct prepared global.protectedTags selected head tail writable preparedRaw
  have childEq : result prepared=child input global.protectedTags .VisitChildrenOfAccessed := by
    simp only [result,GeneralBorrowExposedScopedWindowWritableSharedPathMetadata.child,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  rw [childEq,indexEq] at context
  rw [GeneralBorrowStructuralReleaseGeometryFrame.release]
  exact ⟨{
    anchorNode:=context.anchorNode
    selectedNode:=context.selectedNode
    anchorPresent:=context.anchorPresent
    selectedPresent:=context.selectedPresent
    roots:=context.roots
    depth:=context.depth
    children:=context.children
    tags:=context.tags }⟩

/-- Two real scoped shared stages, followed by the real helper release and
endCall, form the original target's complete Write-ready range data. All
prefix paths, hidden helper facts, target membership, final cache coherence,
and foreign Write profiles are derived from initial source metadata/resources.
The physical MIR call/return theorem identifies its released tree with this
same source result. -/
theorem build (first helper : Input) (firstTags : ProtectedTags) (global : GlobalState)
    (allocation : AllocId) (selected head : UniIndex) (tail : List UniIndex)
    (firstRaw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources first firstTags selected head tail (fun _=>true))
    (helperRaw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources helper global.protectedTags selected head tail
      (GeneralBorrowFreshMixedChild.extend (fun _=>true) (index first).toNat))
    (treeEq : helper.tree=child first firstTags .VisitChildrenOfAccessed) (parentEq : helper.parent=index first)
    (initialTags : GeneralBorrowGcAllocator.NodeTags first.tree)
    (exprUnheld : global.protectedTags.contains helper.parentNode.tag=false)
    (positive : helper.offset.toNat<(helper.offset+helper.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index helper)=none) helper.tree.locations) :
    let released:=((child helper global.protectedTags .VisitChildrenOfAccessed).releaseProtector helper.newTag global.protectedTags).tree
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context released first.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedWritableReadData.Data released location
        (global.endCall (({} : FrameState).addProtector allocation helper.newTag)).protectedTags first.parent selected head tail
        (fun position=>helperRaw.component.support position ∨ position=(index helper).toNat) (fun _=>true)))
        helper.offset (helper.offset+helper.len) released.locations ∧
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released location
        (global.endCall (({} : FrameState).addProtector allocation helper.newTag)).protectedTags first.parent selected head tail .Write))
        helper.offset (helper.offset+helper.len) released.locations ∧
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released location
        (global.endCall (({} : FrameState).addProtector allocation helper.newTag)).protectedTags first.parent selected head tail .Read))
        helper.offset (helper.offset+helper.len) released.locations := by
  let firstChild:=child first firstTags .VisitChildrenOfAccessed
  let helperChild:=child helper global.protectedTags .VisitChildrenOfAccessed
  let released:=(helperChild.releaseProtector helper.newTag global.protectedTags).tree
  have firstMetadata:=GeneralBorrowExposedScopedWindowWritableSharedMetadata.run first firstTags selected head tail (fun _=>true) firstRaw initialTags
  have helperTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by rw [treeEq];exact firstMetadata.1
  have helperMetadata:=GeneralBorrowExposedScopedWindowWritableSharedMetadata.run helper global.protectedTags selected head tail _ helperRaw helperTags
  obtain ⟨oldTarget,targetAtFirst,targetTag,targetExposure⟩:=firstMetadata.2.2.2.2 first.parent first.parentNode first.parentPresent
  have firstFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release firstChild firstTags first.newTag
  change (firstChild.releaseProtector first.newTag firstTags).tree.nodeAt first.parent=some oldTarget at targetAtFirst
  have targetAtHelper : helper.tree.nodeAt first.parent=some oldTarget := by
    rw [firstFrame] at targetAtFirst
    rw [treeEq]
    exact targetAtFirst
  obtain ⟨targetNode,targetPresent,_,_⟩:=helperMetadata.2.2.2.2 first.parent oldTarget targetAtHelper
  obtain ⟨exprNode,exprPresent,exprTag,_⟩:=helperMetadata.2.2.2.2 helper.parent helper.parentNode helper.parentPresent
  rw [parentEq] at exprPresent
  obtain ⟨helperNode,helperPresent,helperTag,helperHidden⟩:=helperMetadata.2.2.2.1
  obtain ⟨helperContext⟩:=helper_context helper global selected head tail _ helperRaw
  have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release helperChild global.protectedTags helper.newTag
  have paths (location : LocationTree) := GeneralBorrowExposedScopedWindowWritableSharedPathMetadata.two_step first helper firstTags global.protectedTags selected head tail (fun _=>true)
    firstRaw helperRaw .VisitChildrenOfAccessed .VisitChildrenOfAccessed treeEq parentEq global.protectedTags location
  have releasedPaths (location : LocationTree) :
      (source_normal_projection released location global.protectedTags).topology.ancestorPath (index helper).toNat=
        (index helper).toNat::(index first).toNat::(source_normal_projection released location global.protectedTags).topology.ancestorPath first.parent.toNat ∧
      (index first).toNat∉(source_normal_projection released location global.protectedTags).topology.ancestorPath first.parent.toNat ∧
      (index helper).toNat∉(source_normal_projection released location global.protectedTags).topology.ancestorPath first.parent.toNat := by
    dsimp only [released]
    rw [frame]
    exact paths location
  have helperData:=GeneralBorrowExposedScopedWindowWritableSharedReadRelease.release helper global.protectedTags selected head tail _ helperRaw positive clean
  let targetContext : GeneralBorrowExposedKnownRootRangeData.Context released first.parent selected head tail:={
    helperContext with anchorNode:=targetNode,anchorPresent:=targetPresent}
  have targetData : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedWritableReadData.Data released location
      (global.endCall (({} : FrameState).addProtector allocation helper.newTag)).protectedTags first.parent selected head tail
      (fun position=>helperRaw.component.support position ∨ position=(index helper).toNat) (fun _=>true)))
      helper.offset (helper.offset+helper.len) released.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩:=helperData.2.1 position valid positive lower upper
    have restored:=GeneralBorrowExposedScopedWritableSharedRestore.restore released _ global allocation (index helper) (index first) first.parent selected head tail
      (fun position=>helperRaw.component.support position ∨ position=(index helper).toNat) data helperContext
      targetNode exprNode helperNode targetPresent exprPresent helperPresent helperMetadata.2.1
      (by rw [exprTag];exact exprUnheld) (fun location=>(releasedPaths location).1)
      (fun location=>(releasedPaths location).2.1) (fun location=>(releasedPaths location).2.2) helperRaw.first helperRaw.rest
    rw [helperTag] at restored
    exact ⟨restored⟩
  refine ⟨targetContext,targetData,?_,?_⟩
  · intro position valid positive lower upper
    obtain ⟨data⟩:=targetData position valid positive lower upper
    exact ⟨GeneralBorrowExposedScopedWritableReadData.write released _ _ first.parent selected head tail _ targetContext data⟩
  · intro position valid positive lower upper
    obtain ⟨data⟩:=targetData position valid positive lower upper
    exact ⟨data.base.base⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableSharedCallReady
