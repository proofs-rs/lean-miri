import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedRun
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildOld
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableSharedMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedScopedWritableSharedConstructor (Resources)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem construct_nodeTags (input : Input) (initial : GeneralBorrowGcAllocator.NodeTags input.tree) :
    GeneralBorrowGcAllocator.NodeTags (result input) := by
  have staged := GeneralBorrowSharedAllocatorInvariant.staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned
    (locations input) input.parentPresent input.fresh initial
  have coherent : GeneralBorrowGcAllocator.NodeTags (stage input) := by simpa only [stage,mapping] using staged
  exact GeneralBorrowSharedAllocatorInvariant.shape_tags (stage input) (result input) (shape input) coherent

theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes)
    (initialTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected
    let released := (child.tree.releaseProtector input.newTag protections).tree
    GeneralBorrowGcAllocator.NodeTags child.tree ∧ GeneralBorrowGcAllocator.NodeTags released ∧
      released.indexOfTag input.newTag=some (index input) ∧
      (∃ node,released.nodeAt (index input)=some node ∧ node.tag=input.newTag ∧ node.isExposed=false) ∧
      (∀ query node,input.tree.nodeAt query=some node →
        ∃ next,released.nodeAt query=some next ∧ next.tag=node.tag ∧ next.isExposed=node.isExposed) := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedWritableSharedRun.prepare input protections selected head tail writable raw atBase full .VisitChildrenOfAccessed
  have readFrame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have preparedFrame : prepared.tree={input.tree with locations:=prepared.tree.locations} := by rw [treeEq];exact readFrame
  have preparedTags : GeneralBorrowGcAllocator.NodeTags prepared.tree := by
    rw [preparedFrame]
    exact initialTags
  let released := ((result prepared).releaseProtector input.newTag protections).tree
  have releaseFrame := GeneralBorrowStructuralReleaseGeometryFrame.release (result prepared) protections input.newTag
  have tags := construct_nodeTags prepared preparedTags
  have releasedTags : GeneralBorrowGcAllocator.NodeTags released := by dsimp only [released];rw [releaseFrame];exact tags
  let metadata := GeneralBorrowFreshMetadataChildShared.append prepared
  have lookup : released.indexOfTag input.newTag=some (index input) := by
    dsimp only [released]
    rw [releaseFrame,←newTagEq,←indexEq]
    exact metadata.freshLookup
  have newNode : ∃ node,released.nodeAt (index input)=some node ∧ node.tag=input.newTag ∧ node.isExposed=false := by
    obtain ⟨node,present,tag,parent,children,permission,exposed⟩ := metadata.newNode
    refine ⟨node,?_,tag.trans newTagEq,exposed⟩
    dsimp only [released]
    rw [releaseFrame,←indexEq]
    exact present
  have oldNodes : ∀ query node,input.tree.nodeAt query=some node →
      ∃ next,released.nodeAt query=some next ∧ next.tag=node.tag ∧ next.isExposed=node.isExposed := by
    intro query node present
    have preparedPresent : prepared.tree.nodeAt query=some node := by rw [preparedFrame];exact present
    obtain ⟨next,found,tag,exposed⟩ := GeneralBorrowFreshMetadataChildOld.append prepared query node preparedPresent
    exact ⟨next,by dsimp only [released];rw [releaseFrame];exact found,tag,exposed⟩
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  dsimp only [released] at releasedTags lookup newNode oldNodes
  rw [childEq] at tags releasedTags lookup newNode oldNodes
  exact ⟨tags,releasedTags,lookup,newNode,oldNodes⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWritableSharedMetadata
