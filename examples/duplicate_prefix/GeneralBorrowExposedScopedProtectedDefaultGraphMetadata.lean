import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafRun
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultOld
import duplicate_prefix.GeneralBorrowFreshSharedPaths
import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableLeafPipeline
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableOld
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedDefaultGraphMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedScopedDefaultLeafConstructor (Resources)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem construct_nodeTags (input : GeneralBorrowFreshMetadataChildMutable.Input) (initial : GeneralBorrowGcAllocator.NodeTags input.tree) :
    GeneralBorrowGcAllocator.NodeTags (GeneralBorrowFreshMetadataChildMutable.result input) := by
  have staged:=GeneralBorrowSharedAllocatorInvariant.staged_tags input.tree (GeneralBorrowFreshMetadataChildMutable.index input) input.parent input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned
    (GeneralBorrowFreshMetadataChildMutable.locations input) input.parentPresent input.fresh initial
  have coherent : GeneralBorrowGcAllocator.NodeTags (GeneralBorrowFreshMetadataChildMutable.stage input) := by
    simpa only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildMutable.mapping] using staged
  exact GeneralBorrowSharedAllocatorInvariant.shape_tags _ _ (GeneralBorrowFreshMetadataChildMutable.shape input) coherent

theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes)
    (initialTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    let released := (child.tree.releaseProtector input.newTag protections).tree
    GeneralBorrowGcAllocator.NodeTags child.tree ∧ GeneralBorrowGcAllocator.NodeTags released ∧
      released.indexOfTag input.newTag=some (index input) ∧
      (∃ node,released.nodeAt (index input)=some node ∧ node.tag=input.newTag ∧ node.isExposed=false) ∧
      (∀ query node,input.tree.nodeAt query=some node →
        ∃ next,released.nodeAt query=some next ∧ next.tag=node.tag ∧ next.isExposed=node.isExposed) := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedDefaultLeafRun.prepare input protections selected head tail raw atBase full .VisitChildrenOfAccessed
  have readFrame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have preparedFrame : prepared.tree={input.tree with locations:=prepared.tree.locations} := by rw [treeEq];exact readFrame
  have preparedTags : GeneralBorrowGcAllocator.NodeTags prepared.tree := by
    rw [preparedFrame]
    exact initialTags
  let released := ((GeneralBorrowFreshMetadataChildMutable.result (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared)).releaseProtector input.newTag protections).tree
  have releaseFrame := GeneralBorrowStructuralReleaseGeometryFrame.release (GeneralBorrowFreshMetadataChildMutable.result (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared)) protections input.newTag
  have tags := construct_nodeTags (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared) preparedTags
  have releasedTags : GeneralBorrowGcAllocator.NodeTags released := by dsimp only [released];rw [releaseFrame];exact tags
  let metadata := GeneralBorrowFreshMetadataChildMutable.append (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared)
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
    obtain ⟨next,found,tag,exposed⟩ := GeneralBorrowFreshMetadataChildMutableOld.append (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared) query node preparedPresent
    exact ⟨next,by dsimp only [released];rw [releaseFrame];exact found,tag,exposed⟩
  have childEq : GeneralBorrowFreshMetadataChildMutable.result (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared) =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  dsimp only [released] at releasedTags lookup newNode oldNodes
  rw [childEq] at tags releasedTags lookup newNode oldNodes
  exact ⟨tags,releasedTags,lookup,newNode,oldNodes⟩
theorem attach (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail) (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes)
    (oldLocation newLocation : LocationTree) (tags : ProtectedTags) :
    let read:=input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child:=read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    GeneralBorrowFreshSharedPaths.Attach (source_normal_projection input.tree oldLocation tags).topology
      (source_normal_projection child.tree newLocation tags).topology input.parent.toNat (index input).toNat := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedDefaultLeafRun.prepare input protections selected head tail raw atBase full .VisitChildrenOfAccessed
  have readFrame:=GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have size : (source_normal_projection prepared.tree oldLocation tags).topology.nodes.size=(index prepared).toNat := by
    rw [at_end prepared]
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have forest : GeneralBorrowForest.Forest (source_normal_projection prepared.tree oldLocation tags).topology := by
    have same : (source_normal_projection prepared.tree oldLocation tags).topology=(source_normal_projection prepared.tree default protections).topology := by unfold_general_projection;rfl
    rw [same]
    exact preparedRaw.forest
  have data:=GeneralBorrowFreshSharedPaths.of_append _ _ prepared.parent.toNat ((GeneralBorrowFreshMetadataChildMutable.append (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared)).extension oldLocation newLocation tags) forest
  change GeneralBorrowFreshSharedPaths.Attach (source_normal_projection prepared.tree oldLocation tags).topology
    (source_normal_projection (GeneralBorrowFreshMetadataChildMutable.result (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared)) newLocation tags).topology prepared.parent.toNat (source_normal_projection prepared.tree oldLocation tags).topology.nodes.size at data
  rw [size] at data
  have childEq : GeneralBorrowFreshMetadataChildMutable.result (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared)=
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  rw [childEq,parentEq,indexEq,treeEq] at data
  have before : (source_normal_projection (input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree oldLocation tags).topology=
      (source_normal_projection input.tree oldLocation tags).topology := by
    rw [readFrame]
    rfl
  rw [before] at data
  exact data
end DuplicatePrefix.GeneralBorrowExposedScopedProtectedDefaultGraphMetadata
