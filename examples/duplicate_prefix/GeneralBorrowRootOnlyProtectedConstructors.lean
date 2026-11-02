import duplicate_prefix.GeneralBorrowRootOnlyPositiveConstructors
import duplicate_prefix.GeneralBorrowRootOnlyConstructorFlags
import duplicate_prefix.GeneralBorrowPartitionProtectedDefault
namespace DuplicatePrefix.GeneralBorrowRootOnlyProtectedConstructors
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowRootOnlyConstructorFrames DuplicatePrefix.GeneralBorrowRootOnlySharedFrames DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem default_append (input : GeneralBorrowFreshMetadataChildMutable.Input) (cache : ExposedCache)
    (only : RootOnly input.tree input.parent)
    (initial : Every (LocationInvariant cache input.parent) input.tree.locations) :
    RootOnly (GeneralBorrowFreshMetadataChildMutable.result input) input.parent ∧
    Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
  have different := GeneralBorrowFreshNode.parent_not_fresh input.tree.nodes
    (GeneralBorrowFreshMetadataChildMutable.index input) input.parent input.parentNode
    (GeneralBorrowFreshMetadataChildMutable.at_end input) input.parentPresent
  have stageOnly : RootOnly (GeneralBorrowFreshMetadataChildMutable.stage input) input.parent := by
    simpa only [RootOnly,GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged]
      using attach input.tree input.parent (GeneralBorrowFreshMetadataChildMutable.index input) input.parentNode
        (GeneralBorrowFreshChild.child input.newTag input.parent) only rfl
  have installed : Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildMutable.stage input).locations := by
    simpa only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshMetadataChildMutable.locations]
      using materialize input.tree.locations input.parent (GeneralBorrowFreshMetadataChildMutable.index input) different cache
      GeneralBorrowFreshChild.inside (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds initial
  let P := fun tree : BorrowTree => RootOnly tree input.parent ∧ Every (LocationInvariant cache input.parent) tree.locations
  have result : P (sourceUpdateSifa (GeneralBorrowFreshMetadataChildMutable.stage input) input.parent .None).1 :=
    sifa (GeneralBorrowFreshMetadataChildMutable.stage input) input.parent input.parent .None cache stageOnly installed
  exact (congrArg P (GeneralBorrowFreshMetadataChildMutable.tree_eq input)).mpr result

/-- The real positive Default reused-slot constructor has the same exact frame;
the slot is selected by its actual allocator certificate. -/
theorem default_reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) (cache : ExposedCache)
    (only : RootOnly input.tree input.parent)
    (initial : Every (LocationInvariant cache input.parent) input.tree.locations) :
    RootOnly (GeneralBorrowFreshMetadataChildMutableReuse.result input) input.parent ∧
    Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildMutableReuse.result input).locations := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant input.tree.nodes
    input.index input.parent input.parentNode input.vacant input.parentPresent
  have stageOnly : RootOnly (GeneralBorrowFreshMetadataChildMutableReuse.stage input) input.parent := by
    simpa only [RootOnly,GeneralBorrowFreshMetadataChildMutableReuse.index,GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged]
      using attach input.tree input.parent input.index input.parentNode
        (GeneralBorrowFreshChild.child input.newTag input.parent) only rfl
  have installed : Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildMutableReuse.stage input).locations := by
    simpa only [GeneralBorrowFreshMetadataChildMutableReuse.index,GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshMetadataChildMutableReuse.locations]
      using materialize input.tree.locations input.parent input.index different cache
      GeneralBorrowFreshChild.inside (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds initial
  let P := fun tree : BorrowTree => RootOnly tree input.parent ∧ Every (LocationInvariant cache input.parent) tree.locations
  have result : P (sourceUpdateSifa (GeneralBorrowFreshMetadataChildMutableReuse.stage input) input.parent .None).1 :=
    sifa (GeneralBorrowFreshMetadataChildMutableReuse.stage input) input.parent input.parent .None cache stageOnly installed
  exact (congrArg P (GeneralBorrowFreshMetadataChildMutableReuse.tree_eq input)).mpr result

theorem reserve (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (requested : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    RootOnly (GeneralBorrowPartitionProtectedDefault.operation tree s.node.tag tag offset len).tree root ∧
    Every (LocationInvariant cache root) (GeneralBorrowPartitionProtectedDefault.operation tree s.node.tag tag offset len).tree.locations := by
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have tagPresent := s.allocator.nodeTags root s.node s.star.present
  have well := s.well
  have bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact requested
  have slack : depth.depth root < tree.nodes.size := by
    have positive := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root s.node s.star.present
    have available : 0 < tree.nodes.data.size := by omega
    simpa [depth,GeneralBorrowStarCertificates.depth,UniValMap.size] using available
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree s.allocator.accounting available
    let input : GeneralBorrowFreshMetadataChildMutable.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      noFree := available,aligned := aligned,fits := by rw [aligned];change tree.nodes.size ≤ _;omega
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact default_append input cache only initial
  | some index =>
    have member := Array.mem_of_back? available
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      index := index,available := available,valid := s.allocator.pool.bounded index member
      vacant := s.allocator.pool.vacant index member,parentSlack := slack
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact default_reuse input cache only initial

namespace Flags
open GeneralBorrowRootOnlyConstructorFlags
theorem default_append (input : GeneralBorrowFreshMetadataChildMutable.Input) :
    ((GeneralBorrowFreshMetadataChildMutable.result input).nodes.get input.parent).map TreeNode.isExposed =
      (input.tree.nodes.get input.parent).map TreeNode.isExposed := by
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (GeneralBorrowFreshMetadataChildMutable.stage input)
    (GeneralBorrowFreshMetadataChildMutable.result input) (GeneralBorrowFreshMetadataChildMutable.exposure input) input.parent
  have root := attached_flag input.tree input.parent (GeneralBorrowFreshMetadataChildMutable.index input) input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent)
  have stage : ((GeneralBorrowFreshMetadataChildMutable.stage input).nodes.get input.parent).map TreeNode.isExposed = some input.parentNode.isExposed := by
    simpa only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged] using root
  rw [flags,stage,show input.tree.nodes.get input.parent = some input.parentNode from input.parentPresent]
  rfl

/-- Exact original-root flag after the real Default Reuse constructor. -/
theorem default_reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) :
    ((GeneralBorrowFreshMetadataChildMutableReuse.result input).nodes.get input.parent).map TreeNode.isExposed =
      (input.tree.nodes.get input.parent).map TreeNode.isExposed := by
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (GeneralBorrowFreshMetadataChildMutableReuse.stage input)
    (GeneralBorrowFreshMetadataChildMutableReuse.result input) (GeneralBorrowFreshMetadataChildMutableReuse.exposure input) input.parent
  have root := attached_flag input.tree input.parent (GeneralBorrowFreshMetadataChildMutableReuse.index input) input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent)
  have stage : ((GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodes.get input.parent).map TreeNode.isExposed = some input.parentNode.isExposed := by
    simpa only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged] using root
  rw [flags,stage,show input.tree.nodes.get input.parent = some input.parentNode from input.parentPresent]
  rfl

theorem reserve (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (requested : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295) :
    ((GeneralBorrowPartitionProtectedDefault.operation tree s.node.tag tag offset len).tree.nodes.get root).map TreeNode.isExposed =
      (tree.nodes.get root).map TreeNode.isExposed := by
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have tagPresent := s.allocator.nodeTags root s.node s.star.present
  have well := s.well
  have bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact requested
  have slack : depth.depth root < tree.nodes.size := by
    have positive := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root s.node s.star.present
    have available : 0 < tree.nodes.data.size := by omega
    simpa [depth,GeneralBorrowStarCertificates.depth,UniValMap.size] using available
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree s.allocator.accounting available
    let input : GeneralBorrowFreshMetadataChildMutable.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      noFree := available,aligned := aligned,fits := by rw [aligned];change tree.nodes.size ≤ _;omega
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact default_append input
  | some index =>
    have member := Array.mem_of_back? available
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      index := index,available := available,valid := s.allocator.pool.bounded index member
      vacant := s.allocator.pool.vacant index member,parentSlack := slack
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact default_reuse input


end Flags
end DuplicatePrefix.GeneralBorrowRootOnlyProtectedConstructors
