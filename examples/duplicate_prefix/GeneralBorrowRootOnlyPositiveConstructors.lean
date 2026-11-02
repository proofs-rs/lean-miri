import duplicate_prefix.GeneralBorrowRootOnlySharedFrames
import duplicate_prefix.GeneralBorrowPartitionShared
import duplicate_prefix.GeneralBorrowPartitionDefault
namespace DuplicatePrefix.GeneralBorrowRootOnlyPositiveConstructors
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowRootOnlyConstructorFrames DuplicatePrefix.GeneralBorrowRootOnlySharedFrames DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The real positive Default append constructor preserves root-only exposure,
Unique root storage and the exact per-location cache, after its actual SIFA scan. -/
theorem default_append (input : GeneralBorrowFreshMetadataChildDefault.Input) (cache : ExposedCache)
    (only : RootOnly input.tree input.parent)
    (initial : Every (LocationInvariant cache input.parent) input.tree.locations) :
    RootOnly (GeneralBorrowFreshMetadataChildDefault.result input) input.parent ∧
    Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildDefault.result input).locations := by
  have different := GeneralBorrowFreshNode.parent_not_fresh input.tree.nodes
    (GeneralBorrowFreshMetadataChildDefault.index input) input.parent input.parentNode
    (GeneralBorrowFreshMetadataChildDefault.at_end input) input.parentPresent
  have stageOnly : RootOnly (GeneralBorrowFreshMetadataChildDefault.stage input) input.parent := by
    simpa only [RootOnly,GeneralBorrowFreshMetadataChildDefault.stage,GeneralBorrowFreshMetadataChildAttach.staged]
      using attach input.tree input.parent (GeneralBorrowFreshMetadataChildDefault.index input) input.parentNode
        (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) only rfl
  have installed : Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildDefault.stage input).locations := by
    simpa only [GeneralBorrowFreshMetadataChildDefault.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshMetadataChildDefault.locations]
      using materialize input.tree.locations input.parent (GeneralBorrowFreshMetadataChildDefault.index input) different cache
      GeneralBorrowFreshDefaultChild.inside (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds initial
  let P := fun tree : BorrowTree => RootOnly tree input.parent ∧ Every (LocationInvariant cache input.parent) tree.locations
  have result : P (sourceUpdateSifa (GeneralBorrowFreshMetadataChildDefault.stage input) input.parent .Read).1 :=
    sifa (GeneralBorrowFreshMetadataChildDefault.stage input) input.parent input.parent .Read cache stageOnly installed
  exact (congrArg P (GeneralBorrowFreshMetadataChildDefault.tree_eq input)).mpr result

/-- The real positive Default reused-slot constructor has the same exact frame;
the slot is selected by its actual allocator certificate. -/
theorem default_reuse (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input) (cache : ExposedCache)
    (only : RootOnly input.tree input.parent)
    (initial : Every (LocationInvariant cache input.parent) input.tree.locations) :
    RootOnly (GeneralBorrowFreshMetadataChildDefaultReuse.result input) input.parent ∧
    Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildDefaultReuse.result input).locations := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant input.tree.nodes
    input.index input.parent input.parentNode input.vacant input.parentPresent
  have stageOnly : RootOnly (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) input.parent := by
    simpa only [RootOnly,GeneralBorrowFreshMetadataChildDefaultReuse.index,GeneralBorrowFreshMetadataChildDefaultReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged]
      using attach input.tree input.parent input.index input.parentNode
        (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) only rfl
  have installed : Every (LocationInvariant cache input.parent) (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).locations := by
    simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.index,GeneralBorrowFreshMetadataChildDefaultReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshMetadataChildDefaultReuse.locations]
      using materialize input.tree.locations input.parent input.index different cache
      GeneralBorrowFreshDefaultChild.inside (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds initial
  let P := fun tree : BorrowTree => RootOnly tree input.parent ∧ Every (LocationInvariant cache input.parent) tree.locations
  have result : P (sourceUpdateSifa (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) input.parent .Read).1 :=
    sifa (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) input.parent input.parent .Read cache stageOnly installed
  exact (congrArg P (GeneralBorrowFreshMetadataChildDefaultReuse.tree_eq input)).mpr result

/-- The actual positive Shared constructor selects append or reuse internally;
root-only exposure and exact root cache/Unique storage are preserved. -/
theorem shared (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (requested : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    RootOnly (GeneralBorrowPartitionShared.operation tree s.node.tag tag offset len).tree root ∧
    Every (LocationInvariant cache root) (GeneralBorrowPartitionShared.operation tree s.node.tag tag offset len).tree.locations := by
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
    let input : GeneralBorrowFreshMetadataChildShared.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      noFree := available,aligned := aligned,fits := by rw [aligned];change tree.nodes.size ≤ _;omega
      isProtected := false,offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact append input cache only initial
  | some index =>
    have member := Array.mem_of_back? available
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      index := index,available := available,valid := s.allocator.pool.bounded index member
      vacant := s.allocator.pool.vacant index member,parentSlack := slack
      isProtected := false,offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact reuse input cache only initial

/-- The actual positive Default constructor selects append or reuse internally;
root-only exposure and exact root cache/Unique storage are preserved. -/
theorem reserve (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (requested : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    RootOnly (GeneralBorrowPartitionDefault.operation tree s.node.tag tag offset len).tree root ∧
    Every (LocationInvariant cache root) (GeneralBorrowPartitionDefault.operation tree s.node.tag tag offset len).tree.locations := by
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
    let input : GeneralBorrowFreshMetadataChildDefault.Input := {
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
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      index := index,available := available,valid := s.allocator.pool.bounded index member
      vacant := s.allocator.pool.vacant index member,parentSlack := slack
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact default_reuse input cache only initial

end DuplicatePrefix.GeneralBorrowRootOnlyPositiveConstructors
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyPositiveConstructors." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only positive constructor dependency {dependency}"
