import duplicate_prefix.GeneralBorrowReusableStar
import duplicate_prefix.GeneralBorrowGeneratedReuseStarShape
import duplicate_prefix.GeneralBorrowFullSharedReuseProfile

namespace DuplicatePrefix.GeneralBorrowReusableShared
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowReusableStar
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The actual full-slice shared constructor, selecting append or reuse itself. -/
def operation (tree : BorrowTree) (parentTag tag : BorTag) (capacity : UInt64) :=
  tree.newChild (Size.ofBytes 0) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes capacity) GeneralBorrowFreshAnchor.sharedState) .Frozen false

/-- Form a recurring state after the actual shared constructor. Every physical
slot condition and completion fact is derived from coherent initial resources. -/
theorem shared (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) :
    (operation tree s.node.tag tag capacity).outcome = .ok () ∧
    Nonempty {post : State (operation tree s.node.tag tag capacity).tree root capacity // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag tag capacity).tree.nodes.size ≤ tree.nodes.size+1 ∧
    (∀ future, tag ≠ future → GeneralBorrowTagMap.Fresh tree.tagMapping future →
      GeneralBorrowTagMap.Fresh (operation tree s.node.tag tag capacity).tree.tagMapping future) := by
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have tagPresent := s.allocator.nodeTags root s.node s.star.present
  have well : tree.locations.WellFormed := by
    rw [s.locations];simp [RangeMapNonempty.homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr s.nonzero]
  have bounds : (0 : UInt64).toNat+capacity.toNat ≤ tree.locations.size.bytes.toNat := by
    simp [s.locations,RangeMapNonempty.homogeneous,DedupRangeMap.size,Size.ofBytes]
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
      isProtected := false,offset := 0,len := capacity,nonzero := s.nonzero,well := well,bounds := bounds }
    have output := GeneralBorrowFreshMetadataChildShared.append input
    obtain ⟨node,star⟩ := GeneralBorrowGeneratedStarShape.append_star input s.star
    obtain ⟨location,locations,profile,cache⟩ := GeneralBorrowFullSharedAppend.append input s.location rfl s.locations s.star.parentless s.profile
    have stagedRoot : (GeneralBorrowFreshMetadataChildShared.stage input).nodeAt root =
        some (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildShared.index input)) := by
      simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
        GeneralBorrowFreshGraph.parent_lookup tree (GeneralBorrowFreshMetadataChildShared.index input) root s.node
          (GeneralBorrowFreshAnchor.sharedNode tag root)
          (GeneralBorrowFreshMetadataChildShared.at_end input) s.star.present
    obtain ⟨old,oldPresent,nodeTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields
      (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.stage input)
      (GeneralBorrowFreshMetadataChildShared.shape input).symm root node star.present
    have oldEq : old = GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildShared.index input) :=
      Option.some.inj (oldPresent.symm.trans stagedRoot)
    have tagEq : node.tag = s.node.tag := by rw [←nodeTag,oldEq];rfl
    have size : (operation tree s.node.tag tag capacity).tree.nodes.size = tree.nodes.size+1 := output.size
    refine ⟨output.success,⟨⟨⟨node,location,s.nonzero,star,output.roots.trans s.roots,locations,profile,
      GeneralBorrowSharedAllocatorInvariant.Append.preserves input s.allocator,?_⟩,tagEq⟩⟩,by omega,?_⟩
    · rw [size];omega
    · intro future different old
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildShared.result input).tagMapping future
      rw [output.mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future _ _ old different
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
      isProtected := false,offset := 0,len := capacity,nonzero := s.nonzero,well := well,bounds := bounds }
    have output := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    obtain ⟨node,star⟩ := GeneralBorrowGeneratedReuseStarShape.reuse_star input s.star
    obtain ⟨location,locations,profile,cache⟩ := GeneralBorrowFullSharedReuseProfile.reuse input s.location rfl s.locations s.profile
    have stagedRoot : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodeAt root =
        some (GeneralBorrowFreshGraph.updatedParent s.node index) := by
      simpa only [GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildSharedReuse.index,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
        GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index root s.node
          (GeneralBorrowFreshAnchor.sharedNode tag root) input.vacant s.star.present
    obtain ⟨old,oldPresent,nodeTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields
      (GeneralBorrowFreshMetadataChildSharedReuse.result input) (GeneralBorrowFreshMetadataChildSharedReuse.stage input)
      (GeneralBorrowFreshMetadataChildSharedReuse.shape input).symm root node star.present
    have oldEq : old = GeneralBorrowFreshGraph.updatedParent s.node index :=
      Option.some.inj (oldPresent.symm.trans stagedRoot)
    have tagEq : node.tag = s.node.tag := by rw [←nodeTag,oldEq];rfl
    have size : (operation tree s.node.tag tag capacity).tree.nodes.size = tree.nodes.size := output.size
    refine ⟨output.success,⟨⟨⟨node,location,s.nonzero,star,output.roots.trans s.roots,locations,profile,
      GeneralBorrowSharedAllocatorInvariant.Reuse.preserves input s.allocator,?_⟩,tagEq⟩⟩,by omega,?_⟩
    · rw [size];exact s.room
    · intro future different old
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildSharedReuse.result input).tagMapping future
      rw [output.mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future _ _ old different

end DuplicatePrefix.GeneralBorrowReusableShared
