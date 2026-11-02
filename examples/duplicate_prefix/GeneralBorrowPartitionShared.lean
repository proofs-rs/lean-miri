import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowPartialSharedClean
import duplicate_prefix.GeneralBorrowGeneratedReuseStarShape

namespace DuplicatePrefix.GeneralBorrowPartitionShared
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- The actual partial-range shared constructor, selecting append or reuse itself. -/
def operation (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen false

/-- Form a recurring state after the actual shared constructor. Every physical
slot condition and completion fact is derived from coherent initial resources. -/
theorem shared (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (requested : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) :
    (operation tree s.node.tag tag offset len).outcome = .ok () ∧
    Nonempty {post : State (operation tree s.node.tag tag offset len).tree root capacity // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag tag offset len).tree.nodes.size ≤ tree.nodes.size+1 ∧
    (∀ future, tag ≠ future → GeneralBorrowTagMap.Fresh tree.tagMapping future →
      GeneralBorrowTagMap.Fresh (operation tree s.node.tag tag offset len).tree.tagMapping future) := by
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
    have output := GeneralBorrowFreshMetadataChildShared.append input
    obtain ⟨node,star⟩ := GeneralBorrowGeneratedStarShape.append_star input s.star
    have rawStar := GeneralBorrowGeneratedStarShape.attached_star tree root s.node
      (GeneralBorrowFreshMetadataChildShared.index input) (GeneralBorrowFreshAnchor.sharedNode tag root) s.star
      (GeneralBorrowFreshMetadataChildShared.at_end input) rfl rfl
    have notRoot := GeneralBorrowFreshNode.parent_not_fresh tree.nodes (GeneralBorrowFreshMetadataChildShared.index input) root s.node
      (GeneralBorrowFreshMetadataChildShared.at_end input) s.star.present
    have rawSize : (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildShared.index input) root s.node
        (GeneralBorrowFreshAnchor.sharedNode tag root)).nodes.data.size = tree.nodes.data.size+1 := by
      have rootInserted := (GeneralBorrowFreshLocation.get_other tree.nodes (GeneralBorrowFreshMetadataChildShared.index input) root
        (GeneralBorrowFreshAnchor.sharedNode tag root) notRoot).trans s.star.present
      have count := GeneralBorrowNodeUpdate.insert_existing_size
        (tree.nodes.insert (GeneralBorrowFreshMetadataChildShared.index input) (GeneralBorrowFreshAnchor.sharedNode tag root)) root s.node
        (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildShared.index input)) rootInserted
      have appended := GeneralBorrowFreshNode.append_size tree.nodes (GeneralBorrowFreshMetadataChildShared.index input)
        (GeneralBorrowFreshAnchor.sharedNode tag root) (GeneralBorrowFreshMetadataChildShared.at_end input)
      simpa only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowFreshGraph.updatedParent,UniValMap.size] using count.trans appended
    have rawLeaf := GeneralBorrowFreshGraph.new_lookup tree (GeneralBorrowFreshMetadataChildShared.index input) root s.node
      (GeneralBorrowFreshAnchor.sharedNode tag root) (GeneralBorrowFreshMetadataChildShared.at_end input) s.star.present
    have rawFit : (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildShared.index input) root s.node
        (GeneralBorrowFreshAnchor.sharedNode tag root)).nodes.data.size ≤ 4294967296 := by rw [rawSize];change tree.nodes.data.size+5 ≤ _ at room;omega
    have rawOwned := GeneralBorrowPartialSharedRange.owned tree root (GeneralBorrowFreshMetadataChildShared.index input) s.node tag
      s.star.present s.star.parentless notRoot rawStar rawLeaf rawFit
      (by intro position valid different;rw [rawSize] at valid;have endEq : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input;omega)
      (Size.ofBytes offset) (Size.ofBytes len) well bounds s.owned
      (s.clean _ (by
        have endEq : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
        unfold UniValMap.get;rw [endEq,Array.getElem?_eq_none (Nat.le_refl _)]))
    have stageLocations : (GeneralBorrowFreshMetadataChildShared.stage input).locations =
        (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
          (fun _ location => GeneralBorrowFreshMaterialization.materialized location (GeneralBorrowFreshMetadataChildShared.index input) GeneralBorrowFreshAnchor.sharedState)).state := rfl
    have stageNodes : (GeneralBorrowFreshMetadataChildShared.stage input).nodes =
        (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildShared.index input) root s.node (GeneralBorrowFreshAnchor.sharedNode tag root)).nodes := by
      simp only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,input,GeneralBorrowFreshMetadataChildShared.index]
    have stageOwned : GeneralRangeMapState.Every
        (GeneralBorrowRange.LocationOwned (GeneralBorrowFreshMetadataChildShared.stage input) {} root .Write)
        (GeneralBorrowFreshMetadataChildShared.stage input).locations := by
      rw [stageLocations]
      intro position valid
      exact GeneralBorrowPartialSharedRange.owned_nodes
        (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildShared.index input) root s.node (GeneralBorrowFreshAnchor.sharedNode tag root))
        (GeneralBorrowFreshMetadataChildShared.stage input) stageNodes root _ (rawOwned position valid)
    have postOwned := GeneralBorrowFreshOwnership.sifa_preserves (GeneralBorrowFreshMetadataChildShared.stage input) input.parent .Read {} root .Write stageOwned
    rw [←GeneralBorrowFreshMetadataChildShared.tree_eq input] at postOwned
    have rawClean := GeneralBorrowPartialSharedClean.staged tree (GeneralBorrowFreshMetadataChildShared.index input) root s.node
      (GeneralBorrowFreshAnchor.sharedNode tag root) (GeneralBorrowFreshMetadataChildShared.mapping input) (Size.ofBytes offset) (Size.ofBytes len)
      notRoot well bounds s.clean
    have stageClean : GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowFreshMetadataChildShared.stage input) := by
      simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildShared.locations] using rawClean
    have postClean := GeneralBorrowPartialSharedClean.shaped (GeneralBorrowFreshMetadataChildShared.stage input) (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.shape input) stageClean
    have locationFrame := GeneralBorrowFreshSharedGeometry.append_frame input
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
    have size : (operation tree s.node.tag tag offset len).tree.nodes.size = tree.nodes.size+1 := output.size
    refine ⟨output.success,⟨⟨⟨node,s.nonzero,star,output.roots.trans s.roots,locationFrame.2.trans s.capacity,locationFrame.1,postOwned,
      GeneralBorrowSharedAllocatorInvariant.Append.preserves input s.allocator,postClean,?_⟩,tagEq⟩⟩,by omega,?_⟩
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
      isProtected := false,offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    have output := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    obtain ⟨node,star⟩ := GeneralBorrowGeneratedReuseStarShape.reuse_star input s.star
    have rawStar := GeneralBorrowGeneratedReuseStarShape.attached_star tree root s.node index (GeneralBorrowFreshAnchor.sharedNode tag root) s.star input.vacant rfl rfl
    have notRoot := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index root s.node input.vacant s.star.present
    have rawSize := GeneralBorrowFreshReuseState.attached_size tree index root s.node (GeneralBorrowFreshAnchor.sharedNode tag root)
      input.valid input.vacant s.star.present
    have rawLeaf := GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index root s.node (GeneralBorrowFreshAnchor.sharedNode tag root) input.vacant s.star.present
    have rawFit : (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshAnchor.sharedNode tag root)).nodes.data.size ≤ 4294967296 := by
      rw [rawSize];change tree.nodes.data.size+5 ≤ _ at room;omega
    have rawOwned := GeneralBorrowPartialSharedRange.owned tree root index s.node tag s.star.present s.star.parentless notRoot
      rawStar rawLeaf rawFit (by intro position valid different;rw [rawSize] at valid;exact valid)
      (Size.ofBytes offset) (Size.ofBytes len) well bounds s.owned (s.clean index input.vacant)
    have stageLocations : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).locations =
        (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
          (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshAnchor.sharedState)).state := rfl
    have stageNodes : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodes =
        (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshAnchor.sharedNode tag root)).nodes := by
      simp only [GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,input,GeneralBorrowFreshMetadataChildSharedReuse.index]
    have stageOwned : GeneralRangeMapState.Every
        (GeneralBorrowRange.LocationOwned (GeneralBorrowFreshMetadataChildSharedReuse.stage input) {} root .Write)
        (GeneralBorrowFreshMetadataChildSharedReuse.stage input).locations := by
      rw [stageLocations]
      intro position valid
      exact GeneralBorrowPartialSharedRange.owned_nodes
        (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshAnchor.sharedNode tag root))
        (GeneralBorrowFreshMetadataChildSharedReuse.stage input) stageNodes root _ (rawOwned position valid)
    have postOwned := GeneralBorrowFreshOwnership.sifa_preserves (GeneralBorrowFreshMetadataChildSharedReuse.stage input) input.parent .Read {} root .Write stageOwned
    rw [←GeneralBorrowFreshMetadataChildSharedReuse.tree_eq input] at postOwned
    have rawClean := GeneralBorrowPartialSharedClean.staged tree index root s.node (GeneralBorrowFreshAnchor.sharedNode tag root)
      (GeneralBorrowFreshMetadataChildSharedReuse.mapping input) (Size.ofBytes offset) (Size.ofBytes len) notRoot well bounds s.clean
    have stageClean : GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowFreshMetadataChildSharedReuse.stage input) := by
      simpa only [GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildSharedReuse.locations,GeneralBorrowFreshMetadataChildSharedReuse.index,input] using rawClean
    have postClean := GeneralBorrowPartialSharedClean.shaped (GeneralBorrowFreshMetadataChildSharedReuse.stage input) (GeneralBorrowFreshMetadataChildSharedReuse.result input) (GeneralBorrowFreshMetadataChildSharedReuse.shape input) stageClean
    have locationFrame := GeneralBorrowFreshSharedGeometry.reuse_frame input
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
    have size : (operation tree s.node.tag tag offset len).tree.nodes.size = tree.nodes.size := output.size
    refine ⟨output.success,⟨⟨⟨node,s.nonzero,star,output.roots.trans s.roots,locationFrame.2.trans s.capacity,locationFrame.1,postOwned,
      GeneralBorrowSharedAllocatorInvariant.Reuse.preserves input s.allocator,postClean,?_⟩,tagEq⟩⟩,by omega,?_⟩
    · rw [size];exact s.room
    · intro future different old
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildSharedReuse.result input).tagMapping future
      rw [output.mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future _ _ old different

end DuplicatePrefix.GeneralBorrowPartitionShared
