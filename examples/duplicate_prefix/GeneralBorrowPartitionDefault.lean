import duplicate_prefix.GeneralBorrowDefaultInvariant
import duplicate_prefix.GeneralBorrowPartialDefaultRange
import duplicate_prefix.GeneralBorrowPartialSharedClean
import duplicate_prefix.GeneralBorrowGeneratedReuseStarShape

namespace DuplicatePrefix.GeneralBorrowPartitionDefault
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- The actual partial-range Default mutable reservation constructor, selecting append or reuse itself. -/
def operation (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false

/-- Form a recurring state after the actual Default mutable reservation constructor. Every physical
slot condition and completion fact is derived from coherent initial resources. -/
theorem reserve (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
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
    let input : GeneralBorrowFreshMetadataChildDefault.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      noFree := available,aligned := aligned,fits := by rw [aligned];change tree.nodes.size ≤ _;omega
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    have output := GeneralBorrowFreshMetadataChildDefault.append input
    have rawStar := GeneralBorrowGeneratedStarShape.attached_star tree root s.node
      (GeneralBorrowFreshMetadataChildDefault.index input) (GeneralBorrowFreshDefaultChild.child tag root) s.star
      (GeneralBorrowFreshMetadataChildDefault.at_end input) rfl rfl
    have notRoot := GeneralBorrowFreshNode.parent_not_fresh tree.nodes (GeneralBorrowFreshMetadataChildDefault.index input) root s.node
      (GeneralBorrowFreshMetadataChildDefault.at_end input) s.star.present
    have rawSize : (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildDefault.index input) root s.node
        (GeneralBorrowFreshDefaultChild.child tag root)).nodes.data.size = tree.nodes.data.size+1 := by
      have rootInserted := (GeneralBorrowFreshLocation.get_other tree.nodes (GeneralBorrowFreshMetadataChildDefault.index input) root
        (GeneralBorrowFreshDefaultChild.child tag root) notRoot).trans s.star.present
      have count := GeneralBorrowNodeUpdate.insert_existing_size
        (tree.nodes.insert (GeneralBorrowFreshMetadataChildDefault.index input) (GeneralBorrowFreshDefaultChild.child tag root)) root s.node
        (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildDefault.index input)) rootInserted
      have appended := GeneralBorrowFreshNode.append_size tree.nodes (GeneralBorrowFreshMetadataChildDefault.index input)
        (GeneralBorrowFreshDefaultChild.child tag root) (GeneralBorrowFreshMetadataChildDefault.at_end input)
      simpa only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowFreshGraph.updatedParent,UniValMap.size] using count.trans appended
    have rawLeaf := GeneralBorrowFreshGraph.new_lookup tree (GeneralBorrowFreshMetadataChildDefault.index input) root s.node
      (GeneralBorrowFreshDefaultChild.child tag root) (GeneralBorrowFreshMetadataChildDefault.at_end input) s.star.present
    have rawFit : (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildDefault.index input) root s.node
        (GeneralBorrowFreshDefaultChild.child tag root)).nodes.data.size ≤ 4294967296 := by rw [rawSize];change tree.nodes.data.size+5 ≤ _ at room;omega
    have rawOwned := GeneralBorrowPartialDefaultRange.owned tree root (GeneralBorrowFreshMetadataChildDefault.index input) s.node tag
      s.star.present s.star.parentless notRoot rawStar rawLeaf rawFit
      (by intro position valid different;rw [rawSize] at valid;have endEq : (GeneralBorrowFreshMetadataChildDefault.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input;omega)
      (Size.ofBytes offset) (Size.ofBytes len) well bounds s.owned
      (s.clean _ (by
        have endEq : (GeneralBorrowFreshMetadataChildDefault.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
        unfold UniValMap.get;rw [endEq,Array.getElem?_eq_none (Nat.le_refl _)]))
    have stageLocations : (GeneralBorrowFreshMetadataChildDefault.stage input).locations =
        (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
          (fun _ location => GeneralBorrowFreshMaterialization.materialized location (GeneralBorrowFreshMetadataChildDefault.index input) GeneralBorrowFreshDefaultChild.inside)).state := rfl
    have stageNodes : (GeneralBorrowFreshMetadataChildDefault.stage input).nodes =
        (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildDefault.index input) root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes := by
      simp only [GeneralBorrowFreshMetadataChildDefault.stage,GeneralBorrowFreshMetadataChildAttach.staged,input,GeneralBorrowFreshMetadataChildDefault.index]
    have stageOwned : GeneralRangeMapState.Every
        (GeneralBorrowRange.LocationOwned (GeneralBorrowFreshMetadataChildDefault.stage input) {} root .Write)
        (GeneralBorrowFreshMetadataChildDefault.stage input).locations := by
      rw [stageLocations]
      intro position valid
      exact GeneralBorrowPartialDefaultRange.owned_nodes
        (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildDefault.index input) root s.node (GeneralBorrowFreshDefaultChild.child tag root))
        (GeneralBorrowFreshMetadataChildDefault.stage input) stageNodes root _ (rawOwned position valid)
    have stagedStar := GeneralBorrowGeneratedStarShape.of_nodes _ (GeneralBorrowFreshMetadataChildDefault.stage input) root
      (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildDefault.index input)) stageNodes rawStar
    obtain ⟨node,star⟩ := GeneralBorrowGeneratedStarShape.shaped (GeneralBorrowFreshMetadataChildDefault.stage input) (GeneralBorrowFreshMetadataChildDefault.result input)
      root (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildDefault.index input)) (GeneralBorrowFreshMetadataChildDefault.shape input) stagedStar
    have postOwned := GeneralBorrowFreshOwnership.sifa_preserves (GeneralBorrowFreshMetadataChildDefault.stage input) input.parent .Read {} root .Write stageOwned
    rw [←GeneralBorrowFreshMetadataChildDefault.tree_eq input] at postOwned
    have rawClean := GeneralBorrowPartialSharedClean.staged_generic tree (GeneralBorrowFreshMetadataChildDefault.index input) root s.node
      (GeneralBorrowFreshDefaultChild.child tag root) (GeneralBorrowFreshMetadataChildDefault.mapping input)
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location (GeneralBorrowFreshMetadataChildDefault.index input) GeneralBorrowFreshDefaultChild.inside)).state
      (fun query vacant different => GeneralBorrowFreshFutureClean.modified tree.locations (GeneralBorrowFreshMetadataChildDefault.index input) query
        (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside different well bounds (s.clean query vacant))
    have stageClean : GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowFreshMetadataChildDefault.stage input) := by
      simpa only [GeneralBorrowFreshMetadataChildDefault.stage,GeneralBorrowFreshMetadataChildDefault.locations] using rawClean
    have postClean := GeneralBorrowPartialSharedClean.shaped (GeneralBorrowFreshMetadataChildDefault.stage input) (GeneralBorrowFreshMetadataChildDefault.result input) (GeneralBorrowFreshMetadataChildDefault.shape input) stageClean
    have locationFrame := GeneralBorrowDefaultInvariant.Append.geometry input
    have stagedRoot : (GeneralBorrowFreshMetadataChildDefault.stage input).nodeAt root =
        some (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildDefault.index input)) := by
      simpa only [GeneralBorrowFreshMetadataChildDefault.stage,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
        GeneralBorrowFreshGraph.parent_lookup tree (GeneralBorrowFreshMetadataChildDefault.index input) root s.node
          (GeneralBorrowFreshDefaultChild.child tag root)
          (GeneralBorrowFreshMetadataChildDefault.at_end input) s.star.present
    obtain ⟨old,oldPresent,nodeTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields
      (GeneralBorrowFreshMetadataChildDefault.result input) (GeneralBorrowFreshMetadataChildDefault.stage input)
      (GeneralBorrowFreshMetadataChildDefault.shape input).symm root node star.present
    have oldEq : old = GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildDefault.index input) :=
      Option.some.inj (oldPresent.symm.trans stagedRoot)
    have tagEq : node.tag = s.node.tag := by rw [←nodeTag,oldEq];rfl
    have size : (operation tree s.node.tag tag offset len).tree.nodes.size = tree.nodes.size+1 := output.size
    refine ⟨output.success,⟨⟨⟨node,s.nonzero,star,output.roots.trans s.roots,locationFrame.2.trans s.capacity,locationFrame.1,postOwned,
      GeneralBorrowDefaultInvariant.Append.preserves input s.allocator,postClean,?_⟩,tagEq⟩⟩,by omega,?_⟩
    · rw [size];omega
    · intro future different old
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildDefault.result input).tagMapping future
      rw [output.mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future _ _ old different
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
    have output := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
    have rawStar := GeneralBorrowGeneratedReuseStarShape.attached_star tree root s.node index (GeneralBorrowFreshDefaultChild.child tag root) s.star input.vacant rfl rfl
    have notRoot := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index root s.node input.vacant s.star.present
    have rawSize := GeneralBorrowFreshReuseState.attached_size tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)
      input.valid input.vacant s.star.present
    have rawLeaf := GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root) input.vacant s.star.present
    have rawFit : (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.data.size ≤ 4294967296 := by
      rw [rawSize];change tree.nodes.data.size+5 ≤ _ at room;omega
    have rawOwned := GeneralBorrowPartialDefaultRange.owned tree root index s.node tag s.star.present s.star.parentless notRoot
      rawStar rawLeaf rawFit (by intro position valid different;rw [rawSize] at valid;exact valid)
      (Size.ofBytes offset) (Size.ofBytes len) well bounds s.owned (s.clean index input.vacant)
    have stageLocations : (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).locations =
        (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
          (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside)).state := rfl
    have stageNodes : (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).nodes =
        (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes := by
      simp only [GeneralBorrowFreshMetadataChildDefaultReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,input,GeneralBorrowFreshMetadataChildDefaultReuse.index]
    have stageOwned : GeneralRangeMapState.Every
        (GeneralBorrowRange.LocationOwned (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) {} root .Write)
        (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).locations := by
      rw [stageLocations]
      intro position valid
      exact GeneralBorrowPartialDefaultRange.owned_nodes
        (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root))
        (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) stageNodes root _ (rawOwned position valid)
    have stagedStar := GeneralBorrowGeneratedStarShape.of_nodes _ (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) root
      (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildDefaultReuse.index input)) stageNodes rawStar
    obtain ⟨node,star⟩ := GeneralBorrowGeneratedStarShape.shaped (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) (GeneralBorrowFreshMetadataChildDefaultReuse.result input)
      root (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildDefaultReuse.index input)) (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) stagedStar
    have postOwned := GeneralBorrowFreshOwnership.sifa_preserves (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) input.parent .Read {} root .Write stageOwned
    rw [←GeneralBorrowFreshMetadataChildDefaultReuse.tree_eq input] at postOwned
    have rawClean := GeneralBorrowPartialSharedClean.staged_generic tree index root s.node
      (GeneralBorrowFreshDefaultChild.child tag root) (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input)
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside)).state
      (fun query vacant different => GeneralBorrowFreshFutureClean.modified tree.locations index query
        (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside different well bounds (s.clean query vacant))
    have stageClean : GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) := by
      simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.stage,GeneralBorrowFreshMetadataChildDefaultReuse.locations,GeneralBorrowFreshMetadataChildDefaultReuse.index,input] using rawClean
    have postClean := GeneralBorrowPartialSharedClean.shaped (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) (GeneralBorrowFreshMetadataChildDefaultReuse.result input) (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) stageClean
    have locationFrame := GeneralBorrowDefaultInvariant.Reuse.geometry input
    have stagedRoot : (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).nodeAt root =
        some (GeneralBorrowFreshGraph.updatedParent s.node index) := by
      simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.stage,GeneralBorrowFreshMetadataChildDefaultReuse.index,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
        GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index root s.node
          (GeneralBorrowFreshDefaultChild.child tag root) input.vacant s.star.present
    obtain ⟨old,oldPresent,nodeTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields
      (GeneralBorrowFreshMetadataChildDefaultReuse.result input) (GeneralBorrowFreshMetadataChildDefaultReuse.stage input)
      (GeneralBorrowFreshMetadataChildDefaultReuse.shape input).symm root node star.present
    have oldEq : old = GeneralBorrowFreshGraph.updatedParent s.node index :=
      Option.some.inj (oldPresent.symm.trans stagedRoot)
    have tagEq : node.tag = s.node.tag := by rw [←nodeTag,oldEq];rfl
    have size : (operation tree s.node.tag tag offset len).tree.nodes.size = tree.nodes.size := output.size
    refine ⟨output.success,⟨⟨⟨node,s.nonzero,star,output.roots.trans s.roots,locationFrame.2.trans s.capacity,locationFrame.1,postOwned,
      GeneralBorrowDefaultInvariant.Reuse.preserves input s.allocator,postClean,?_⟩,tagEq⟩⟩,by omega,?_⟩
    · rw [size];exact s.room
    · intro future different old
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildDefaultReuse.result input).tagMapping future
      rw [output.mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future _ _ old different

end DuplicatePrefix.GeneralBorrowPartitionDefault
