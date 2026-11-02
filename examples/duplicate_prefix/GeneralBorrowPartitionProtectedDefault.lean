import duplicate_prefix.GeneralBorrowProtectedDefaultInvariant
import duplicate_prefix.GeneralBorrowPartialProtectedRange
import duplicate_prefix.GeneralBorrowPartialSharedClean
import duplicate_prefix.GeneralBorrowGeneratedReuseStarShape

namespace DuplicatePrefix.GeneralBorrowPartitionProtectedDefault
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- Actual protected mutable constructor, selecting real append or reuse.
The resulting borrow tree is independent of the separately tracked protectors. -/
def operation (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true

/-- The actual protected constructor forms metadata/resources and a
COUNTERFACTUAL empty-protector root State. This does not permit root Write while
the child's real protector is held. A lifecycle theorem must discharge actual
protector removal before treating this State's ownership as real root ownership.
Constructor success and all append/reuse slot facts are derived. -/
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
    let input : GeneralBorrowFreshMetadataChildMutable.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      noFree := available,aligned := aligned,fits := by rw [aligned];change tree.nodes.size ≤ _;omega
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    have output := GeneralBorrowFreshMetadataChildMutable.append input
    have rawStar := GeneralBorrowGeneratedStarShape.attached_star tree root s.node
      (GeneralBorrowFreshMetadataChildMutable.index input) (GeneralBorrowFreshChild.child tag root) s.star
      (GeneralBorrowFreshMetadataChildMutable.at_end input) rfl rfl
    have notRoot := GeneralBorrowFreshNode.parent_not_fresh tree.nodes (GeneralBorrowFreshMetadataChildMutable.index input) root s.node
      (GeneralBorrowFreshMetadataChildMutable.at_end input) s.star.present
    have rawSize : (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildMutable.index input) root s.node
        (GeneralBorrowFreshChild.child tag root)).nodes.data.size = tree.nodes.data.size+1 := by
      have rootInserted := (GeneralBorrowFreshLocation.get_other tree.nodes (GeneralBorrowFreshMetadataChildMutable.index input) root
        (GeneralBorrowFreshChild.child tag root) notRoot).trans s.star.present
      have count := GeneralBorrowNodeUpdate.insert_existing_size
        (tree.nodes.insert (GeneralBorrowFreshMetadataChildMutable.index input) (GeneralBorrowFreshChild.child tag root)) root s.node
        (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildMutable.index input)) rootInserted
      have appended := GeneralBorrowFreshNode.append_size tree.nodes (GeneralBorrowFreshMetadataChildMutable.index input)
        (GeneralBorrowFreshChild.child tag root) (GeneralBorrowFreshMetadataChildMutable.at_end input)
      simpa only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowFreshGraph.updatedParent,UniValMap.size] using count.trans appended
    have rawLeaf := GeneralBorrowFreshGraph.new_lookup tree (GeneralBorrowFreshMetadataChildMutable.index input) root s.node
      (GeneralBorrowFreshChild.child tag root) (GeneralBorrowFreshMetadataChildMutable.at_end input) s.star.present
    have rawFit : (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildMutable.index input) root s.node
        (GeneralBorrowFreshChild.child tag root)).nodes.data.size ≤ 4294967296 := by rw [rawSize];change tree.nodes.data.size+5 ≤ _ at room;omega
    have rawOwned := GeneralBorrowPartialProtectedRange.owned tree root (GeneralBorrowFreshMetadataChildMutable.index input) s.node tag
      s.star.present s.star.parentless notRoot rawStar rawLeaf rawFit
      (by intro position valid different;rw [rawSize] at valid;have endEq : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input;omega)
      (Size.ofBytes offset) (Size.ofBytes len) well bounds s.owned
      (s.clean _ (by
        have endEq : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
        unfold UniValMap.get;rw [endEq,Array.getElem?_eq_none (Nat.le_refl _)]))
    have stageLocations : (GeneralBorrowFreshMetadataChildMutable.stage input).locations =
        (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
          (fun _ location => GeneralBorrowFreshMaterialization.materialized location (GeneralBorrowFreshMetadataChildMutable.index input) GeneralBorrowFreshChild.inside)).state := rfl
    have stageNodes : (GeneralBorrowFreshMetadataChildMutable.stage input).nodes =
        (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildMutable.index input) root s.node (GeneralBorrowFreshChild.child tag root)).nodes := by
      simp only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,input,GeneralBorrowFreshMetadataChildMutable.index]
    have stageOwned : GeneralRangeMapState.Every
        (GeneralBorrowRange.LocationOwned (GeneralBorrowFreshMetadataChildMutable.stage input) {} root .Write)
        (GeneralBorrowFreshMetadataChildMutable.stage input).locations := by
      rw [stageLocations]
      intro position valid
      exact GeneralBorrowPartialProtectedRange.owned_nodes
        (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildMutable.index input) root s.node (GeneralBorrowFreshChild.child tag root))
        (GeneralBorrowFreshMetadataChildMutable.stage input) stageNodes root _ (rawOwned position valid)
    have stagedStar := GeneralBorrowGeneratedStarShape.of_nodes _ (GeneralBorrowFreshMetadataChildMutable.stage input) root
      (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildMutable.index input)) stageNodes rawStar
    obtain ⟨node,star⟩ := GeneralBorrowGeneratedStarShape.shaped (GeneralBorrowFreshMetadataChildMutable.stage input) (GeneralBorrowFreshMetadataChildMutable.result input)
      root (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildMutable.index input)) (GeneralBorrowFreshMetadataChildMutable.shape input) stagedStar
    have postOwned := GeneralBorrowFreshOwnership.sifa_preserves (GeneralBorrowFreshMetadataChildMutable.stage input) input.parent .None {} root .Write stageOwned
    rw [←GeneralBorrowFreshMetadataChildMutable.tree_eq input] at postOwned
    have rawClean := GeneralBorrowPartialSharedClean.staged_generic tree (GeneralBorrowFreshMetadataChildMutable.index input) root s.node
      (GeneralBorrowFreshChild.child tag root) (GeneralBorrowFreshMetadataChildMutable.mapping input)
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location (GeneralBorrowFreshMetadataChildMutable.index input) GeneralBorrowFreshChild.inside)).state
      (fun query vacant different => GeneralBorrowFreshFutureClean.modified tree.locations (GeneralBorrowFreshMetadataChildMutable.index input) query
        (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshChild.inside different well bounds (s.clean query vacant))
    have stageClean : GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowFreshMetadataChildMutable.stage input) := by
      simpa only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildMutable.locations] using rawClean
    have postClean := GeneralBorrowPartialSharedClean.shaped (GeneralBorrowFreshMetadataChildMutable.stage input) (GeneralBorrowFreshMetadataChildMutable.result input) (GeneralBorrowFreshMetadataChildMutable.shape input) stageClean
    have locationFrame := GeneralBorrowProtectedDefaultInvariant.Append.geometry input
    have stagedRoot : (GeneralBorrowFreshMetadataChildMutable.stage input).nodeAt root =
        some (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildMutable.index input)) := by
      simpa only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
        GeneralBorrowFreshGraph.parent_lookup tree (GeneralBorrowFreshMetadataChildMutable.index input) root s.node
          (GeneralBorrowFreshChild.child tag root)
          (GeneralBorrowFreshMetadataChildMutable.at_end input) s.star.present
    obtain ⟨old,oldPresent,nodeTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields
      (GeneralBorrowFreshMetadataChildMutable.result input) (GeneralBorrowFreshMetadataChildMutable.stage input)
      (GeneralBorrowFreshMetadataChildMutable.shape input).symm root node star.present
    have oldEq : old = GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildMutable.index input) :=
      Option.some.inj (oldPresent.symm.trans stagedRoot)
    have tagEq : node.tag = s.node.tag := by rw [←nodeTag,oldEq];rfl
    have size : (operation tree s.node.tag tag offset len).tree.nodes.size = tree.nodes.size+1 := output.size
    refine ⟨output.success,⟨⟨⟨node,s.nonzero,star,output.roots.trans s.roots,locationFrame.2.trans s.capacity,locationFrame.1,postOwned,
      GeneralBorrowProtectedDefaultInvariant.Append.preserves input s.allocator,postClean,?_⟩,tagEq⟩⟩,by omega,?_⟩
    · rw [size];omega
    · intro future different old
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildMutable.result input).tagMapping future
      rw [output.mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future _ _ old different
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
    have output := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    have rawStar := GeneralBorrowGeneratedReuseStarShape.attached_star tree root s.node index (GeneralBorrowFreshChild.child tag root) s.star input.vacant rfl rfl
    have notRoot := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index root s.node input.vacant s.star.present
    have rawSize := GeneralBorrowFreshReuseState.attached_size tree index root s.node (GeneralBorrowFreshChild.child tag root)
      input.valid input.vacant s.star.present
    have rawLeaf := GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index root s.node (GeneralBorrowFreshChild.child tag root) input.vacant s.star.present
    have rawFit : (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshChild.child tag root)).nodes.data.size ≤ 4294967296 := by
      rw [rawSize];change tree.nodes.data.size+5 ≤ _ at room;omega
    have rawOwned := GeneralBorrowPartialProtectedRange.owned tree root index s.node tag s.star.present s.star.parentless notRoot
      rawStar rawLeaf rawFit (by intro position valid different;rw [rawSize] at valid;exact valid)
      (Size.ofBytes offset) (Size.ofBytes len) well bounds s.owned (s.clean index input.vacant)
    have stageLocations : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).locations =
        (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
          (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)).state := rfl
    have stageNodes : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodes =
        (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshChild.child tag root)).nodes := by
      simp only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,input,GeneralBorrowFreshMetadataChildMutableReuse.index]
    have stageOwned : GeneralRangeMapState.Every
        (GeneralBorrowRange.LocationOwned (GeneralBorrowFreshMetadataChildMutableReuse.stage input) {} root .Write)
        (GeneralBorrowFreshMetadataChildMutableReuse.stage input).locations := by
      rw [stageLocations]
      intro position valid
      exact GeneralBorrowPartialProtectedRange.owned_nodes
        (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshChild.child tag root))
        (GeneralBorrowFreshMetadataChildMutableReuse.stage input) stageNodes root _ (rawOwned position valid)
    have stagedStar := GeneralBorrowGeneratedStarShape.of_nodes _ (GeneralBorrowFreshMetadataChildMutableReuse.stage input) root
      (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildMutableReuse.index input)) stageNodes rawStar
    obtain ⟨node,star⟩ := GeneralBorrowGeneratedStarShape.shaped (GeneralBorrowFreshMetadataChildMutableReuse.stage input) (GeneralBorrowFreshMetadataChildMutableReuse.result input)
      root (GeneralBorrowFreshGraph.updatedParent s.node (GeneralBorrowFreshMetadataChildMutableReuse.index input)) (GeneralBorrowFreshMetadataChildMutableReuse.shape input) stagedStar
    have postOwned := GeneralBorrowFreshOwnership.sifa_preserves (GeneralBorrowFreshMetadataChildMutableReuse.stage input) input.parent .None {} root .Write stageOwned
    rw [←GeneralBorrowFreshMetadataChildMutableReuse.tree_eq input] at postOwned
    have rawClean := GeneralBorrowPartialSharedClean.staged_generic tree index root s.node
      (GeneralBorrowFreshChild.child tag root) (GeneralBorrowFreshMetadataChildMutableReuse.mapping input)
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)).state
      (fun query vacant different => GeneralBorrowFreshFutureClean.modified tree.locations index query
        (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshChild.inside different well bounds (s.clean query vacant))
    have stageClean : GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowFreshMetadataChildMutableReuse.stage input) := by
      simpa only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildMutableReuse.locations,GeneralBorrowFreshMetadataChildMutableReuse.index,input] using rawClean
    have postClean := GeneralBorrowPartialSharedClean.shaped (GeneralBorrowFreshMetadataChildMutableReuse.stage input) (GeneralBorrowFreshMetadataChildMutableReuse.result input) (GeneralBorrowFreshMetadataChildMutableReuse.shape input) stageClean
    have locationFrame := GeneralBorrowProtectedDefaultInvariant.Reuse.geometry input
    have stagedRoot : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodeAt root =
        some (GeneralBorrowFreshGraph.updatedParent s.node index) := by
      simpa only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildMutableReuse.index,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
        GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index root s.node
          (GeneralBorrowFreshChild.child tag root) input.vacant s.star.present
    obtain ⟨old,oldPresent,nodeTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields
      (GeneralBorrowFreshMetadataChildMutableReuse.result input) (GeneralBorrowFreshMetadataChildMutableReuse.stage input)
      (GeneralBorrowFreshMetadataChildMutableReuse.shape input).symm root node star.present
    have oldEq : old = GeneralBorrowFreshGraph.updatedParent s.node index :=
      Option.some.inj (oldPresent.symm.trans stagedRoot)
    have tagEq : node.tag = s.node.tag := by rw [←nodeTag,oldEq];rfl
    have size : (operation tree s.node.tag tag offset len).tree.nodes.size = tree.nodes.size := output.size
    refine ⟨output.success,⟨⟨⟨node,s.nonzero,star,output.roots.trans s.roots,locationFrame.2.trans s.capacity,locationFrame.1,postOwned,
      GeneralBorrowProtectedDefaultInvariant.Reuse.preserves input s.allocator,postClean,?_⟩,tagEq⟩⟩,by omega,?_⟩
    · rw [size];exact s.room
    · intro future different old
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildMutableReuse.result input).tagMapping future
      rw [output.mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future _ _ old different

end DuplicatePrefix.GeneralBorrowPartitionProtectedDefault
