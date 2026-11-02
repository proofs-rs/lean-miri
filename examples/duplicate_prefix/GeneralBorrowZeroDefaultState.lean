import duplicate_prefix.GeneralBorrowZeroDefaultConstructor
import duplicate_prefix.GeneralBorrowZeroSharedState
import duplicate_prefix.GeneralBorrowPartialDefaultOwnership
import duplicate_prefix.GeneralBorrowPartialSharedClean
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant

namespace DuplicatePrefix.GeneralBorrowZeroDefaultState
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralBorrowGeneratedStarShape
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Package the real empty-range attachment before SIFA. The allocator branch
supplies only its Pool/Accounting equations, not operation success or ownership. -/
noncomputable def attached_state (tree : BorrowTree) (root index : UniIndex) (bytes : UInt64)
    (s : State tree root bytes) (tag : BorTag) (free : Array UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (vacant : tree.nodes.get index = none)
    (rawStar : Star (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root))
      root (GeneralBorrowFreshGraph.updatedParent s.node index))
    (leaf : (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodeAt index =
      some (GeneralBorrowFreshDefaultChild.child tag root))
    (fit : (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.data.size ≤ 4294967296)
    (oldPosition : ∀ position, position < (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.data.size →
      position ≠ index.toNat → position < tree.nodes.data.size)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool
      (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes free)
    (accounting : tree.tagMapping.mapping.size+1+free.size =
      (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.size)
    (room : (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.size+4 ≤ 4294967295) :
    State (GeneralBorrowFreshMetadataChildAttach.staged tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)
      ⟨tree.tagMapping.mapping.push (tag,index),free⟩ tree.locations) root bytes := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)
    ⟨tree.tagMapping.mapping.push (tag,index),free⟩ tree.locations
  have nodes : stage.nodes = (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes := by
    simp only [stage,GeneralBorrowFreshMetadataChildAttach.staged]
  have notRoot := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index root s.node vacant s.star.present
  have owned : GeneralRangeMapState.Every (GeneralBorrowRange.LocationOwned stage {} root .Write) tree.locations := by
    intro position valid
    apply GeneralBorrowPartialSharedRange.owned_nodes
      (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)) stage nodes root _
    refine ⟨⟨GeneralBorrowStarCertificates.forest _ root (GeneralBorrowFreshGraph.updatedParent s.node index) rawStar _ {} fit⟩,?_⟩
    apply GeneralBorrowPartialDefaultOwnership.location tree root index s.node tag s.star.present s.star.parentless notRoot rawStar.present leaf fit oldPosition
      tree.locations.entries[position].data tree.locations.entries[position].data
    · intro query different;rfl
    · exact Or.inl (s.clean index vacant position valid)
    · exact (s.owned position valid).2
  have stagePool : GeneralBorrowFreshAllocatorInvariant.Pool stage.nodes stage.tagMapping.deassigned := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged] using pool
  have stageUnique : GeneralBorrowGcAllocator.KeyUnique stage.tagMapping := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged] using
      GeneralBorrowGcAllocator.fresh_push_unique tree.tagMapping tag index free s.allocator.unique fresh
  have allocator : GeneralBorrowGcAllocator.Invariant stage := by
    refine ⟨stagePool,?_,stageUnique,?_⟩
    · simpa only [GeneralBorrowFreshStagePool.Accounting,stage,GeneralBorrowFreshMetadataChildAttach.staged,Array.size_push] using accounting
    · exact GeneralBorrowSharedAllocatorInvariant.staged_tags tree index root s.node
        (GeneralBorrowFreshDefaultChild.child tag root) tag rfl free tree.locations s.star.present fresh s.allocator.nodeTags
  exact ⟨GeneralBorrowFreshGraph.updatedParent s.node index,s.nonzero,
    GeneralBorrowGeneratedStarShape.of_nodes _ stage root _ nodes rawStar,s.roots,s.capacity,s.well,owned,allocator,
    GeneralBorrowPartialSharedClean.staged_generic tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)
      ⟨tree.tagMapping.mapping.push (tag,index),free⟩ tree.locations (fun query absent _ => s.clean query absent),by
        simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged] using room⟩

/-- The actual empty-range Default reservation constructor. It allocates a real node even
though it performs no inside-range permission materialization. -/
def operation (tree : BorrowTree) (parentTag tag : BorTag) (offset : UInt64) :=
  tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false

/-- Real zero-length Default reservation construction closes the recurring partition state
for either allocator branch. Offset bounds are unnecessary for this raw
constructor because its inside map is empty; a preceding access has its own
explicit range bounds. -/
theorem reserve (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) (offset : UInt64) :
    (operation tree s.node.tag tag offset).outcome = .ok () ∧
    Nonempty {post : State (operation tree s.node.tag tag offset).tree root bytes // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag tag offset).tree.nodes.size ≤ tree.nodes.size+1 ∧
    (∀ future, tag ≠ future → GeneralBorrowTagMap.Fresh tree.tagMapping future →
      GeneralBorrowTagMap.Fresh (operation tree s.node.tag tag offset).tree.tagMapping future) := by
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have tagged := s.allocator.nodeTags root s.node s.star.present
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree s.allocator.accounting available
    have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by rw [aligned];change tree.nodes.data.size+5 ≤ _ at room;change tree.nodes.data.size ≤ _;omega
    have atEnd : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    have vacant : tree.nodes.get index = none := by
      unfold UniValMap.get
      rw [atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have rawStar := GeneralBorrowGeneratedStarShape.attached_star tree root s.node index
      (GeneralBorrowFreshDefaultChild.child tag root) s.star atEnd rfl rfl
    have leaf := GeneralBorrowFreshGraph.new_lookup tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root) atEnd s.star.present
    have notRoot := GeneralBorrowFreshNode.parent_not_fresh tree.nodes index root s.node atEnd s.star.present
    have rawSize : (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.size = tree.nodes.size+1 := by
      have rootInserted := (GeneralBorrowFreshLocation.get_other tree.nodes index root (GeneralBorrowFreshDefaultChild.child tag root) notRoot).trans s.star.present
      have count := GeneralBorrowNodeUpdate.insert_existing_size (tree.nodes.insert index (GeneralBorrowFreshDefaultChild.child tag root)) root s.node
        (GeneralBorrowFreshGraph.updatedParent s.node index) rootInserted
      have appended := GeneralBorrowFreshNode.append_size tree.nodes index (GeneralBorrowFreshDefaultChild.child tag root) atEnd
      simpa only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,GeneralBorrowFreshGraph.updatedParent] using count.trans appended
    have dataSize : (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.data.size = tree.nodes.data.size+1 := rawSize
    have freeEmpty := Array.back?_eq_none_iff.mp available
    have pool : GeneralBorrowFreshAllocatorInvariant.Pool
        (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes tree.tagMapping.deassigned := by
      rw [freeEmpty]
      exact ⟨by simp,by simp,by simp⟩
    let rawState := attached_state tree root index bytes s tag tree.tagMapping.deassigned fresh vacant rawStar leaf
      (by rw [dataSize];change tree.nodes.data.size+5 ≤ _ at room;omega)
      (by intro position valid different;rw [dataSize] at valid;rw [atEnd] at different;omega)
      pool (by rw [freeEmpty,Array.size_empty,Nat.add_zero,rawSize,aligned];rfl)
      (by rw [rawSize];omega)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)
      ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ tree.locations
    have completed := GeneralBorrowZeroDefaultConstructor.append tree depth s.node.tag tag root s.node tagged s.star.present fresh available aligned fits offset
    have actual : (operation tree s.node.tag tag offset).tree = (sourceUpdateSifa stage root .Read).1 := by
      simpa only [operation,stage,GeneralBorrowFreshMetadataChildAttach.staged,index,GeneralBorrowFreshGraph.attached] using completed.2
    have closed := GeneralBorrowZeroSharedState.sifa stage root bytes rawState
    have rootTag : rawState.node.tag = s.node.tag := rfl
    rw [rootTag,←actual] at closed
    have shape := GeneralBorrowSifaView.preserves stage root .Read
    have size := GeneralBorrowFreshMetadata.node_size stage _ shape
    have mapping := GeneralBorrowFreshMetadata.mapping stage _ shape
    rw [←actual] at size mapping
    have stageSize : stage.nodes.size = tree.nodes.size+1 := by
      simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,UniValMap.size] using rawSize
    refine ⟨completed.1,closed.2,?_,?_⟩
    · rw [size,stageSize];omega
    · intro future different unused
      rw [mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future index tree.tagMapping.deassigned unused different
  | some index =>
    have member := Array.mem_of_back? available
    have bounded := s.allocator.pool.bounded index member
    have vacant := s.allocator.pool.vacant index member
    have rawStar := GeneralBorrowGeneratedReuseStarShape.attached_star tree root s.node index
      (GeneralBorrowFreshDefaultChild.child tag root) s.star vacant rfl rfl
    have leaf := GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root) vacant s.star.present
    have rawSize := GeneralBorrowFreshReuseState.attached_size tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root) bounded vacant s.star.present
    have pool := GeneralBorrowFreshAllocatorInvariant.attached tree.nodes tree.tagMapping.deassigned s.allocator.pool index root available s.node
      (GeneralBorrowFreshDefaultChild.child tag root) s.star.present
    have accounting : tree.tagMapping.mapping.size+1+tree.tagMapping.deassigned.pop.size =
        (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.size := by
      have old := s.allocator.accounting
      have positive : 0 < tree.tagMapping.deassigned.size := by
        obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp available
        rw [eq]
        simp only [Array.size_push];omega
      change tree.tagMapping.mapping.size+tree.tagMapping.deassigned.size = tree.nodes.data.size at old
      change _ = (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.data.size
      rw [rawSize,Array.size_pop]
      omega
    have slack : depth.depth root < tree.nodes.size := by
      have positive := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root s.node s.star.present
      have nonempty : 0 < tree.nodes.data.size := by omega
      simpa [depth,GeneralBorrowStarCertificates.depth,UniValMap.size] using nonempty
    let rawState := attached_state tree root index bytes s tag tree.tagMapping.deassigned.pop fresh vacant rawStar leaf
      (by rw [rawSize];change tree.nodes.data.size+5 ≤ _ at room;omega)
      (by intro position valid different;rw [rawSize] at valid;exact valid)
      pool accounting (by change _+4 ≤ _;rw [show (GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)).nodes.size = tree.nodes.size from rawSize];omega)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)
      ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned.pop⟩ tree.locations
    have completed := GeneralBorrowZeroDefaultConstructor.reuse tree depth s.node.tag tag root index s.node tagged s.star.present fresh available bounded vacant slack offset
    have actual : (operation tree s.node.tag tag offset).tree = (sourceUpdateSifa stage root .Read).1 := by
      simpa only [operation,stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached] using completed.2
    have closed := GeneralBorrowZeroSharedState.sifa stage root bytes rawState
    have rootTag : rawState.node.tag = s.node.tag := rfl
    rw [rootTag,←actual] at closed
    have shape := GeneralBorrowSifaView.preserves stage root .Read
    have size := GeneralBorrowFreshMetadata.node_size stage _ shape
    have mapping := GeneralBorrowFreshMetadata.mapping stage _ shape
    rw [←actual] at size mapping
    have stageSize : stage.nodes.size = tree.nodes.size := by
      simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,UniValMap.size] using rawSize
    refine ⟨completed.1,closed.2,?_,?_⟩
    · rw [size,stageSize];omega
    · intro future different unused
      rw [mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag future index tree.tagMapping.deassigned.pop unused different

end DuplicatePrefix.GeneralBorrowZeroDefaultState
