import duplicate_prefix.GeneralBorrowRootExposureFrame
import duplicate_prefix.GeneralBorrowPartialSharedClean
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant

namespace DuplicatePrefix.GeneralBorrowExposedPartitionState
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Transport range-local ownership through the actual permission/topology
view. Cache values and exposure flags are separate invariants. -/
theorem owned_shape (tree next : BorrowTree) (preserved : treeShape next = treeShape tree)
    (root : UniIndex)
    (owned : Every (GeneralBorrowRange.LocationOwned tree {} root .Write) tree.locations) :
    Every (GeneralBorrowRange.LocationOwned next {} root .Write) next.locations := by
  have nodes : next.nodes.data.map (Option.map nodeShape) = tree.nodes.data.map (Option.map nodeShape) := congrArg (fun row => row.2.1) preserved
  have ranges : next.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) := congrArg (fun row => row.2.2.1) preserved
  have sizes : next.locations.entries.size = tree.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size ranges
  intro position valid
  have validOld : position < tree.locations.entries.size := by rw [←sizes];exact valid
  have entriesSame : some ((next.locations.entries[position]'valid).range,locationShape (next.locations.entries[position]'valid).data) =
      some ((tree.locations.entries[position]'validOld).range,locationShape (tree.locations.entries[position]'validOld).data) := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simpa only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem validOld,Option.map_some] using known
  have locations := congrArg Prod.snd (Option.some.inj entriesSame)
  have profiles := GeneralBorrowFreshOwnership.projection_shape tree next (tree.locations.entries[position]'validOld).data
    (next.locations.entries[position]'valid).data {} nodes locations
  obtain ⟨forest,owner⟩ := owned position validOld
  refine ⟨?_,GeneralBorrowFreshOwnership.anchor_owned _ _ profiles root.toNat .Write owner⟩
  have topology : (source_normal_projection next (next.locations.entries[position]'valid).data {}).topology =
      (source_normal_projection tree (tree.locations.entries[position]'validOld).data {}).topology := congrArg (fun row => row.1) profiles
  rw [topology]
  exact forest

/-- A permission/topology frame transfers the entire recurring state, including
vacant Clean and allocator coherence. No cache-correctness claim is bundled. -/
theorem of_shape (tree next : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (s : State tree root bytes) (shape : treeShape next = treeShape tree) :
    Nonempty {post : State next root bytes // post.node.tag = s.node.tag} := by
  obtain ⟨node,star⟩ := GeneralBorrowGeneratedStarShape.shaped tree next root s.node shape s.star
  obtain ⟨node2,present,tagged,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields tree next shape root s.node s.star.present
  have equal : node = node2 := Option.some.inj (star.present.symm.trans present)
  have tag : node.tag = s.node.tag := equal ▸ tagged
  have geometry := GeneralBorrowFreshGeometry.shape_frame tree next shape s.well
  have allocator : GeneralBorrowGcAllocator.Invariant next := by
    refine ⟨GeneralBorrowFreshStagePool.shape_pool tree next shape s.allocator.pool,
      GeneralBorrowFreshStagePool.shape_accounting tree next shape s.allocator.accounting,?_,
      GeneralBorrowSharedAllocatorInvariant.shape_tags tree next shape s.allocator.nodeTags⟩
    unfold GeneralBorrowGcAllocator.KeyUnique
    rw [GeneralBorrowFreshMetadata.mapping tree next shape]
    exact s.allocator.unique
  refine ⟨⟨⟨node,s.nonzero,star,(GeneralBorrowFreshMetadata.roots tree next shape).trans s.roots,
    geometry.2.trans s.capacity,geometry.1,owned_shape tree next shape root s.owned,
    allocator,GeneralBorrowPartialSharedClean.shaped tree next shape s.clean,?_⟩,tag⟩⟩
  rw [GeneralBorrowFreshMetadata.node_size tree next shape]
  exact s.room

/-- Root exposure is a real successfully completed operation on every recurring
partition state. No exposed-cache witness, successful exposure or resulting
state is assumed. Numerical cache validity remains a separate obligation. -/
theorem expose_root (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes) :
    (tree.exposeTag {} s.node.tag).outcome = .ok () ∧
    Nonempty {post : State (tree.exposeTag {} s.node.tag).tree root bytes // post.node.tag = s.node.tag} ∧
    (tree.exposeTag {} s.node.tag).tree.nodes.size = tree.nodes.size ∧
    (tree.exposeTag {} s.node.tag).tree.tagMapping = tree.tagMapping := by
  have tagged := s.allocator.nodeTags root s.node s.star.present
  cases flag : s.node.isExposed with
  | false =>
    have completed := GeneralBorrowRootExposureFrame.expose tree s.node.tag root s.node tagged s.star.present
      (GeneralBorrowStarCertificates.depth tree root s.node s.star) flag {}
    exact ⟨completed.1,of_shape tree _ root bytes s completed.2.1,
      GeneralBorrowFreshMetadata.node_size tree _ completed.2.1,
      GeneralBorrowFreshMetadata.mapping tree _ completed.2.1⟩
  | true =>
    have exactTree := GeneralBorrowRootExposureFrame.already tree s.node.tag root s.node tagged s.star.present flag {}
    rw [exactTree]
    exact ⟨rfl,⟨⟨s,rfl⟩⟩,rfl,rfl⟩

end DuplicatePrefix.GeneralBorrowExposedPartitionState
