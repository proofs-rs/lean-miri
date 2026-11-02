import duplicate_prefix.GeneralBorrowPartialSharedOwnership

namespace DuplicatePrefix.GeneralBorrowPartialSharedRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The explicit-location normal projection ignores allocator metadata and
other stored ranges; only its nodes and the supplied location/protectors matter. -/
theorem owned_nodes (before after : BorrowTree) (nodes : after.nodes = before.nodes)
    (root : UniIndex) (location : LocationTree)
    (owned : GeneralBorrowRange.LocationOwned before {} root .Write location) :
    GeneralBorrowRange.LocationOwned after {} root .Write location := by
  have same : source_normal_projection after location {} = source_normal_projection before location {} := by
    unfold_general_projection
    unfold_general_topology
    rw [nodes]
  unfold GeneralBorrowRange.LocationOwned
  rw [same]
  exact owned

/-- Real partial-range installation retains root ownership across the ENTIRE
partition, including untouched locations with the child's actual lazy default.
No selected-range success or resulting ownership is assumed. -/
theorem owned (tree : BorrowTree) (root index : UniIndex) (node : TreeNode) (tag : BorTag)
    (present : tree.nodeAt root = some node) (parentless : node.parent = none) (notRoot : root ≠ index)
    (star : DuplicatePrefix.GeneralBorrowGeneratedStarShape.Star
      (attached tree index root node (GeneralBorrowFreshAnchor.sharedNode tag root)) root (updatedParent node index))
    (leaf : (attached tree index root node (GeneralBorrowFreshAnchor.sharedNode tag root)).nodeAt index = some (GeneralBorrowFreshAnchor.sharedNode tag root))
    (fits : (attached tree index root node (GeneralBorrowFreshAnchor.sharedNode tag root)).nodes.data.size ≤ 4294967296)
    (oldPosition : ∀ position, position < (attached tree index root node (GeneralBorrowFreshAnchor.sharedNode tag root)).nodes.data.size →
      position ≠ index.toNat → position < tree.nodes.data.size)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : Every (GeneralBorrowRange.LocationOwned tree {} root .Write) tree.locations)
    (clean : Every (fun location : LocationTree => location.perms.get index = none) tree.locations) :
    let next := attached tree index root node (GeneralBorrowFreshAnchor.sharedNode tag root)
    let map := (tree.locations.modifyRange offset len (fun _ location => materialized location index GeneralBorrowFreshAnchor.sharedState)).state
    Every (GeneralBorrowRange.LocationOwned next {} root .Write) map := by
  dsimp only
  let modify := fun (_ : ByteRange) location => materialized location index GeneralBorrowFreshAnchor.sharedState
  let prepared := tree.locations.iterMut offset len
  have owners := GeneralRangeMapSafety.iter_mut (GeneralBorrowRange.LocationOwned tree {} root .Write) tree.locations offset len well initial bounds
  have vacant := GeneralRangeMapSafety.iter_mut (fun location : LocationTree => location.perms.get index = none) tree.locations offset len well clean bounds
  have sizes : (tree.locations.modifyRange offset len modify).state.entries.size = prepared.state.entries.size := by
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid
  have oldBound : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputBound,exactEntry⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location index GeneralBorrowFreshAnchor.sharedState) well bounds position oldBound
  change GeneralBorrowRange.LocationOwned _ {} root .Write (tree.locations.modifyRange offset len modify).state.entries[position].data
  rw [exactEntry]
  split
  · refine ⟨⟨GeneralBorrowStarCertificates.forest _ root (updatedParent node index) star _ {} fits⟩,?_⟩
    apply GeneralBorrowPartialSharedOwnership.location tree root index node tag present parentless notRoot star.present leaf fits oldPosition
      prepared.state.entries[position].data (materialized prepared.state.entries[position].data index GeneralBorrowFreshAnchor.sharedState)
    · intro query different
      exact GeneralBorrowFreshLocation.get_other _ index query _ different
    · exact Or.inr (GeneralBorrowFreshLocation.get_same _ index _)
    · exact (owners.every position oldBound).2
  · refine ⟨⟨GeneralBorrowStarCertificates.forest _ root (updatedParent node index) star _ {} fits⟩,?_⟩
    apply GeneralBorrowPartialSharedOwnership.location tree root index node tag present parentless notRoot star.present leaf fits oldPosition
      prepared.state.entries[position].data prepared.state.entries[position].data
    · intro query different;rfl
    · exact Or.inl (vacant.every position oldBound)
    · exact (owners.every position oldBound).2

end DuplicatePrefix.GeneralBorrowPartialSharedRange
