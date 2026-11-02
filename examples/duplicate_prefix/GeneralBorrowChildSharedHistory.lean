import duplicate_prefix.GeneralBorrowPartitionSharedStage
import duplicate_prefix.GeneralBorrowFreshStageMetadata
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant

namespace DuplicatePrefix.GeneralBorrowChildSharedHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshMixedChild DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Structural constructor Data for any present parent in the generated star.
The selected append/reuse Slot, child depth slack and vacant Clean are derived.
Ownership of the parent's requested range is deliberately a later conclusion. -/
noncomputable def data (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (parent : UniIndex) (node : TreeNode)
    (present : tree.nodeAt parent = some node) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) : Data tree tag parent offset len := by
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have parentBound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes parent node present
  have rootBound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root s.node s.star.present
  have slack : depth.depth parent < tree.nodes.size := by
    by_cases same : parent = root
    · subst parent
      have positive : 0 < tree.nodes.data.size := by omega
      simpa [depth,GeneralBorrowStarCertificates.depth,UniValMap.size] using positive
    · have two : 1 < tree.nodes.data.size := by
        by_cases large : 1 < tree.nodes.data.size
        · exact large
        · have eq : parent.toNat = root.toNat := by omega
          exact False.elim (same (GeneralBorrowNodeUpdate.index_injective parent root eq))
      simpa [depth,GeneralBorrowStarCertificates.depth,same,UniValMap.size] using two
  have aligned := GeneralBorrowFreshStagePool.empty_aligned tree s.allocator.accounting
  have fits : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty
    rw [aligned empty]
    have room := s.room
    change tree.nodes.data.size+4 ≤ _ at room
    omega
  let slot := GeneralBorrowFreshAllocatorInvariant.slot tree depth parent s.allocator.pool aligned fits slack
  exact {
    parentTag := node.tag, root := root,parentNode := node,depth := depth
    children := GeneralBorrowStarCertificates.children tree root s.node s.star
    parentPresent := present,roots := s.roots
    covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
    parentTagPresent := s.allocator.nodeTags parent node present
    tagFresh := fresh
    protectorFresh := GeneralBorrowFullSharedResources.protector_fresh tree s.allocator.nodeTags tag fresh
    nodeFits := by have room := s.room;change tree.nodes.data.size+4 ≤ _ at room;omega
    slot := slot,nonzero := nonzero,well := s.well
    bounds := by rw [s.capacity];exact bounds
    clean := s.clean _ (GeneralBorrowFreshSharedWithinStages.slot_vacant tree depth parent slot) }

/-- A generated actual shared child owns its real requested slice for a
subsequent child-tag Read, with all graph and allocator Data internally formed.
No successful operation or child ownership is supplied as an input. -/
theorem child_owned (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    let first := data tree root capacity s root s.node s.star.present tag fresh offset len nonzero bounds
    (read first {} false).status = .Completed ∧
    (child first {} false).outcome = .ok () ∧
    OwnedOn (Combined (child first {} false).tree {} (index first) (extend (fun _ => true) (index first).toNat))
      offset (offset+len) (child first {} false).tree.locations ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (child first {} false).tree (index first) .Read offset (offset+len) := by
  dsimp only
  apply GeneralBorrowFreshSharedSequence.run tree tag root offset len _ {} false (fun _ => true)
  intro position valid positive lower upper
  exact write_combined tree _ {} root (s.owned position valid)

/-- The actual generated child-tag Read completes on its requested range and
preserves its mixed ownership. Root and child are distinct actual nodes; this
is a child-source operation, rather than another operation through the root. -/
theorem child_read (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    let first := data tree root capacity s root s.node s.star.present tag fresh offset len nonzero bounds
    let next := (child first {} false).tree
    (read first {} false).status = .Completed ∧ (child first {} false).outcome = .ok () ∧
    (next.performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len) .Read {} .VisitChildrenOfAccessed).status = .Completed := by
  dsimp only
  let first := data tree root capacity s root s.node s.star.present tag fresh offset len nonzero bounds
  have generated := child_owned tree root capacity s tag fresh offset len nonzero bounds
  have initial : OwnedOn (Combined tree {} root (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ {} root (s.owned position valid)
  let metadata := GeneralBorrowFreshStageMetadata.build tree tag root offset len first {} false (fun _ => true) initial
  obtain ⟨node,present,tagged,exposed⟩ := metadata.node
  have postBound : offset.toNat+len.toNat ≤ (child first {} false).tree.locations.size.bytes.toNat := by
    rw [metadata.capacity,s.capacity];exact bounds
  have postFits : (child first {} false).tree.nodes.data.size ≤ 4294967296 := by
    have extension := metadata.extension GeneralBorrowFullSharedSeed.location GeneralBorrowFullSharedSeed.location {}
    have beforeSize : (source_normal_projection tree GeneralBorrowFullSharedSeed.location {}).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    have afterSize : (source_normal_projection (child first {} false).tree GeneralBorrowFullSharedSeed.location {}).topology.nodes.size =
        (child first {} false).tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    have room := s.room
    change tree.nodes.data.size+4 ≤ 4294967295 at room
    rcases extension with appended | reused
    · have count := appended.length
      rw [beforeSize,afterSize] at count
      omega
    · have count := reused.length
      rw [beforeSize,afterSize] at count
      omega
  have actual := GeneralBorrowFreshMixedRead.access (child first {} false).tree {} tag (index first) root
    (Size.ofBytes offset) (Size.ofBytes len) (extend (fun _ => true) (index first).toNat) .VisitChildrenOfAccessed
    postFits metadata.certificates.depth metadata.certificates.children node present (metadata.roots.trans s.roots) metadata.certificates.covered
    metadata.lookup metadata.well offset (offset+len) generated.2.2.1 postBound (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨generated.1,generated.2.1,actual.1⟩

end DuplicatePrefix.GeneralBorrowChildSharedHistory
