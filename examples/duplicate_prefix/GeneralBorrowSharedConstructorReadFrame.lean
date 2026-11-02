import duplicate_prefix.GeneralBorrowFreshReadExtension
import duplicate_prefix.GeneralBorrowFreshSharedPaths
import duplicate_prefix.GeneralBorrowFreshSharedInstallation

namespace DuplicatePrefix.GeneralBorrowSharedConstructorReadFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowFreshMaterialization
open DuplicatePrefix.GeneralBorrowFreshSharedPaths
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem topology_size (tree : BorrowTree) (location : LocationTree) :
    (source_normal_projection tree location {}).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection;unfold_general_topology;simp only [Array.size_map]

private theorem empty (tree : BorrowTree) (location : LocationTree) (position : Nat) :
    (source_normal_projection tree location {}).protectedNodes.contains position = false := by
  unfold_general_projection;simp [ProtectedTags.contains,ProtectedTags.get]

/-- A raw shared leaf append preserves any old Read anchor, including anchors
on unrelated branches. The new Frozen leaf is foreign to every old path. -/
theorem append_location (tree : BorrowTree) (index parent target : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (owned : GeneralBorrowRange.LocationOwned tree {} target .Read location) :
    GeneralBorrowRange.LocationOwned
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)) {}
      target .Read (materialized location index GeneralBorrowFreshAnchor.sharedState) := by
  obtain ⟨⟨forest⟩,owner⟩ := owned
  let afterTree := GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
  let afterLocation := materialized location index GeneralBorrowFreshAnchor.sharedState
  let before := source_normal_projection tree location {}
  let after := source_normal_projection afterTree afterLocation {}
  have ext : GeneralBorrowFreshTopology.Extension before.topology after.topology parent.toNat :=
    GeneralBorrowFreshProjection.topology_extension tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      atEnd parentPresent rfl rfl location afterLocation {}
  have attach := of_append before.topology after.topology parent.toNat ext forest
  have oldSize : before.topology.nodes.size = index.toNat := (topology_size tree location).trans atEnd.symm
  have different : target.toNat ≠ index.toNat := by have valid := owner.anchorValid;rw [oldSize] at valid;omega
  have path := attach.oldPath target.toNat owner.anchorValid (by rw [oldSize];exact different)
  have outside := attach.outsideOld target.toNat owner.anchorValid (by rw [oldSize];exact different)
  rw [oldSize] at outside
  refine ⟨⟨GeneralBorrowFreshProjection.projected_forest tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
    atEnd parentPresent rfl rfl location afterLocation {} forest⟩,?_⟩
  apply GeneralBorrowFreshReadExtension.extension_owned before after target.toNat index.toNat owner
    (attach.oldValid target.toNat owner.anchorValid (by rw [oldSize];exact different))
    ((projection_sizes afterTree afterLocation {}).1.trans (topology_size afterTree afterLocation).symm)
    ((projection_sizes afterTree afterLocation {}).2.trans (topology_size afterTree afterLocation).symm)
    (by intro position valid different;rw [ext.length,oldSize] at valid;omega)
    (by intro position valid different;rw [topology_size tree location] at valid
        exact state_old tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent) atEnd parentPresent location GeneralBorrowFreshAnchor.sharedState {} position valid)
    (by intro position valid different;rw [empty,empty]) path outside GeneralBorrowFreshAnchor.sharedState
    (state_new tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent) atEnd parentPresent location GeneralBorrowFreshAnchor.sharedState {})
    rfl (empty afterTree afterLocation index.toNat)

/-- Reuse of a vacant slot has the same arbitrary-old-anchor Read frame. -/
theorem reuse_location (tree : BorrowTree) (index parent target : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (different : target ≠ index) (location : LocationTree)
    (owned : GeneralBorrowRange.LocationOwned tree {} target .Read location) :
    GeneralBorrowRange.LocationOwned
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)) {}
      target .Read (materialized location index GeneralBorrowFreshAnchor.sharedState) := by
  obtain ⟨⟨forest⟩,owner⟩ := owned
  let afterTree := GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
  let afterLocation := materialized location index GeneralBorrowFreshAnchor.sharedState
  let before := source_normal_projection tree location {}
  let after := source_normal_projection afterTree afterLocation {}
  have ext : GeneralBorrowFreshReuseTopology.Extension before.topology after.topology index.toNat parent.toNat :=
    GeneralBorrowFreshReuseProjection.topology_extension tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      bounded vacant parentPresent rfl rfl location afterLocation {}
  have attach := of_reuse before.topology after.topology index.toNat parent.toNat ext forest
  have distinct : target.toNat ≠ index.toNat := fun equal => different (GeneralBorrowNodeUpdate.index_injective target index equal)
  refine ⟨⟨GeneralBorrowFreshReuseProjection.projected_forest tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
    bounded vacant parentPresent rfl rfl location afterLocation {} forest⟩,?_⟩
  apply GeneralBorrowFreshReadExtension.extension_owned before after target.toNat index.toNat owner
    (attach.oldValid target.toNat owner.anchorValid distinct)
    ((projection_sizes afterTree afterLocation {}).1.trans (topology_size afterTree afterLocation).symm)
    ((projection_sizes afterTree afterLocation {}).2.trans (topology_size afterTree afterLocation).symm)
    (by intro position valid different;rw [ext.length] at valid;exact valid)
    (by intro position valid different;rw [topology_size tree location] at valid
        exact GeneralBorrowFreshReuseState.state_old tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
          bounded vacant parentPresent fits location GeneralBorrowFreshAnchor.sharedState {} position valid different)
    (by intro position valid different;rw [empty,empty])
    (attach.oldPath target.toNat owner.anchorValid distinct) (attach.outsideOld target.toNat owner.anchorValid distinct)
    GeneralBorrowFreshAnchor.sharedState
    (GeneralBorrowFreshReuseState.state_new tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      bounded vacant parentPresent location GeneralBorrowFreshAnchor.sharedState {}) rfl (empty afterTree afterLocation index.toNat)

end DuplicatePrefix.GeneralBorrowSharedConstructorReadFrame
