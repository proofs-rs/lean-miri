import duplicate_prefix.GeneralBorrowPhysicalRootPath
import duplicate_prefix.GeneralBorrowSnapshotReadState

namespace DuplicatePrefix.GeneralBorrowSnapshotReadTransport
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option autoImplicit false

/-- Internal data transport; operational callers derive the frames from real
accesses. These frames are not added to the call-time safety contract. -/
theorem transport (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree before protections root position maximum .Read support)
    (counters : GeneralBorrowExposedNonleafState.ReadFrame before after)
    (slots : ∀ index, support index → after.perms.get index = before.perms.get index) :
    Snapshot tree after protections root position maximum .Read support := by
  refine ⟨?_, ?_⟩
  · intro index node included present
    rw [GeneralBorrowSnapshotReadState.relation_frame before after counters]
    change Scalar (effective after index node) .Read _ _
    simpa only [effective, slots index included] using snapshot.scalar index node included present
  · intro physical
    obtain ⟨index, node, included, present, witness⟩ := snapshot.witness physical
    exact ⟨index, node, included, present, by simpa only [Supports, slots index included] using witness⟩

/-- Covers of distinct physical roots cannot contain the same present node. -/
theorem covers_disjoint (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (left right index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (leftMember : left ∈ tree.roots.toList) (rightMember : right ∈ tree.roots.toList)
    (different : left ≠ right)
    (leftCovers : GeneralBorrowExposureCardinality.Covers tree.nodes left index)
    (rightCovers : GeneralBorrowExposureCardinality.Covers tree.nodes right index) : False := by
  obtain ⟨depth⟩ := formed.depth
  let topology := (source_normal_projection tree location protections).topology
  have leftPath := GeneralBorrowPhysicalRootPath.projection_desc tree location protections left index
    (GeneralBorrowWildcardControlWitness.path_of_covers tree depth left index node present leftCovers)
  have rightPath := GeneralBorrowPhysicalRootPath.projection_desc tree location protections right index
    (GeneralBorrowWildcardControlWitness.path_of_covers tree depth right index node present rightCovers)
  have parentless : ∀ root, root ∈ tree.roots.toList →
      ∃ valid : root.toNat < topology.nodes.size, topology.nodes[root.toNat].parent = none := by
    intro root member
    obtain ⟨rootNode, rootPresent, rootParentless⟩ := formed.rootNodes root member
    have valid : root.toNat < topology.nodes.size := by
      have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root rootNode rootPresent
      unfold topology
      unfold_general_projection
      unfold_general_topology
      simpa only [Array.size_map] using bound
    refine ⟨valid, ?_⟩
    have projected := projection_topology_node tree location protections root.toNat root rootNode rfl rootPresent
    change (topology.nodes[root.toNat]?.getD ⟨none, []⟩) = _ at projected
    simp only [Array.getElem?_eq_getElem valid, Option.getD_some] at projected
    rw [projected]
    simp only [rootParentless, Option.map_none]
  obtain ⟨leftValid, leftParentless⟩ := parentless left leftMember
  obtain ⟨rightValid, rightParentless⟩ := parentless right rightMember
  apply GeneralBorrowNormalComponentNormalization.roots_disjoint topology left.toNat right.toNat index.toNat
    leftValid rightValid leftParentless rightParentless _ leftPath rightPath
  intro same
  exact different (GeneralBorrowNodeUpdate.index_injective left right same)

/-- Another root's snapshot follows from actual outside and counter frames;
component separation is derived from graph consistency and Covers. -/
theorem transport_other (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root other : UniIndex) (rootMember : root ∈ tree.roots.toList)
    (otherMember : other ∈ tree.roots.toList) (different : root ≠ other)
    (support otherSupport : UniIndex → Prop)
    (covers : ∀ index, support index → GeneralBorrowExposureCardinality.Covers tree.nodes root index)
    (otherPresent : ∀ index, otherSupport index → ∃ node, tree.nodes.get index = some node)
    (otherCovers : ∀ index, otherSupport index → GeneralBorrowExposureCardinality.Covers tree.nodes other index)
    (position : Nat) (maximum : Option BorTag)
    (snapshot : Snapshot tree before protections other position maximum .Read otherSupport)
    (counters : GeneralBorrowExposedNonleafState.ReadFrame before after)
    (outside : ∀ index, ¬support index → after.perms.get index = before.perms.get index) :
    Snapshot tree after protections other position maximum .Read otherSupport := by
  apply transport tree before after protections other position maximum otherSupport snapshot counters
  intro index included
  apply outside index
  intro inside
  obtain ⟨node, present⟩ := otherPresent index included
  exact covers_disjoint tree before protections formed root other index node present rootMember otherMember different
    (covers index inside) (otherCovers index included)

end DuplicatePrefix.GeneralBorrowSnapshotReadTransport
