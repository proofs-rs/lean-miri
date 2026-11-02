import duplicate_prefix.GeneralBorrowPhysicalRootPath
import duplicate_prefix.GeneralBorrowCompatibleNormalReadFrame
import duplicate_prefix.GeneralBorrowSnapshotReadState
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.GeneralBorrowTerminal
namespace DuplicatePrefix.GeneralBorrowNormalOtherRootReadSnapshot
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowPresence
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- A real normal Read leaves all scalar rows of a different physical-root
callback unchanged and transports its raw Read snapshot. The arbitrary normal
certificate is restricted to its actual selected component internally. No
component separation or successful operation is assumed by the caller. -/
theorem after_normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (callback : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections other rootPosition maximum .Read support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let after := (tree.performNormalAccessAt location anchor .Read protections mode).location
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
    GeneralBorrowExposedNonleafState.ReadFrame location after ∧
    (∀ index, support index → after.perms.get index = location.perms.get index) ∧
    Snapshot tree after protections other rootPosition maximum .Read support := by
  let topology := (source_normal_projection tree location protections).topology
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨depth⟩ := formed.depth
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections anchor anchorNode anchorPresent
  have selectedPath := GeneralBorrowPhysicalRootPath.selected_desc topology forest anchor.toNat selected.toNat geometry.1 rootPath
  have terminal := GeneralBorrowTerminal.ancestor_terminal topology forest anchor.toNat geometry.1
  have lastEq : (topology.ancestorPath anchor.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath]
    rfl
  rw [lastEq] at terminal
  have selectedParentless : (topology.nodes[selected.toNat]'selectedPath.valid.1).parent = none := by
    simpa only [nodeData,Array.getElem?_eq_getElem selectedPath.valid.1,Option.getD_some] using terminal
  obtain ⟨canonical,canonicalSupport⟩ := GeneralBorrowNormalComponentNormalization.canonical tree location protections
    anchor selected.toNat forest selectedPath.valid.1 selectedParentless selectedPath normal
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      anchor.toNat .Read canonical.component := by
    intro index included bounded
    have size : topology.nodes.size = tree.nodes.data.size := by
      unfold topology
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact canonical.permissions .Read index included (by rw [←size];exact bounded)
  have actual := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections anchor .Read mode
    depth formed.children anchorNode anchorPresent forest canonical.component owned coherent
  have pointwise := GeneralBorrowCompatibleNormalReadFrame.pointwise tree location protections anchor mode
    forest canonical.component owned depth formed.children anchorNode anchorPresent
  have counters := GeneralBorrowCompatibleNormalReadFrame.counters tree location _ protections coherent actual.2.2 pointwise
  obtain ⟨otherNode,otherPresent,otherParent⟩ := formed.rootNodes other otherMember
  have otherValid : other.toNat < topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes other otherNode otherPresent
    unfold topology
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  have otherProjection := projection_topology_node tree location protections other.toNat other otherNode rfl otherPresent
  change (topology.nodes[other.toNat]?.getD ⟨none,[]⟩) = _ at otherProjection
  simp only [Array.getElem?_eq_getElem otherValid,Option.getD_some] at otherProjection
  have otherParentless : (topology.nodes[other.toNat]'otherValid).parent = none := by
    rw [otherProjection]
    simp only [otherParent,Option.map_none]
  have slotFrame : ∀ index, support index →
      (tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get index = location.perms.get index := by
    intro index included
    obtain ⟨node,present⟩ := callback.present index included
    have physicalPath := GeneralBorrowWildcardControlWitness.path_of_covers tree depth other index node present (callback.covers index included)
    have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree location protections other index physicalPath
    apply GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor .Read mode canonical.component index node present
    intro contained
    rw [canonicalSupport] at contained
    apply GeneralBorrowNormalComponentNormalization.roots_disjoint topology selected.toNat other.toNat index.toNat
      selectedPath.valid.1 otherValid selectedParentless otherParentless _ contained projectedPath
    intro same
    exact different (GeneralBorrowNodeUpdate.index_injective selected other same)
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections other rootPosition maximum .Read support callback coherent short
  refine ⟨actual.1,actual.2.1,actual.2.2,counters,slotFrame,?_,?_⟩
  · intro index node included present
    have authorized := snapshot.scalar index node included present
    rw [GeneralBorrowSnapshotReadState.relation_frame location _ counters]
    change Scalar (effective _ index node) .Read _ _
    simpa only [effective,slotFrame index included] using authorized
  · intro physical
    obtain ⟨index,node,included,present,witness⟩ := snapshot.witness physical
    refine ⟨index,node,included,present,?_⟩
    simpa only [Supports,slotFrame index included] using witness

end DuplicatePrefix.GeneralBorrowNormalOtherRootReadSnapshot
