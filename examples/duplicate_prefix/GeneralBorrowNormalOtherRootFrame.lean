import duplicate_prefix.GeneralBorrowNormalOtherRootSnapshot
import duplicate_prefix.DuplicatePrefixNormalKind

/-! Actual normal access frames other physical components without requiring
legacy callback authorization. The normal capability is scalar input data;
no operation outcome is a premise. -/
namespace DuplicatePrefix.GeneralBorrowNormalOtherRootFrame
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowPresence
set_option autoImplicit false
set_option maxHeartbeats 4000000

private theorem canonical_kind (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (root : Nat)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (valid : root < (source_normal_projection tree location protections).topology.nodes.size)
    (parentless : (source_normal_projection tree location protections).topology.nodes[root].parent = none)
    (path : Desc (source_normal_projection tree location protections).topology root anchor.toNat)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections anchor kind) :
    ∃ next : DuplicatePrefixNormalKind.Capability tree location protections anchor kind,
      next.component.support = Desc (source_normal_projection tree location protections).topology root := by
  have rootInside := GeneralBorrowNormalComponentNormalization.contains_ancestor _ anchor.toNat normal.component
    root anchor.toNat path normal.component.anchor
  let chosen := GeneralBorrowExposedScopedNormalRoot.component
    (source_normal_projection tree location protections).topology forest root anchor.toNat valid parentless path
  refine ⟨⟨chosen,?_⟩,rfl⟩
  intro index inside bounded
  exact normal.permissions index
    (GeneralBorrowNormalComponentNormalization.contains_descendant _ forest anchor.toNat normal.component root index inside rootInside) bounded

theorem access_kind (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (kind : AccessKind)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections anchor kind)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (mode : ChildrenVisitMode) :
    let result := tree.performNormalAccessAt location anchor kind protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ index node, tree.nodes.get index = some node →
      GeneralBorrowExposedNonleafPrimaryPath.Path tree other index →
      result.location.perms.get index = location.perms.get index) := by
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
  obtain ⟨canonical,canonicalSupport⟩ := canonical_kind tree location protections
    anchor kind selected.toNat forest selectedPath.valid.1 selectedParentless selectedPath normal
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      anchor.toNat kind canonical.component := by
    intro index included bounded
    have size : topology.nodes.size = tree.nodes.data.size := by
      unfold topology
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact canonical.permissions index included (by rw [←size];exact bounded)
  have actual := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections anchor kind mode
    depth formed.children anchorNode anchorPresent forest canonical.component owned coherent
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
  have componentSlots : ∀ index node, tree.nodes.get index = some node →
      other ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) index →
      (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get index = location.perms.get index := by
    intro index node present member
    have physicalPath := GeneralBorrowWildcardControlWitness.path_of_walk tree depth other index node present _ member
    have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree location protections other index physicalPath
    apply GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor kind mode canonical.component index node present
    intro contained
    rw [canonicalSupport] at contained
    apply GeneralBorrowNormalComponentNormalization.roots_disjoint topology selected.toNat other.toNat index.toNat
      selectedPath.valid.1 otherValid selectedParentless otherParentless _ contained projectedPath
    intro same
    exact different (GeneralBorrowNodeUpdate.index_injective selected other same)
  refine ⟨actual.1,actual.2.1,actual.2.2,?_⟩
  intro index node present path
  exact componentSlots index node present (path.walk depth)

/-- Both-kind normal capabilities specialize the operation-specific frame. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (kind : AccessKind) (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (mode : ChildrenVisitMode) :
    let result := tree.performNormalAccessAt location anchor kind protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ index node, tree.nodes.get index = some node →
      GeneralBorrowExposedNonleafPrimaryPath.Path tree other index →
      result.location.perms.get index = location.perms.get index) := by
  exact access_kind tree location protections formed anchor selected other anchorNode anchorPresent kind
    (DuplicatePrefixNormalKind.of_normal tree location protections anchor normal kind) rootPath otherMember different coherent mode

end DuplicatePrefix.GeneralBorrowNormalOtherRootFrame

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowNormalOtherRootFrame." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved normal-frame dependency {dependency}"
