import duplicate_prefix.GeneralBorrowNormalOtherRootSnapshot
import duplicate_prefix.GeneralBorrowCompatibleLocationSifaConsistency
import duplicate_prefix.GeneralBorrowCompatibleNormalPossible
namespace DuplicatePrefix.GeneralBorrowConcreteRowNormalAccess
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The actual normal phase preserves the complete concrete-source row for
both access kinds and visit modes, with arbitrary other-root cutoffs. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode)
    (present : tree.nodeAt anchor = some anchorNode) (maximum : Option BorTag)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some anchor) (some selected) maximum)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) :
    let result := tree.performNormalAccessAt location anchor kind protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree result.location protections (some anchor) (some selected) maximum) := by
  obtain ⟨normal⟩ := row.normal anchor rfl
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨depth⟩ := formed.depth
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections anchor anchorNode present
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    change tree.nodes.data.size < 65536 at short
    omega
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      anchor.toNat kind normal.component := by
    intro index supported valid
    apply normal.permissions kind index supported
    have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    simpa only [size] using valid
  have completed := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections anchor kind mode
    depth formed.children anchorNode present forest normal.component owned coherent
  have sifa := GeneralBorrowCompatibleLocationSifaConsistency.normal tree location protections anchor kind mode
    fits depth formed.children anchorNode present forest normal.component owned profile
  have gp := GeneralBorrowCompatibleNormalPossible.normal tree location protections anchor kind mode
    fits forest geometry.1 normal possible
  obtain ⟨normalAfter,sameComponent⟩ := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves_component
    tree location protections anchor kind mode fits forest geometry.1 normal
  refine ⟨completed.1,completed.2.1,completed.2.2,sifa.2.2,gp,⟨{
    wildcard := row.wildcard, rootPath := row.rootPath, rootPresent := row.rootPresent,
    cutoff := row.cutoff, normal := ?_, callbacks := ?_}⟩⟩
  · intro source equal
    have same : source = anchor := Option.some.inj equal.symm
    subst source
    exact ⟨normalAfter⟩
  · intro position valid different
    obtain ⟨support,read,write⟩ := row.callbacks position valid different
    have member : tree.roots[position] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
    have rootsDifferent : selected ≠ tree.roots[position] := by simpa using different
    have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat := by
      simpa using row.rootPath anchor rfl
    have transport (callbackKind : AccessKind)
        (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections
          tree.roots[position] position maximum callbackKind support) :=
      GeneralBorrowNormalOtherRootSnapshot.after_normal_authorization tree location protections formed
        anchor selected tree.roots[position] anchorNode present normal path member rootsDifferent
        kind callbackKind position maximum support authorization coherent short mode
    exact ⟨support,(transport .Read read).2.2.2.2.2,(transport .Write write).2.2.2.2.2⟩
end DuplicatePrefix.GeneralBorrowConcreteRowNormalAccess
