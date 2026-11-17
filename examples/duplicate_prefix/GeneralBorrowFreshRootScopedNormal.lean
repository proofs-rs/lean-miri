import duplicate_prefix.GeneralBorrowFreshRootScopedRow
import duplicate_prefix.GeneralBorrowConcreteRowNormalAccess
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedNormal
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshRootScopedRow DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- The actual normal phase retains the same bounded callback supports for
both access kinds and visit modes. No global parent-tag order is supplied. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : BorTag) (row : Row tree location protections anchor selected maximum)
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
    Nonempty (Row tree result.location protections anchor selected maximum) := by
  obtain ⟨done,outcome,cache,sifa,gp,⟨afterBase⟩⟩ := GeneralBorrowConcreteRowNormalAccess.access tree location protections
    formed anchor selected anchorNode present (some maximum) row.base kind mode coherent profile possible short
  obtain ⟨normal⟩ := row.base.normal anchor rfl
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat := by
    simpa using row.base.rootPath anchor rfl
  refine ⟨done,outcome,cache,sifa,gp,⟨⟨afterBase,row.exposed,?_⟩⟩⟩
  intro position valid different
  obtain ⟨support,bounded,read,write⟩ := row.callbacks position valid different
  have member : tree.roots[position] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  have transport (callbackKind : AccessKind)
      (authorization : Authorization tree location protections tree.roots[position] position (some maximum) callbackKind support) :=
    GeneralBorrowNormalOtherRootSnapshot.after_normal_authorization tree location protections formed anchor selected tree.roots[position]
      anchorNode present normal path member different kind callbackKind position (some maximum) support authorization coherent short mode
  exact ⟨support,bounded,(transport .Read read).2.2.2.2.2,(transport .Write write).2.2.2.2.2⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedNormal
