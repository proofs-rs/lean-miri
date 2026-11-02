import duplicate_prefix.GeneralBorrowNormalOtherCallbackFrame
import duplicate_prefix.GeneralBorrowRootLocalAuthorization
import duplicate_prefix.GeneralBorrowResidualVisiblePrimaryWriteBothAuthorization
namespace DuplicatePrefix.GeneralBorrowConcreteRowCutoffPrimaryWriteAccess
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual primary callback retaining the original complete Row/runtime conclusions,
using a static condition at this cutoff rather than global parent-tag order. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup) (valid : 0 < tree.roots.size)
    (different : selected ≠ tree.roots[0])
    (closed : GeneralBorrowPrimaryWitnessVisibility.CutoffClosed tree maximum)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location tree.roots[0] maximum .Write protections false
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree result.location protections (some anchor) (some selected) maximum) := by
  have selectedDifferent : some selected ≠ some tree.roots[0] := by simpa using different
  obtain ⟨support,read,write⟩ := row.callbacks 0 valid selectedDifferent
  obtain ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩ :=
    GeneralBorrowResidualVisiblePrimaryWriteBothAuthorization.access_closed tree location protections formed tree.roots[0] maximum support closed write coherent short profile possible
  have member : tree.roots[0] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  obtain ⟨normal⟩ := row.normal anchor rfl
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat := by
    simpa using row.rootPath anchor rfl
  obtain ⟨normalAfter,_⟩ := GeneralBorrowNormalOtherCallbackFrame.transport tree location _ protections formed anchor selected tree.roots[0] anchorNode present normal path member different support read.present read.covers outside
  refine ⟨done,cache,sifa,gp,vacant,⟨{wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,cutoff := row.cutoff,normal := ?_,callbacks := ?_}⟩⟩
  · intro source equal
    have same : source = anchor := Option.some.inj equal.symm
    subst source
    exact ⟨normalAfter⟩
  · intro other otherValid selectedOther
    by_cases same : other = 0
    · subst other
      exact ⟨support,readAfter,writeAfter⟩
    · obtain ⟨otherSupport,otherRead,otherWrite⟩ := row.callbacks other otherValid selectedOther
      have otherMember : tree.roots[other] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem otherValid)
      have rootsDifferent : tree.roots[0] ≠ tree.roots[other] := by
        intro equal
        have positions : 0 = other := by
          apply distinct.getElem_inj.mp
          change tree.roots[0] = tree.roots[other]
          exact equal
        exact same positions.symm
      have transport (callbackKind : AccessKind)
          (authorization : Authorization tree location protections tree.roots[other] other maximum callbackKind otherSupport) :=
        GeneralBorrowRootLocalAuthorization.authorization_other tree location _ protections formed tree.roots[0] tree.roots[other] member otherMember rootsDifferent support otherSupport read.covers other maximum callbackKind authorization outside
      exact ⟨otherSupport,transport .Read otherRead,transport .Write otherWrite⟩
end DuplicatePrefix.GeneralBorrowConcreteRowCutoffPrimaryWriteAccess
