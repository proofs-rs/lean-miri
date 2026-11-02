import duplicate_prefix.GeneralBorrowNormalOtherCallbackFrame
import duplicate_prefix.GeneralBorrowRootLocalAuthorization
import duplicate_prefix.GeneralBorrowResidualVirtualWriteBothRuntime
import duplicate_prefix.GeneralBorrowSnapshotVirtualReadBothAuthorization
namespace DuplicatePrefix.GeneralBorrowConcreteRowVirtualAccess
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem run (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (virtual : position ≠ 0) (kind : AccessKind)
    (read : Authorization tree location protections root position maximum .Read support)
    (write : Authorization tree location protections root position maximum .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location root maximum kind protections true
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) ∧
    Authorization tree result.location protections root position maximum .Read support ∧
    Authorization tree result.location protections root position maximum .Write support ∧
    (∀ query, ¬support query → result.location.perms.get query = location.perms.get query) := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest location protections
  cases kind with
  | Read =>
    obtain ⟨completed,_,_,_,cache,outside,sifa,gp,vacant,readAfter,writeAfter⟩ :=
      GeneralBorrowSnapshotVirtualReadBothAuthorization.access_both tree location protections root position maximum support virtual read write depth forest coherent short profile possible
    exact ⟨completed,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩
  | Write =>
    obtain ⟨completed,writeAfter,readAfter,_,_,cache,outside,sifa,gp,vacant⟩ :=
      GeneralBorrowResidualVirtualWriteBothRuntime.of_authorization tree location protections root position maximum virtual support write depth forest coherent short profile possible
    exact ⟨completed,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩

/-- A real virtual callback preserves the complete concrete-source S01 Row,
including the selected normal component and all other roots' authorizations.
Any cutoff and either access kind are allowed. This is one actual callback,
not the full root-array operation or a claim of ordinary-valid coverage. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup) (position : Nat) (valid : position < tree.roots.size)
    (virtual : position ≠ 0) (different : selected ≠ tree.roots[position]) (kind : AccessKind)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location tree.roots[position] maximum kind protections true
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree result.location protections (some anchor) (some selected) maximum) := by
  have selectedDifferent : some selected ≠ some tree.roots[position] := by simpa using different
  obtain ⟨support,read,write⟩ := row.callbacks position valid selectedDifferent
  obtain ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩ := run tree location protections formed tree.roots[position] position maximum support virtual kind read write coherent profile possible short
  have member : tree.roots[position] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  obtain ⟨normal⟩ := row.normal anchor rfl
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat := by
    simpa using row.rootPath anchor rfl
  obtain ⟨normalAfter,_⟩ := GeneralBorrowNormalOtherCallbackFrame.transport tree location _ protections formed anchor selected tree.roots[position] anchorNode present normal path member different support read.present read.covers outside
  refine ⟨done,cache,sifa,gp,vacant,⟨{wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,cutoff := row.cutoff,normal := ?_,callbacks := ?_}⟩⟩
  · intro source equal
    have same : source = anchor := Option.some.inj equal.symm
    subst source
    exact ⟨normalAfter⟩
  · intro other otherValid selectedOther
    by_cases same : other = position
    · subst other
      exact ⟨support,readAfter,writeAfter⟩
    · obtain ⟨otherSupport,otherRead,otherWrite⟩ := row.callbacks other otherValid selectedOther
      have otherMember : tree.roots[other] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem otherValid)
      have rootsDifferent : tree.roots[position] ≠ tree.roots[other] := by
        intro equal
        have positions : position = other := by
          apply distinct.getElem_inj.mp
          change tree.roots[position] = tree.roots[other]
          exact equal
        exact same positions.symm
      have transport (callbackKind : AccessKind)
          (authorization : Authorization tree location protections tree.roots[other] other maximum callbackKind otherSupport) :=
        GeneralBorrowRootLocalAuthorization.authorization_other tree location _ protections formed tree.roots[position] tree.roots[other] member otherMember rootsDifferent support otherSupport read.covers other maximum callbackKind authorization outside
      exact ⟨otherSupport,transport .Read otherRead,transport .Write otherWrite⟩
end DuplicatePrefix.GeneralBorrowConcreteRowVirtualAccess
