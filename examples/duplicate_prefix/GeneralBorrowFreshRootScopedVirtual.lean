import duplicate_prefix.GeneralBorrowFreshRootScopedRow
import duplicate_prefix.GeneralBorrowNormalOtherCallbackFrame
import duplicate_prefix.GeneralBorrowRootLocalAuthorization
import duplicate_prefix.GeneralBorrowConcreteRowVirtualAccess
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedVirtual
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshRootScopedRow DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual virtual callback Read or Write retains full selected Normal and
all saved bounded supports. Only exposed contributors and the visited support
are bounded; newer hidden nodes elsewhere and parent tag orders are arbitrary. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : BorTag) (row : Row tree location protections anchor selected maximum)
    (distinct : tree.roots.toList.Nodup) (position : Nat) (valid : position < tree.roots.size)
    (virtual : position ≠ 0) (different : selected ≠ tree.roots[position])
    (kind : AccessKind)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location tree.roots[position] (some maximum) kind protections true
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query,tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) ∧
    Nonempty (Row tree result.location protections anchor selected maximum) := by
  obtain ⟨support,bounded,read,write⟩ := row.callbacks position valid different
  have run : let result := tree.performWildcardAccessAt location tree.roots[position] (some maximum) kind protections true
      result.status = .Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query,tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) ∧
      Authorization tree result.location protections tree.roots[position] position (some maximum) .Read support ∧
      Authorization tree result.location protections tree.roots[position] position (some maximum) .Write support ∧
      (∀ query,¬support query → result.location.perms.get query = location.perms.get query) := by
    obtain ⟨depth⟩ := formed.depth
    obtain ⟨forest⟩ := formed.forest location protections
    cases kind with
    | Read =>
      obtain ⟨done,_,_,_,cache,outside,sifa,gp,vacant,readAfter,writeAfter⟩ :=
        GeneralBorrowSnapshotVirtualReadBothAuthorization.access_both tree location protections tree.roots[position] position
          (some maximum) support virtual read write depth forest coherent short profile possible
      exact ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩
    | Write =>
      obtain ⟨done,writeAfter,readAfter,_,_,cache,outside,sifa,gp,vacant⟩ :=
        GeneralBorrowResidualVirtualWriteBothRuntime.of_authorization tree location protections tree.roots[position] position
          (some maximum) virtual support write depth forest coherent short profile possible
      exact ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩
  obtain ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩ := run
  have member : tree.roots[position] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  obtain ⟨normal⟩ := row.base.normal anchor rfl
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat := by
    simpa using row.base.rootPath anchor rfl
  obtain ⟨normalAfter,_⟩ := GeneralBorrowNormalOtherCallbackFrame.transport tree location _ protections formed anchor selected tree.roots[position]
    anchorNode present normal path member different support read.present read.covers outside
  have callbacks : ∀ other,(otherValid : other < tree.roots.size) → selected ≠ tree.roots[other] →
      ∃ otherSupport,GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum otherSupport ∧
        Authorization tree (tree.performWildcardAccessAt location tree.roots[position] (some maximum) kind protections true).location protections tree.roots[other] other (some maximum) .Read otherSupport ∧
        Authorization tree (tree.performWildcardAccessAt location tree.roots[position] (some maximum) kind protections true).location protections tree.roots[other] other (some maximum) .Write otherSupport := by
    intro other otherValid selectedOther
    by_cases same : other = position
    · subst other
      exact ⟨support,bounded,readAfter,writeAfter⟩
    · obtain ⟨otherSupport,otherBound,otherRead,otherWrite⟩ := row.callbacks other otherValid selectedOther
      have otherMember : tree.roots[other] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem otherValid)
      have rootsDifferent : tree.roots[position] ≠ tree.roots[other] := by
        intro equal
        have positions : position = other := by
          apply distinct.getElem_inj.mp
          change tree.roots[position] = tree.roots[other]
          exact equal
        exact same positions.symm
      have transport (callbackKind : AccessKind)
          (authorization : Authorization tree location protections tree.roots[other] other (some maximum) callbackKind otherSupport) :=
        GeneralBorrowRootLocalAuthorization.authorization_other tree location _ protections formed tree.roots[position] tree.roots[other]
          member otherMember rootsDifferent support otherSupport read.covers other (some maximum) callbackKind authorization outside
      exact ⟨otherSupport,otherBound,transport .Read otherRead,transport .Write otherWrite⟩
  refine ⟨done,cache,sifa,gp,vacant,⟨⟨?_,row.exposed,callbacks⟩⟩⟩
  refine {wildcard := row.base.wildcard,rootPath := row.base.rootPath,rootPresent := row.base.rootPresent,
          cutoff := row.base.cutoff,normal := ?_,callbacks := ?_}
  · intro source equal
    have same : source = anchor := Option.some.inj equal.symm
    subst source
    exact ⟨normalAfter⟩
  · intro other otherValid selectedOther
    have different : selected ≠ tree.roots[other] := by simpa using selectedOther
    obtain ⟨otherSupport,otherBound,otherRead,otherWrite⟩ := callbacks other otherValid different
    exact ⟨otherSupport,otherRead,otherWrite⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedVirtual
