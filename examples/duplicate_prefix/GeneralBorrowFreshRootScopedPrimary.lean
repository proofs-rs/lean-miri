import duplicate_prefix.GeneralBorrowFreshRootScopedRow
import duplicate_prefix.GeneralBorrowNormalOtherCallbackFrame
import duplicate_prefix.GeneralBorrowRootLocalAuthorization
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedPrimary
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshRootScopedRow DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual primary callback Read or Write retains full selected Normal and
all saved bounded supports. Only exposed contributors and the visited support
are bounded; newer hidden nodes elsewhere and parent tag orders are arbitrary. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : BorTag) (row : Row tree location protections anchor selected maximum)
    (distinct : tree.roots.toList.Nodup) (valid : 0 < tree.roots.size) (different : selected ≠ tree.roots[0])
    (kind : AccessKind)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location tree.roots[0] (some maximum) kind protections false
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query,tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) ∧
    Nonempty (Row tree result.location protections anchor selected maximum) := by
  obtain ⟨support,bounded,read,write⟩ := row.callbacks 0 valid different
  have run : let result := tree.performWildcardAccessAt location tree.roots[0] (some maximum) kind protections false
      result.status = .Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query,tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) ∧
      Authorization tree result.location protections tree.roots[0] 0 (some maximum) .Read support ∧
      Authorization tree result.location protections tree.roots[0] 0 (some maximum) .Write support ∧
      (∀ query,¬support query → result.location.perms.get query = location.perms.get query) := by
    cases kind with
    | Read =>
      obtain ⟨done,_,_,_,cache,outside,sifa,gp,vacant,readAfter,writeAfter⟩ :=
        GeneralBorrowFreshRootPrimaryReadBoth.access tree location protections formed tree.roots[0] maximum support
          row.exposed bounded read write coherent short profile possible
      exact ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩
    | Write =>
      exact GeneralBorrowFreshRootPrimaryWriteBoth.access tree location protections formed tree.roots[0] maximum support
        row.exposed bounded write coherent short profile possible
  obtain ⟨done,cache,sifa,gp,vacant,readAfter,writeAfter,outside⟩ := run
  have member : tree.roots[0] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  obtain ⟨normal⟩ := row.base.normal anchor rfl
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat := by
    simpa using row.base.rootPath anchor rfl
  obtain ⟨normalAfter,_⟩ := GeneralBorrowNormalOtherCallbackFrame.transport tree location _ protections formed anchor selected tree.roots[0]
    anchorNode present normal path member different support read.present read.covers outside
  have callbacks : ∀ other,(otherValid : other < tree.roots.size) → selected ≠ tree.roots[other] →
      ∃ otherSupport,GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum otherSupport ∧
        Authorization tree (tree.performWildcardAccessAt location tree.roots[0] (some maximum) kind protections false).location protections tree.roots[other] other (some maximum) .Read otherSupport ∧
        Authorization tree (tree.performWildcardAccessAt location tree.roots[0] (some maximum) kind protections false).location protections tree.roots[other] other (some maximum) .Write otherSupport := by
    intro other otherValid selectedOther
    by_cases same : other = 0
    · subst other
      exact ⟨support,bounded,readAfter,writeAfter⟩
    · obtain ⟨otherSupport,otherBound,otherRead,otherWrite⟩ := row.callbacks other otherValid selectedOther
      have otherMember : tree.roots[other] ∈ tree.roots.toList := Array.mem_toList_iff.mpr (Array.getElem_mem otherValid)
      have rootsDifferent : tree.roots[0] ≠ tree.roots[other] := by
        intro equal
        have positions : 0 = other := by
          apply distinct.getElem_inj.mp
          change tree.roots[0] = tree.roots[other]
          exact equal
        exact same positions.symm
      have transport (callbackKind : AccessKind)
          (authorization : Authorization tree location protections tree.roots[other] other (some maximum) callbackKind otherSupport) :=
        GeneralBorrowRootLocalAuthorization.authorization_other tree location _ protections formed tree.roots[0] tree.roots[other]
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
end DuplicatePrefix.GeneralBorrowFreshRootScopedPrimary
