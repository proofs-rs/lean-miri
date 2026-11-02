import duplicate_prefix.GeneralBorrowReadCapabilityFrames
namespace DuplicatePrefix.GeneralBorrowReadRowNormal
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Internal Read-only selected normal component plus BOTH residual callback
candidates. This is operation-specific and does not replace public S01 Row. -/
structure ReadRow (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) where
  wildcard : source = none → selectedRoot = none
  rootPath : ∀ anchor, source = some anchor →
    ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
      selectedRoot.map UniIndex.toNat
  rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node
  cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag)
  normal : ∀ anchor, source = some anchor → Nonempty (DuplicatePrefixNormalKind.Capability tree location protections anchor .Read)
  callbacks : ∀ position, (valid : position < tree.roots.size) →
    selectedRoot ≠ some tree.roots[position] → ∃ support,
      DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections
        tree.roots[position] position maximum .Read support ∧
      DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections
        tree.roots[position] position maximum .Write support

/-- Every existing Both row supplies the internal Read-only row. -/
theorem of_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum) :
    ReadRow tree location protections source selected maximum := {
  wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,
  cutoff := row.cutoff,callbacks := row.callbacks
  normal := by
    intro anchor same
    obtain ⟨normal⟩ := row.normal anchor same
    exact ⟨DuplicatePrefixNormalKind.of_normal tree location protections anchor normal .Read⟩ }

/-- Actual normal Read preserves the selected Read capability and both
other-root candidates for every cutoff and either visit mode. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag)
    (row : ReadRow tree location protections (some anchor) (some selected) maximum)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let result := tree.performNormalAccessAt location anchor .Read protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    Nonempty (ReadRow tree result.location protections (some anchor) (some selected) maximum) := by
  obtain ⟨normal⟩ := row.normal anchor rfl
  obtain ⟨done,outcome,cache,sifa,gp,normalAfter,same⟩ :=
    GeneralBorrowReadCapabilityNormal.access tree location protections formed anchor anchorNode present normal coherent profile possible short mode
  refine ⟨done,outcome,cache,sifa,gp,⟨{
    wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,
    cutoff := row.cutoff,normal := ?_,callbacks := ?_}⟩⟩
  · intro source equal
    have equal : source = anchor := Option.some.inj equal.symm
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
      GeneralBorrowReadCapabilityFrames.after_normal_authorization tree location protections formed
        anchor selected tree.roots[position] anchorNode present normal path member rootsDifferent
        callbackKind position maximum support authorization coherent short mode
    exact ⟨support,(transport .Read read).2.2.2.2.2,(transport .Write write).2.2.2.2.2⟩
end DuplicatePrefix.GeneralBorrowReadRowNormal
