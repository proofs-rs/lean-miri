import duplicate_prefix.S05LiveSubtreeCacheSoundness
import duplicate_prefix.S05CutoffOwnershipAuthorization
import duplicate_prefix.BoolDestinationWriteOnlyAdapter

namespace DuplicatePrefix.S05RawOwnershipWriteOnlyAdapter
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowWildcardParentTagOrder GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false

/-- Raw permission ownership and numeric live-cone soundness complete a full
protector row, using the existing cutoff geometry and Write-to-Read adapter.
The normal-component permissions, selected-root metadata, graph facts and finite
resource bound remain explicit. This is a sufficient snapshot implication;
formation of these premises from ordinary call-time validity is separate. -/
theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (graph : Reciprocal tree) (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : S05NoCutoffOwnershipBridge.Ownership tree location protections tree.roots[position] position,
        S05CutoffOwnershipGeometry.CutoffWitness tree location protections tree.roots[position]
          position maximum rights.area.contains ∧
        S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply BoolDestinationWriteOnlyAdapter.WriteRow.complete (coherent := coherent) (short := short)
  refine {
    wildcard := wildcard
    rootPath := rootPath
    rootPresent := rootPresent
    cutoff := cutoff
    normal := ?_
    callbacks := ?_ }
  · intro anchor selected
    obtain ⟨component, permissions⟩ := normal anchor selected
    exact ⟨⟨component, permissions⟩⟩
  · intro position valid other
    obtain ⟨rights, witness, sound⟩ := ownership position valid other
    exact ⟨rights.area.contains,
      S05CutoffOwnershipAuthorization.write_authorization tree location protections _ position maximum
        rights depth tagOrder witness
        (S05LiveSubtreeCacheSoundness.skip_stable tree location protections _ position rights depth graph sound maximum)⟩

end DuplicatePrefix.S05RawOwnershipWriteOnlyAdapter
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S05RawOwnershipWriteOnlyAdapter.row) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
