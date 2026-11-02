import duplicate_prefix.S05RawOwnershipWriteOnlyAdapter
import duplicate_prefix.S05PrimaryRootOwnership
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal

namespace DuplicatePrefix.S05PrimaryRootPositiveAdapter
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false

/-- Initial metadata and permission-table facts for one physical partition.
Primary no-cutoff callbacks may use the weaker primary ownership packet;
all other callbacks retain the existing raw numeric soundness bridge.
This packet assumes neither callback authorization nor a completed borrow row.
Its necessity for ordinary valid calls is a separate coverage obligation. -/
structure Snapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) where
  wildcard : source = none → selectedRoot = none
  rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat
  rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node
  cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag)
  normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index)
  ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      (∃ rights : S05NoCutoffOwnershipBridge.Ownership tree location protections tree.roots[position] position,
        S05CutoffOwnershipGeometry.CutoffWitness tree location protections tree.roots[position]
          position maximum rights.area.contains ∧
        S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains) ∨
      (position = 0 ∧ maximum = none ∧
        Nonempty (S05PrimaryRootOwnership.Ownership tree location protections tree.roots[position]))

/-- Complete the existing positive capability directly from raw per-window
snapshots. GraphState supplies depth and reciprocity. The primary no-cutoff case
uses relaxed foreign rights; the remaining cases use numeric cache soundness.
Physical root/cutoff metadata and finite cache capacity remain visible.
No operation result or ordinary-validity equivalence is asserted. -/
theorem positive (tree : BorrowTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (tagOrder : ParentTagOrder tree) (short : tree.nodes.size < 65536)
    (positiveLength : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat)
    (sourcePresent : ∀ anchor, source = some anchor → ∃ node, tree.nodeAt anchor = some node)
    (wildcardRoot : source = none → 0 < tree.roots.size)
    (snapshots : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Snapshot tree location protections source selectedRoot maximum))
      offset (offset + len) tree.locations)
    (coherent : GeneralRangeMapOrigins.OwnedOn
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
      offset (offset + len) tree.locations) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections source selectedRoot maximum offset len := by
  obtain ⟨depth⟩ := graph.depth
  refine { positive := positiveLength, bounds := bounds, sourcePresent := sourcePresent,
           wildcardRoot := wildcardRoot, rows := ?_ }
  intro position valid nonempty start stop
  obtain ⟨snapshot⟩ := snapshots position valid nonempty start stop
  have forest := Classical.choice (graph.forest tree.locations.entries[position].data protections)
  have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest tree _ protections forest depth
  apply Nonempty.intro
  apply BoolDestinationWriteOnlyAdapter.WriteRow.complete
    (coherent := coherent position valid nonempty start stop) (short := short)
  refine {
    wildcard := snapshot.wildcard
    rootPath := snapshot.rootPath
    rootPresent := snapshot.rootPresent
    cutoff := snapshot.cutoff
    normal := ?_
    callbacks := ?_ }
  · intro anchor selected
    obtain ⟨component, permissions⟩ := snapshot.normal anchor selected
    exact ⟨⟨component, permissions⟩⟩
  · intro rootPosition rootValid other
    rcases snapshot.ownership rootPosition rootValid other with strict | primary
    · obtain ⟨rights,witness,sound⟩ := strict
      exact ⟨rights.area.contains,
        S05CutoffOwnershipAuthorization.write_authorization tree _ protections _ rootPosition maximum
          rights depth tagOrder witness
          (S05LiveSubtreeCacheSoundness.skip_stable tree _ protections _ rootPosition rights depth reciprocal sound maximum)⟩
    · obtain ⟨zero,noCutoff,⟨rights⟩⟩ := primary
      subst maximum
      exact ⟨rights.area.contains, by
        simpa only [zero] using S05PrimaryRootOwnership.authorization tree _ protections _ rights depth
          (coherent position valid nonempty start stop) short .Write⟩


end DuplicatePrefix.S05PrimaryRootPositiveAdapter
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S05PrimaryRootPositiveAdapter.positive) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
