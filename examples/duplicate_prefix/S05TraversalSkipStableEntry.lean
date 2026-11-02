import duplicate_prefix.S05TraversalSkipStable
import duplicate_prefix.DuplicatePrefixResidualVisibleWritePlan
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal

namespace DuplicatePrefix.S05TraversalSkipStableEntry
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardControlWitness
open GeneralBorrowWildcardParentTagOrder DuplicatePrefixCallbackAuthorization
open DuplicatePrefixResidualWriteWitnessPlan S05ContributorCacheOrder S05WriteCacheContributorOwnership
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The abstract DFS witness plan is derived from the raw cutoff-eligible
supporter and graph facts. Primary traversal follows a visible retained
supporter; nonprimary traversal has the interpreter's virtual alternative. -/
theorem plan_of_raw (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree initial protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (tagOrder : ParentTagOrder tree) (short : tree.nodes.size < 65536)
    (witness : S05CutoffOwnershipGeometry.CutoffWitness tree initial protections root position maximum rights.area.contains) :
    Nonempty (Plan tree initial protections root position maximum) := by
  by_cases primary : position = 0
  · subst position
    obtain ⟨index,node,inside,present,eligible⟩ := witness rfl
    have path := path_of_covers tree depth root index node present (rights.covers index inside)
    have visible := GeneralBorrowPrimaryWitnessVisibility.of_order tree tagOrder initial protections maximum .Write index node present eligible
    exact ⟨DuplicatePrefixResidualVisibleWritePlan.ordered tree initial protections root maximum depth graph short index node present visible eligible path⟩
  · exact ⟨DuplicatePrefixResidualWriteWitnessPlan.virtual tree initial protections root position maximum primary⟩

/-- Direct actual-traversal entry with no supplied Plan, Authorization, Row,
operation result or future-state witness. Forest/depth/reciprocity and the
exact source traversal bound are derived from initial graph wellformedness.
Ordinary call-time wellformedness implying the remaining ownership/contributor
conditions is a separate, still open coverage obligation. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree initial protections root position)
    (order : ContributorOrder tree initial protections rights.area.contains)
    (tagOrder : ParentTagOrder tree)
    (witness : S05CutoffOwnershipGeometry.CutoffWitness tree initial protections root position maximum rights.area.contains)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (position != 0)
    result.status = .Completed ∧ SkipStable tree result.location protections maximum rights.area.contains := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨plan⟩ := plan_of_raw tree initial protections root position maximum rights depth graph tagOrder short witness
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have bounded := GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root
  exact S05TraversalSkipStable.access tree initial protections root position maximum weights bounded rights.area plan rights rfl order tagOrder
    witness depth forest graph coherent short profile possible

end DuplicatePrefix.S05TraversalSkipStableEntry
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05TraversalSkipStableEntry.plan_of_raw,
      ``DuplicatePrefix.S05TraversalSkipStableEntry.access] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
