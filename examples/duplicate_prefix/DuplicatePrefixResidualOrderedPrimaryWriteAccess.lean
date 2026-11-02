import duplicate_prefix.DuplicatePrefixResidualSavedWriteDFS
import duplicate_prefix.DuplicatePrefixResidualOrderedWritePlan
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.DuplicatePrefixResidualOrderedPrimaryWriteAccess
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel GeneralBorrowWildcardControlWitness
open GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Actual primary Write for any maximum, under the explicit independent
ParentTagOrder law. S01/RuntimeFacts are not strengthened and are not claimed
to imply this law. Saved entry masks handle arbitrary nested legal removals;
no false initial-skip persistence is used. A real eligible witness is reached
by the literal source DFS, rather than supplied as a success premise. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (order : ParentTagOrder tree)
    (root : UniIndex) (maximum : Option BorTag) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root 0 maximum .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections false
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections maximum .Write removed ∧
      Matches tree initial result.location protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨witness,node,included,present,eligible⟩ := authorization.witness rfl
  have path := path_of_covers tree depth root witness node present (authorization.covers witness included)
  let plan := DuplicatePrefixResidualOrderedWritePlan.ordered tree initial protections root maximum order depth graph short witness node present eligible path
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 maximum .Write support authorization
  have actual := DuplicatePrefixResidualSavedWriteDFS.access tree initial protections root 0 maximum weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan authorization depth forest coherent short
  obtain ⟨done,removed,legal,matching,afterCoherent,outside⟩ := actual
  refine ⟨done,removed,legal,matching,afterCoherent,?_⟩
  have physicalEq : ((0 : Nat) != 0) = false := rfl
  simpa only [physicalEq,area,GeneralBorrowWildcardControlStack.Support.of_authorization] using outside
end DuplicatePrefix.DuplicatePrefixResidualOrderedPrimaryWriteAccess
