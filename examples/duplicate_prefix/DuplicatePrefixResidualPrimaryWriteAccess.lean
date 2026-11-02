import duplicate_prefix.DuplicatePrefixResidualScopedWriteDFS
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.DuplicatePrefixResidualPrimaryWriteAccess
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardControlWitness
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The actual no-maximum primary Write callback reaches a real exposed
supporter and completes. Every legal mask is empty here, so current Write
support retains the original support. No plan, source success, leaf shape,
empty allocator pool or ownership profile is a caller premise. Read counters
may change and are deliberately not framed. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root 0 none .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root none .Write protections false
    result.status = .Completed ∧ Matches tree initial result.location protections .Write [] ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨witness,node,included,present,supported⟩ := authorization.witness rfl
  have path := path_of_covers tree depth root witness node present (authorization.covers witness included)
  let plan := DuplicatePrefixResidualWriteWitnessPlan.primary tree initial protections root witness node present supported path depth graph short
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 none .Write support authorization
  have actual := DuplicatePrefixResidualScopedWriteDFS.access tree initial protections root 0 none (.inr rfl) weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan authorization depth forest coherent short
  obtain ⟨done,removed,legal,matching,afterCoherent,outside⟩ := actual
  have empty := no_maximum_removal_empty tree initial protections .Write removed legal
  subst removed
  refine ⟨done,matching,afterCoherent,?_⟩
  have physicalEq : ((0 : Nat) != 0) = false := rfl
  simpa only [physicalEq,area,GeneralBorrowWildcardControlStack.Support.of_authorization] using outside
end DuplicatePrefix.DuplicatePrefixResidualPrimaryWriteAccess
