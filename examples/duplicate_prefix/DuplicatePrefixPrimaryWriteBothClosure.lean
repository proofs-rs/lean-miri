import duplicate_prefix.DuplicatePrefixNoMaximumWriteDFS
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.DuplicatePrefixPrimaryWriteBothClosure
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardControlWitness
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Actual no-maximum primary Write derives BOTH full raw successor callback
candidates from one initial Write authorization. Initial Snapshot formation,
real DFS completion, final Write Snapshot preservation and Read conversion
are all proved internally; no successor/frame/success premise is accepted.
Read counters may change. This closes one callback, not the full function. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root 0 none .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root none .Write protections false
    result.status = .Completed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      Matches tree initial result.location protections .Write [] ∧
      Snapshot tree result.location protections root 0 none .Write support ∧
      Snapshot tree result.location protections root 0 none .Read support ∧
      Authorization tree result.location protections root 0 none .Write support ∧
      Authorization tree result.location protections root 0 none .Read support ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨witness,node,included,present,eligible⟩ := authorization.witness rfl
  have path := path_of_covers tree depth root witness node present (authorization.covers witness included)
  let plan := DuplicatePrefixResidualWriteWitnessPlan.primary tree initial protections root witness node present eligible path depth graph short
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 none .Write support authorization
  have actual := DuplicatePrefixNoMaximumWriteDFS.access tree initial protections root 0 none rfl weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan authorization depth forest coherent short
  have physicalEq : ((0 : Nat) != 0) = false := rfl
  simp only [physicalEq] at actual
  obtain ⟨done,writeSnapshot,removed,legal,matching,afterCoherent,outside⟩ := actual
  have empty := no_maximum_removal_empty tree initial protections .Write removed legal
  subst removed
  have readSnapshot := DuplicatePrefixWriteReadSnapshot.snapshot tree _ protections root 0 none support writeSnapshot afterCoherent short authorization.covers
  have writeAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root 0 none .Write support writeSnapshot
    authorization.rooted authorization.present authorization.children authorization.covers afterCoherent short
    (by intro removed legal;exact no_maximum_removal_empty tree _ protections .Write removed legal)
  have readAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root 0 none .Read support readSnapshot
    authorization.rooted authorization.present authorization.children authorization.covers afterCoherent short
    (by intro removed legal;exact read_removal_empty tree _ protections none removed legal)
  refine ⟨done,afterCoherent,matching,writeSnapshot,readSnapshot,writeAfter,readAfter,?_⟩
  simpa only [area,GeneralBorrowWildcardControlStack.Support.of_authorization] using outside
end DuplicatePrefix.DuplicatePrefixPrimaryWriteBothClosure
