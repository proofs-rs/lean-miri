import duplicate_prefix.DuplicatePrefixResidualVirtualWriteDFS
import duplicate_prefix.DuplicatePrefixWriteReadSnapshot
namespace DuplicatePrefix.DuplicatePrefixVirtualWriteBothClosure
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The actual virtual Write callback completes and preserves both full S01
query-pair candidates. Arbitrary finite forest shape, cutoffs, exposed states
and protected permissions are allowed by the original raw Write candidate.
Masks, Origin and post scalar compatibility are constructed internally. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (virtual : position ≠ 0)
    (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root position maximum .Write support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections true
    result.status = .Completed ∧
      Authorization tree result.location protections root position maximum .Write support ∧
      Authorization tree result.location protections root position maximum .Read support ∧
      Snapshot tree result.location protections root position maximum .Write support ∧
      Snapshot tree result.location protections root position maximum .Read support ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root position maximum .Write support authorization
  have actual := DuplicatePrefixResidualVirtualWriteDFS.access_authorization tree initial protections root position maximum virtual weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area authorization depth forest coherent short
  have virtualEq : (position != 0) = true := by simp [virtual]
  simp only [virtualEq] at actual
  obtain ⟨complete,writeAfter,afterCoherent,outside⟩ := actual
  have writeSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree _ protections root position maximum .Write support writeAfter afterCoherent short
  have readSnapshot := DuplicatePrefixWriteReadSnapshot.snapshot tree _ protections root position maximum support writeSnapshot afterCoherent short authorization.covers
  have readAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root position maximum .Read support readSnapshot
    authorization.rooted authorization.present authorization.children authorization.covers afterCoherent short
    (fun removed legal => read_removal_empty tree _ protections maximum removed legal)
  exact ⟨complete,writeAfter,readAfter,writeSnapshot,readSnapshot,afterCoherent,outside⟩
end DuplicatePrefix.DuplicatePrefixVirtualWriteBothClosure
