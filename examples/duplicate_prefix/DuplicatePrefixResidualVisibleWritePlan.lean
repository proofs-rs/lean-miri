import duplicate_prefix.DuplicatePrefixResidualWriteWitnessPlan
import duplicate_prefix.GeneralBorrowPrimaryWitnessVisibility
namespace DuplicatePrefix.DuplicatePrefixResidualVisibleWritePlan
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardControlWitness GeneralBorrowWildcardSubtreeStack
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open DuplicatePrefixResidualWriteWitnessPlan GeneralBorrowWildcardParentTagOrder
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

private theorem supports_allows (level : WildcardAccessLevel) : GeneralBorrowExposureCardinality.supports level .Write = level.allows .Write := by
  cases level <;> rfl

/-- An eligible initial witness survives every legal Write removal mask. -/
theorem supporter_current (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (model : Model tree initial current protections maximum)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (eligible : Supports initial protections index node maximum .Write) : Supports current protections index node maximum .Write := by
  obtain ⟨removed,legal,matching⟩ := model
  have retained := GeneralBorrowResidualPrimaryWitness.witness_retained tree initial protections maximum .Write removed legal index node present eligible
  have same := matching index node present eligible.1
  have equal : (GeneralBorrowExposureCardinality.effective current protections index node).allows .Write =
      (GeneralBorrowExposureCardinality.effective initial protections index node).allows .Write := by
    simpa [levels,retained,supports_allows] using same
  exact ⟨eligible.1,equal.trans eligible.2.1,eligible.2.2⟩

/-- Primary Write witness bookkeeping from static visibility on one eligible path. -/
def ordered (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root : UniIndex)
    (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree) (short : tree.nodes.size < 65536)
    (witness : UniIndex) (witnessNode : TreeNode) (present : tree.nodes.get witness = some witnessNode)
    (visible : GeneralBorrowPrimaryWitnessVisibility.Visible tree maximum witness)
    (eligible : Supports initial protections witness witnessNode maximum .Write) (path : Path tree root witness) :
    Plan tree initial protections root 0 maximum where
  pending := Pending tree witness
  initial := GeneralBorrowWildcardControlWitness.initial path
  finish := by intro seen pending;exact .inr (GeneralBorrowWildcardControlWitness.empty pending)
  pop := by
    intro current seen stack index node found model coherent pending skipped
    apply GeneralBorrowWildcardControlWitness.pop stack index false pending
    intro witnessPath
    obtain ⟨removed,legal,matching⟩ := model
    have noSkip := GeneralBorrowPrimaryWitnessVisibility.entry_not_skip tree initial protections depth maximum .Write removed legal
      root index witness node witnessNode found present eligible visible path witnessPath (GeneralBorrowWildcardVirtualLeaf.effective current index node)
    rw [relation_matches tree initial current protections .Write removed matching coherent short root index node maximum 0,noSkip] at skipped
    cases skipped
  expand := by intros;exact GeneralBorrowWildcardControlWitness.expand graph _ _ _ _ (by assumption) (by assumption)
  post := by
    intro current seen stack index node found model pending
    apply GeneralBorrowWildcardControlWitness.post seen (DuplicatePrefixResidualWriteDFSInvariant.seen current index node maximum protections seen) stack index pending
    · intro already;simp [DuplicatePrefixResidualWriteDFSInvariant.seen,already]
    · intro same
      subst index
      have nodeEq := Option.some.inj (present.symm.trans found)
      subst node
      have currentEligible := supporter_current tree initial current protections maximum model witness witnessNode present eligible
      have yes := (supports_source current protections witness witnessNode maximum .Write).mp currentEligible
      simp only [DuplicatePrefixResidualWriteDFSInvariant.seen,GeneralBorrowWildcardVirtualLeaf.effective,yes,ite_true]
end DuplicatePrefix.DuplicatePrefixResidualVisibleWritePlan
