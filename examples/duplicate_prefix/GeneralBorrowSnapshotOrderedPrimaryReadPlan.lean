import duplicate_prefix.GeneralBorrowSnapshotReadDFSPlan
import duplicate_prefix.GeneralBorrowResidualPrimaryWitness
namespace DuplicatePrefix.GeneralBorrowSnapshotOrderedPrimaryReadPlan
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardControlWitness
open GeneralBorrowWildcardSubtreeStack GeneralBorrowSnapshotReadDFSPlan DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardParentTagOrder
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A primary Read plan with arbitrary cutoff under an independent raw graph
law. ParentTagOrder is NOT claimed to follow from RuntimeFacts or S01. -/
def primary (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root : UniIndex)
    (maximum : Option BorTag) (order : ParentTagOrder tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (witness : UniIndex) (witnessNode : TreeNode) (witnessPresent : tree.nodes.get witness = some witnessNode)
    (eligible : Supports initial protections witness witnessNode maximum .Read) (path : Path tree root witness) :
    WitnessPlan tree initial protections root 0 maximum where
  pending := Pending tree witness
  initial := GeneralBorrowWildcardControlWitness.initial path
  finish := by
    intro seen pending
    exact .inr (GeneralBorrowWildcardControlWitness.empty pending)
  pop := by
    intro location seen stack index node present frame pending skipped
    apply GeneralBorrowWildcardControlWitness.pop stack index false pending
    intro witnessPath
    have noSkip := GeneralBorrowResidualPrimaryWitness.entry_not_skip tree initial protections depth order maximum .Read []
      (DuplicatePrefixResidualSupportAuthorization.empty_removal tree initial protections maximum .Read)
      root index witness node witnessNode present witnessPresent eligible path witnessPath
      (GeneralBorrowWildcardVirtualLeaf.effective location index node)
    rw [GeneralBorrowSnapshotReadState.relation_frame initial location frame,
      ←DuplicatePrefixResidualSupportAuthorization.initial_relation tree initial protections root index node maximum .Read 0 coherent short] at skipped
    rw [noSkip] at skipped
    cases skipped
  expand := by
    intro seen stack index node present pending
    exact GeneralBorrowWildcardControlWitness.expand graph seen stack index node present pending
  post := by
    intro location seen stack index node present frame pending
    apply GeneralBorrowWildcardControlWitness.post seen (GeneralBorrowSnapshotReadDFSPlan.seen location index node maximum protections seen) stack index pending
    · intro already
      simp [GeneralBorrowSnapshotReadDFSPlan.seen,already]
    · intro same
      subst index
      have sameNode := Option.some.inj (witnessPresent.symm.trans present)
      subst node
      have eligibleNow : Supports location protections witness witnessNode maximum .Read := by
        refine ⟨eligible.1,?_,eligible.2.2⟩
        change (GeneralBorrowExposureCardinality.effective location protections witness witnessNode).allows .Read = true
        rw [frame witness witnessNode witnessPresent]
        exact eligible.2.1
      have found := (supports_source location protections witness witnessNode maximum .Read).mp eligibleNow
      simp only [GeneralBorrowSnapshotReadDFSPlan.seen,GeneralBorrowWildcardVirtualLeaf.effective,found,ite_true]

theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) (support : UniIndex → Prop) (order : ParentTagOrder tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root 0 maximum .Read support) :
    Nonempty (WitnessPlan tree initial protections root 0 maximum) := by
  obtain ⟨witness,node,included,present,eligible⟩ := authorization.witness rfl
  have path := path_of_covers tree depth root witness node present (authorization.covers witness included)
  exact ⟨primary tree initial protections root maximum order depth graph coherent short witness node present eligible path⟩

end DuplicatePrefix.GeneralBorrowSnapshotOrderedPrimaryReadPlan
