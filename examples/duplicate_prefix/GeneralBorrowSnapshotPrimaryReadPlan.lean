import duplicate_prefix.GeneralBorrowSnapshotReadDFSPlan
namespace DuplicatePrefix.GeneralBorrowSnapshotPrimaryReadPlan
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardPrimaryReadWitness
open GeneralBorrowWildcardControlWitness GeneralBorrowSnapshotReadDFSPlan
open GeneralBorrowWildcardSubtreeStack DuplicatePrefixCallbackAuthorization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem allows_support (level : WildcardAccessLevel) :
    GeneralBorrowExposureCardinality.supports level .Read = level.allows .Read := by cases level <;> rfl

/-- Concrete primary-root witness bookkeeping for an unfiltered Read. The
plan is built from raw witness/graph/cache data; it assumes no DFS outcome. -/
def primary (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root : UniIndex)
    (data : Data tree initial protections root)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) : WitnessPlan tree initial protections root 0 none where
  pending := Pending tree data.witness
  initial := GeneralBorrowWildcardControlWitness.initial data.path
  finish := by
    intro witness pending
    exact .inr (GeneralBorrowWildcardControlWitness.empty pending)
  pop := by
    intro location witness stack index node present frame pending skipped
    simp only [relation,aboveMaximum,show (0 != 0) = false from rfl] at skipped
    apply GeneralBorrowWildcardControlReadWitness.pop tree initial location protections depth coherent short frame
      root index data.witness data.node data.present data.supports.1 _ data.path
      (GeneralBorrowWildcardVirtualLeaf.effective location index node) stack false witness pending skipped
    rw [allows_support]
    exact data.supports.2.1
  expand := by
    intro witness stack index node present pending
    exact GeneralBorrowWildcardControlWitness.expand graph witness stack index node present pending
  post := by
    intro location witness stack index node present frame pending
    apply GeneralBorrowWildcardControlWitness.post witness (seen location index node none protections witness) stack index pending
    · intro already
      simp [seen,already]
    · intro same
      subst index
      have sameNode := Option.some.inj (data.present.symm.trans present)
      subst node
      have found := found_current data location frame
      simpa only [seen,GeneralBorrowWildcardVirtualLeaf.effective,found,ite_true] using (rfl : true = true)

/-- S01's no-maximum primary witness forms the source DFS ghost plan. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root : UniIndex)
    (support : UniIndex → Prop) (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root 0 none .Read support) :
    Nonempty (WitnessPlan tree initial protections root 0 none) := by
  obtain ⟨data⟩ := GeneralBorrowWildcardPrimaryReadWitness.of_authorization tree initial protections root support depth authorization
  exact ⟨primary tree initial protections root data depth graph coherent short⟩

end DuplicatePrefix.GeneralBorrowSnapshotPrimaryReadPlan
