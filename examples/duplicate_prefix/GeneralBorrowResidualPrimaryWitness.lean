import duplicate_prefix.GeneralBorrowWildcardParentTagOrder
namespace DuplicatePrefix.GeneralBorrowResidualPrimaryWitness
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixCallbackAuthorization
open DuplicatePrefixResidualSupportAuthorization GeneralBorrowWildcardParentTagOrder
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

private theorem support_allows (level : WildcardAccessLevel) (kind : AccessKind) :
    GeneralBorrowExposureCardinality.supports level kind = level.allows kind := by
  cases level <;> cases kind <;> rfl

/-- Every legal residual-removal set retains an eligible supporter: removals
only discard tags above the maximum. This holds for Read and Write. -/
theorem witness_retained (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections maximum kind removed)
    (witness : UniIndex) (node : TreeNode) (present : tree.nodes.get witness = some node)
    (eligible : Supports location protections witness node maximum kind) : witness ∉ removed := by
  apply nondroppable_retained tree location protections maximum kind removed legal witness node present
  have notAbove : aboveMaximum node maximum = false := by
    cases maximum with
    | none => rfl
    | some maximum =>
      have bound : node.tag.value ≤ maximum.value := by
        simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using eligible.2.2
      simp only [aboveMaximum,decide_eq_false_iff_not]
      exact Nat.not_lt.mpr bound
  cases kind <;> simp [removable,notAbove]

/-- An eligible supporter's real path supplies a positive residual count at
all its ancestors, for every legal removal set. -/
theorem positive (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections maximum kind removed)
    (index witness : UniIndex) (node : TreeNode) (present : tree.nodes.get witness = some node)
    (eligible : Supports location protections witness node maximum kind) (path : Path tree index witness) :
    0 < residualCount tree location protections kind removed index := by
  have retained := witness_retained tree location protections maximum kind removed legal witness node present eligible
  have supported : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective location protections witness node) kind = true := by
    rw [support_allows]
    exact eligible.2.1
  apply List.length_pos_iff.mpr
  intro empty
  have member : (witness,node) ∈ ((tree.nodes.entries.toList.filter
      (GeneralBorrowExposureCardinality.contributes tree.nodes
        (GeneralBorrowExposureCardinality.effective location protections) index kind)).filter
      (fun row => !removed.contains row.1)) := by
    apply List.mem_filter.mpr
    refine ⟨?_,by simpa using retained⟩
    apply List.mem_filter.mpr
    refine ⟨(GeneralBorrowFreshReuseProtection.entries_get tree.nodes witness node).mpr present,?_⟩
    simp only [GeneralBorrowExposureCardinality.contributes,eligible.1,supported,Bool.true_and]
    exact List.contains_iff_mem.mpr (path.walk depth)
  rw [empty] at member
  cases member

/-- Independent parent-tag order and eligible witness paths exclude entry
skipping at every primary-root ancestor, under every legal residual set.
This is static candidate arithmetic, not an execution-success premise. -/
theorem entry_not_skip (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections maximum kind removed)
    (root index witness : UniIndex) (node witnessNode : TreeNode)
    (present : tree.nodes.get index = some node) (witnessPresent : tree.nodes.get witness = some witnessNode)
    (eligible : Supports location protections witness witnessNode maximum kind)
    (rootPath : Path tree root witness) (path : Path tree index witness) (state : LocationState) :
    DuplicatePrefixCallbackVisitAuthorization.entrySkip state kind
      (residualRelation tree location protections root index node maximum kind 0 removed) = false := by
  have rootPositive := positive tree location protections depth maximum kind removed legal root witness witnessNode witnessPresent eligible rootPath
  have localPositive := positive tree location protections depth maximum kind removed legal index witness witnessNode witnessPresent eligible path
  have unclamped := path_not_above tree order location protections maximum kind index witness node witnessNode present witnessPresent path eligible
  simp only [residualRelation,unclamped,classify,show (0 != 0) = false from rfl,Bool.false_eq_true,ite_false,Nat.add_zero]
  have notZeroRoot : (residualCount tree location protections kind removed root == 0) = false := by simp [Nat.ne_of_gt rootPositive]
  have notZeroLocal : (residualCount tree location protections kind removed index == 0) = false := by simp [Nat.ne_of_gt localPositive]
  simp only [notZeroRoot,notZeroLocal,Bool.false_eq_true,ite_false]
  split
  · simp [DuplicatePrefixCallbackVisitAuthorization.entrySkip,skip,AccessRelatedness.isForeign]
  · rfl

end DuplicatePrefix.GeneralBorrowResidualPrimaryWitness
