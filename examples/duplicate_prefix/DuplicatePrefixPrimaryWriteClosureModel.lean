import duplicate_prefix.DuplicatePrefixVirtualWriteClosureState
import duplicate_prefix.DuplicatePrefixResidualClampedQueries
import duplicate_prefix.GeneralBorrowResidualPrimaryWitness
import duplicate_prefix.DuplicatePrefixCrossKindQueryGuard
namespace DuplicatePrefix.DuplicatePrefixPrimaryWriteClosureModel
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowExposureCardinality GeneralBorrowWildcardControlWitness
open DuplicatePrefixVirtualWriteClosureState (residual_decreases)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Only above-cutoff supporters need unchanged permission origins: only they
can enter a later legal mask. Local Write activation is therefore allowed. -/
def CutoffOrigin (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags) (maximum : Option BorTag) : Prop :=
  ∀ index node, tree.nodes.get index = some node → node.isExposed = true → aboveMaximum node maximum = true →
    supports (effective current protections index node) .Write = true →
    ((current.perms.get index).getD node.defaultLocationState).permission = ((initial.perms.get index).getD node.defaultLocationState).permission

theorem removal_append (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (first second : List UniIndex)
    (firstLegal : Removal tree initial protections maximum .Write first) (secondLegal : Removal tree current protections maximum .Write second)
    (matching : Matches tree initial current protections .Write first) (origin : CutoffOrigin tree initial current protections maximum) :
    Removal tree initial protections maximum .Write (first ++ second) := by
  refine ⟨List.nodup_append.mpr ⟨firstLegal.distinct,secondLegal.distinct,?_⟩,?_⟩
  · intro left leftMember right rightMember equal
    subst right
    exact DuplicatePrefixResidualComposition.masks_disjoint tree initial current protections maximum first second matching secondLegal left leftMember rightMember
  · intro index member
    rcases List.mem_append.mp member with old | later
    · exact firstLegal.allowed index old
    · obtain ⟨node,present,allowed⟩ := secondLegal.allowed index later
      have parts := allowed
      simp only [removable,Bool.and_eq_true] at parts
      have same := origin index node present parts.1.1.1 parts.1.1.2 parts.1.2
      exact ⟨node,present,by simpa only [removable,effective,same] using allowed⟩

private theorem filter_equal {α : Type} (items : List α) (selected root : α → Bool)
    (included : ∀ row ∈ items, selected row = true → root row = true)
    (equal : (items.filter selected).length = (items.filter root).length) : items.filter selected = items.filter root := by
  have nested : items.filter selected = (items.filter root).filter selected := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro row member
    have implication := included row member
    cases a : selected row <;> cases b : root row <;> simp_all
  apply List.Sublist.eq_of_length _ equal
  rw [nested]
  exact List.filter_sublist

/-- Equality of residual counts under coverage identifies the actual finite
contributor lists, so it survives all later removal filtering. -/
theorem count_equal_persists (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (covers : Covers tree.nodes root index) (before after : List UniIndex)
    (subset : ∀ query ∈ before, query ∈ after)
    (equal : residualCount tree initial protections .Write before root = residualCount tree initial protections .Write before index) :
    residualCount tree initial protections .Write after root = residualCount tree initial protections .Write after index := by
  have lists : ((tree.nodes.entries.toList.filter (contributes tree.nodes (effective initial protections) index .Write)).filter (fun row => !before.contains row.1)) =
      ((tree.nodes.entries.toList.filter (contributes tree.nodes (effective initial protections) root .Write)).filter (fun row => !before.contains row.1)) := by
    simp only [List.filter_filter]
    apply filter_equal
    · intro row member good
      simp only [Bool.and_eq_true,contributes,List.contains_iff_mem] at good ⊢
      exact ⟨good.1,⟨good.2.1,covers row member good.2.2⟩⟩
    · simpa only [residualCount,List.filter_filter] using equal.symm
  have nested (items : List (UniIndex × TreeNode)) : items.filter (fun row => !after.contains row.1) =
      (items.filter (fun row => !before.contains row.1)).filter (fun row => !after.contains row.1) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro row member
    by_cases old : row.1 ∈ before
    · have later := subset row.1 old;simp [old,later]
    · simp [old]
  unfold residualCount
  rw [nested (tree.nodes.entries.toList.filter (contributes tree.nodes (effective initial protections) root .Write)),
    nested (tree.nodes.entries.toList.filter (contributes tree.nodes (effective initial protections) index .Write)),lists]

theorem root_positive (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) (area : UniIndex → Prop)
    (old : Authorization tree initial protections root 0 maximum .Write area)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed) :
    0 < residualCount tree initial protections .Write removed root := by
  obtain ⟨witness,node,inside,present,eligible⟩ := old.witness rfl
  have path := path_of_covers tree depth root witness node present (old.covers witness inside)
  exact GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth maximum .Write removed legal root witness node present eligible path

theorem local_persists (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (area : UniIndex → Prop)
    (old : Authorization tree initial protections root 0 maximum .Write area) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (inside : area index) (before after : List UniIndex) (legalAfter : Removal tree initial protections maximum .Write after)
    (subset : ∀ query ∈ before, query ∈ after)
    (classified : residualRelation tree initial protections root index node maximum .Write 0 before = some .LocalAccess) :
    residualRelation tree initial protections root index node maximum .Write 0 after = some .LocalAccess := by
  have bound := DuplicatePrefixResidualWriteSkip.residual_dominates tree initial protections before root index (old.covers index inside)
  obtain ⟨_,clampFalse,equal,_⟩ := DuplicatePrefixCrossKindQueryGuard.local_classification _ _ _ _ bound classified
  have laterEqual := count_equal_persists tree initial protections root index (old.covers index inside) before after subset equal
  have positive := root_positive tree initial protections root maximum area old depth after legalAfter
  have localPositive : 0 < residualCount tree initial protections .Write after index := by omega
  simp [residualRelation,clampFalse,classify,laterEqual,Nat.ne_of_gt localPositive]

theorem foreign_persists (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (area : UniIndex → Prop)
    (old : Authorization tree initial protections root 0 maximum .Write area) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (inside : area index) (present : tree.nodes.get index = some node)
    (before after : List UniIndex) (legalAfter : Removal tree initial protections maximum .Write after)
    (subset : ∀ query ∈ before, query ∈ after)
    (classified : residualRelation tree initial protections root index node maximum .Write 0 before = some .ForeignAccess) :
    residualRelation tree initial protections root index node maximum .Write 0 after = some .ForeignAccess := by
  by_cases above : aboveMaximum node maximum = true
  · exact DuplicatePrefixResidualClampedQueries.foreign tree initial protections root index node 0 maximum area old after legalAfter inside present above
  · have clampFalse : aboveMaximum node maximum = false := Bool.eq_false_iff.mpr above
    have zero : residualCount tree initial protections .Write before index = 0 := by
      by_cases zero : residualCount tree initial protections .Write before index = 0
      · exact zero
      · have positive : 0 < residualCount tree initial protections .Write before index := by omega
        have impossible := DuplicatePrefixResidualWriteTransition.classify_foreign_above _ _ _ _ positive classified
        rw [clampFalse] at impossible;cases impossible
    have decrease := residual_decreases tree initial protections before after subset index
    have afterZero : residualCount tree initial protections .Write after index = 0 := by omega
    have positive := root_positive tree initial protections root maximum area old depth after legalAfter
    simp [residualRelation,clampFalse,classify,afterZero,Nat.ne_of_gt positive]
end DuplicatePrefix.DuplicatePrefixPrimaryWriteClosureModel
