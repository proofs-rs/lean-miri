import duplicate_prefix.DuplicatePrefixResidualComposition
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.DuplicatePrefixResidualWriteSkip
namespace DuplicatePrefix.DuplicatePrefixResidualClampedQueries
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

private theorem classify_clamped (rootCount localCount : Nat) (virtual : Bool) :
    classify rootCount localCount virtual true = some .ForeignAccess ∨ classify rootCount localCount virtual true = none := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases equal : rootCount = localCount <;>
    by_cases plusEqual : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

private theorem foreign_gap (rootCount localCount : Nat) (virtual : Bool)
    (bounded : localCount ≤ rootCount) :
    classify rootCount localCount virtual true = some .ForeignAccess ↔ localCount < rootCount + (if virtual then 1 else 0) := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases equal : rootCount = localCount <;>
    by_cases plusEqual : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

def without (removed : List UniIndex) (index : UniIndex) : List UniIndex :=
  removed.filter (fun query => decide (query ≠ index))

private theorem without_legal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (removed : List UniIndex) (index : UniIndex)
    (legal : Removal tree location protections maximum .Write removed) :
    Removal tree location protections maximum .Write (without removed index) := by
  refine ⟨legal.distinct.filter _,?_⟩
  intro query member
  exact legal.allowed query ((List.mem_filter.mp member).1)

private theorem count_without (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (index query : UniIndex) (member : index ∈ removed) :
    residualCount tree location protections .Write removed query =
      residualCount tree location protections .Write (index :: without removed index) query := by
  unfold residualCount
  apply congrArg List.length
  apply List.filter_congr
  intro row inside
  apply congrArg Bool.not
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,List.mem_cons,without,List.mem_filter,decide_eq_true_eq]
  by_cases same : row.1 = index <;> simp_all

/-- An above-cutoff node excluded from a legal mask has a Foreign query:
its original same-query authorization rules out the clamped absent case. -/
theorem retained_foreign (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (position : Nat) (maximum : Option BorTag)
    (kind : AccessKind) (area : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum kind area)
    (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed)
    (inside : area index) (present : tree.nodes.get index = some node) (retained : index ∉ removed)
    (above : aboveMaximum node maximum = true) :
    residualRelation tree location protections root index node maximum kind position removed = some .ForeignAccess := by
  have authorized := old.queries removed removed legal legal (fun _ member => member) index node inside present retained
  have scalar := (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ kind _ _).mp authorized
  rcases classify_clamped (residualCount tree location protections kind removed root)
    (residualCount tree location protections kind removed index) (position != 0) with foreign | absent
  · simpa only [residualRelation,above] using foreign
  · have none : residualRelation tree location protections root index node maximum kind position removed = none := by
      simpa only [residualRelation,above] using absent
    rw [none] at scalar
    exact False.elim scalar

/-- Full Write authorization implies Foreign classification of every
above-cutoff support node, even when that node belongs to the removal mask.
Deleting its own contribution subtracts equally from root/local counts and
preserves the strict gap derived from the legal mask without that node.
No tag-order or witness-separation premise is needed for this data fact. -/
theorem foreign (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (position : Nat) (maximum : Option BorTag)
    (area : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum .Write area)
    (removed : List UniIndex) (legal : Removal tree location protections maximum .Write removed)
    (inside : area index) (present : tree.nodes.get index = some node)
    (above : aboveMaximum node maximum = true) :
    residualRelation tree location protections root index node maximum .Write position removed = some .ForeignAccess := by
  by_cases retained : index ∉ removed
  · exact retained_foreign tree location protections root index node position maximum .Write area old removed legal inside present retained above
  · have member : index ∈ removed := by simpa using retained
    have filteredLegal := without_legal tree location protections maximum removed index legal
    have notFiltered : index ∉ without removed index := by simp [without]
    have filteredForeign := retained_foreign tree location protections root index node position maximum .Write area old (without removed index) filteredLegal inside present notFiltered above
    have covers := old.covers index inside
    have filteredBound := DuplicatePrefixResidualWriteSkip.residual_dominates tree location protections (without removed index) root index covers
    have bound := DuplicatePrefixResidualWriteSkip.residual_dominates tree location protections removed root index covers
    have gap := (foreign_gap _ _ _ filteredBound).mp (by simpa only [residualRelation,above] using filteredForeign)
    have rootBalance := count_cons_balance tree location protections .Write (without removed index) root index node present
    have indexBalance := count_cons_balance tree location protections .Write (without removed index) index index node present
    rw [←count_without tree location protections removed index root member] at rootBalance
    rw [←count_without tree location protections removed index index member] at indexBalance
    have own : index ∈ walk tree.nodes (tree.nodes.size+1) index := by simp [walk]
    have ancestor := covers (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present) own
    have rootContains : (walk tree.nodes (tree.nodes.size+1) index).contains root = true := List.contains_iff_mem.mpr ancestor
    have ownContains : (walk tree.nodes (tree.nodes.size+1) index).contains index = true := List.contains_iff_mem.mpr own
    have sameContribution : contributes tree.nodes (levels location protections (without removed index)) root .Write (index,node) =
        contributes tree.nodes (levels location protections (without removed index)) index .Write (index,node) := by
      simp only [contributes,rootContains,ownContains]
    rw [sameContribution] at rootBalance
    have finalGap : residualCount tree location protections .Write removed index < residualCount tree location protections .Write removed root + (if (position != 0) then 1 else 0) := by omega
    have classified := (foreign_gap _ _ _ bound).mpr finalGap
    simpa only [residualRelation,above] using classified
end DuplicatePrefix.DuplicatePrefixResidualClampedQueries
