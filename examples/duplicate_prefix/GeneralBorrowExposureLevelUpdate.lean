import duplicate_prefix.GeneralBorrowExposureContributionList
namespace DuplicatePrefix.GeneralBorrowExposureLevelUpdate
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposurePointwise
open DuplicatePrefix.GeneralBorrowExposureContributionList
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def replace (levels : UniIndex → TreeNode → WildcardAccessLevel) (index : UniIndex) (level : WildcardAccessLevel) :
    UniIndex → TreeNode → WildcardAccessLevel := fun query node => if query = index then level else levels query node

/-- Exact finite-source balance when one effective permission/protection level
changes; the actual optional-slot enumeration supplies source distinctness. -/
theorem cardinality_balance (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node) (level : WildcardAccessLevel)
    (query : UniIndex) (kind : AccessKind) :
    cardinality nodes (replace levels index level) query kind +
      (if contributes nodes levels query kind (index,node) then 1 else 0) =
    cardinality nodes levels query kind +
      (if contributes nodes (replace levels index level) query kind (index,node) then 1 else 0) := by
  apply balance nodes.entries.toList (entries_nodup nodes) (index,node)
    ((GeneralBorrowFreshReuseProtection.entries_get nodes index node).mpr present)
  intro row member different
  have indexDifferent : row.1 ≠ index := by
    intro same
    have lookup := (GeneralBorrowFreshReuseProtection.entries_get nodes row.1 row.2).mp member
    rw [same,present] at lookup
    apply different
    exact Prod.ext same (Option.some.inj lookup).symm
  simp only [contributes,replace,ite_eq_right indexDifferent]

/-- The actual source updateExposure preserves descendant cardinality when an
exposed source changes effective local permission/protection strength. All
UInt16 arithmetic (including wrap) is proved; no success/output premise enters. -/
theorem preserves (cache : ExposedCache) (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) (coherent : Coherent cache nodes levels)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (exposed : node.isExposed = true) (level : WildcardAccessLevel) :
    Coherent (cache.updateExposure nodes index (levels index node) level).cache nodes (replace levels index level) := by
  intro query kind
  rw [update_counter cache nodes depth index node present (levels index node) level query kind,coherent query kind]
  have balanced := cardinality_balance nodes levels index node present level query kind
  have exactDelta := modular_delta (cardinality nodes levels query kind)
    (cardinality nodes (replace levels index level) query kind)
    (contributes nodes levels query kind (index,node))
    (contributes nodes (replace levels index level) query kind (index,node)) balanced
  by_cases ancestor : query ∈ walk nodes (nodes.size+1) index
  · have contained : (walk nodes (nodes.size+1) index).contains query = true := List.contains_iff_mem.mpr ancestor
    simp only [contributes,exposed,replace,ite_true,Bool.true_and,contained,Bool.and_true] at exactDelta
    rw [ite_eq_left ancestor]
    exact exactDelta.symm
  · have notContained : (walk nodes (nodes.size+1) index).contains query = false := by simp [ancestor]
    simp only [contributes,exposed,replace,ite_true,Bool.true_and,notContained,Bool.and_false] at exactDelta
    rw [ite_eq_right ancestor]
    simpa only [delta,Bool.not_false,Bool.false_and,Bool.and_false,Bool.false_eq_true,ite_false] using exactDelta.symm
end DuplicatePrefix.GeneralBorrowExposureLevelUpdate
