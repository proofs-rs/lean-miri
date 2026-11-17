import duplicate_prefix.GeneralBorrowExposureMarkGraph
namespace DuplicatePrefix.GeneralBorrowExposureMarkCardinality
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposureContributionList
open DuplicatePrefix.GeneralBorrowExposureEntries DuplicatePrefix.GeneralBorrowExposureMarkGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Flag-only marking adds exactly one supporting source contribution at each
ancestor, with no cardinality/cache condition on unrelated components. -/
theorem addition (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (stable : ∀ index node,levels index {node with isExposed := true} = levels index node)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node) (unexposed : node.isExposed = false)
    (query : UniIndex) (kind : AccessKind) :
    cardinality (marked nodes index node) levels query kind = cardinality nodes levels query kind +
      (if supports (levels index node) kind && (walk nodes (nodes.size+1) index).contains query then 1 else 0) := by
  let oldPredicate := contributes nodes levels query kind
  let newPredicate := fun row => contributes (marked nodes index node) levels query kind (replaceRow index {node with isExposed := true} row)
  have paths : ∀ source,walk (marked nodes index node) ((marked nodes index node).size+1) source = walk nodes (nodes.size+1) source := by
    intro source;rw [size nodes index node present];exact walk_mark nodes index node present _ source
  have differentRows : ∀ row ∈ nodes.entries.toList,row ≠ (index,node) → oldPredicate row = newPredicate row := by
    intro row member different
    have notIndex : row.1 ≠ index := by
      intro same
      have lookup := (GeneralBorrowFreshReuseProtection.entries_get nodes row.1 row.2).mp member
      rw [same,present] at lookup
      exact different (Prod.ext same (Option.some.inj lookup).symm)
    simp only [oldPredicate,newPredicate,replaceRow,ite_eq_right notIndex,contributes,paths]
  have balance := balance nodes.entries.toList (entries_nodup nodes) (index,node)
    ((GeneralBorrowFreshReuseProtection.entries_get nodes index node).mpr present) oldPredicate newPredicate differentRows
  have enumeration : cardinality (marked nodes index node) levels query kind = (nodes.entries.toList.filter newPredicate).length := by
    unfold cardinality
    rw [show (marked nodes index node).entries.toList = nodes.entries.toList.map (replaceRow index {node with isExposed := true}) from insert nodes index node _ present]
    rw [List.filter_map,List.length_map]
    rfl
  rw [←enumeration] at balance
  simpa only [oldPredicate,newPredicate,contributes,unexposed,Bool.false_and,Bool.false_eq_true,ite_false,Nat.add_zero,
    replaceRow,ite_true,Bool.true_and,stable,paths,cardinality] using balance

/-- Actual source cache update used by exposeTag preserves the generic cache
invariant after marking a previously unexposed node. Source success is derived
from ParentDepth; finite-width arithmetic remains exactly modular. -/
theorem preserves (cache : ExposedCache) (nodes : UniValMap TreeNode) (good : ParentDepth nodes)
    (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (stable : ∀ index node,levels index {node with isExposed := true} = levels index node)
    (coherent : Coherent cache nodes levels) (index : UniIndex) (node : TreeNode)
    (present : nodes.get index = some node) (unexposed : node.isExposed = false) :
    Coherent (cache.updateExposure (marked nodes index node) index .None (levels index {node with isExposed := true})).cache
      (marked nodes index node) levels := by
  intro query kind
  have markedDepth := depth nodes good index node present
  have markedPresent : (marked nodes index node).get index = some {node with isExposed := true} := GeneralBorrowFreshLocation.get_same nodes index _
  rw [GeneralBorrowExposurePointwise.update_counter cache _ markedDepth index _ markedPresent .None _ query kind,stable,
    size nodes index node present,walk_mark nodes index node present,coherent query kind,
    addition nodes levels stable index node present unexposed query kind]
  by_cases ancestor : query ∈ walk nodes (nodes.size+1) index
  · have contained := List.contains_iff_mem.mpr ancestor
    rw [ite_eq_left ancestor,contained]
    cases value : levels index node <;> cases kind <;>
      simp only [supports,supportsRead,supportsWrite,Bool.and_true,Bool.false_eq_true,ite_false,ite_true,
        delta,Bool.not_false,Bool.true_and,Bool.false_and,Nat.add_zero,UInt16.ofNat_add]
    all_goals rfl
  · have notContained : (walk nodes (nodes.size+1) index).contains query = false := by simp [ancestor]
    rw [ite_eq_right ancestor,notContained]
    simp only [Bool.and_false,Bool.false_eq_true,ite_false,Nat.add_zero]

theorem effective_stable (location : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode) :
    effective location protections index {node with isExposed := true} = effective location protections index node := rfl
end DuplicatePrefix.GeneralBorrowExposureMarkCardinality
