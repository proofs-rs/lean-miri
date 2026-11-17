import duplicate_prefix.GeneralBorrowExposureLevelUpdate
namespace DuplicatePrefix.GeneralBorrowExposureLevelTransition
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposureLevelUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- An unexposed node contributes no cache witness at either permission level,
so changing only its effective level needs no cache update. -/
theorem unexposed (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) (coherent : Coherent cache nodes levels)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (hidden : node.isExposed = false) (level : WildcardAccessLevel) :
    Coherent cache nodes (replace levels index level) := by
  intro query kind
  have balance := cardinality_balance nodes levels index node present level query kind
  simp only [contributes,replace,ite_true,hidden,Bool.false_and,Bool.false_eq_true,ite_false,Nat.add_zero] at balance
  rw [coherent query kind,balance]

/-- The actual conditional cache operation used for one effective permission
strength change. It retains the interpreter's genuine updateExposure branch. -/
def operation (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) (index : UniIndex) (node : TreeNode) (level : WildcardAccessLevel) : ExposedCacheUpdate :=
  if node.isExposed then cache.updateExposure nodes index (levels index node) level else ⟨cache,.ok ()⟩

/-- Both actual exposure-flag branches preserve the modular descendant-count
invariant. ParentDepth derives source completion in the exposed branch. -/
theorem preserves (cache : ExposedCache) (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) (coherent : Coherent cache nodes levels)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node) (level : WildcardAccessLevel) :
    (operation cache nodes levels index node level).outcome = .ok () ∧
      Coherent (operation cache nodes levels index node level).cache nodes (replace levels index level) := by
  cases exposed : node.isExposed with
  | false =>
    simp only [operation,exposed,Bool.false_eq_true,ite_false]
    exact ⟨trivial,unexposed cache nodes levels coherent index node present exposed level⟩
  | true =>
    simp only [operation,exposed,ite_true]
    exact ⟨update_exposure_succeeds cache nodes depth index node present (levels index node) level,
      GeneralBorrowExposureLevelUpdate.preserves cache nodes depth levels coherent index node present exposed level⟩
end DuplicatePrefix.GeneralBorrowExposureLevelTransition
