import duplicate_prefix.GeneralBorrowExposureCardinality
namespace DuplicatePrefix.GeneralBorrowExposureCardinalityUse
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Empty caches are coherent for any sparse node graph with no exposed node,
regardless of effective permission/protection levels. -/
theorem empty (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (unexposed : ∀ index node,nodes.get index = some node → node.isExposed = false) :
    Coherent {} nodes levels := by
  intro query kind
  have none : nodes.entries.toList.filter (contributes nodes levels query kind) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row member
    have present := (GeneralBorrowFreshReuseProtection.entries_get nodes row.1 row.2).mp member
    simp only [contributes,unexposed row.1 row.2 present,Bool.false_and,Bool.false_eq_true,not_false_eq_true]
  cases kind <;> simp only [counter,cardinality,none,List.length_nil,UniValMap.get,Array.getElem?_empty,Option.getD_none]
  all_goals rfl

/-- The generic descendant invariant supplies the actual wildcard classifier's
root bound; Covers restricts the query to the selected root's component. -/
theorem virtual_classify (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (levels : UniIndex → TreeNode → WildcardAccessLevel) (coherent : Coherent cache nodes levels)
    (short : nodes.size < 65536) (root query : UniIndex) (covers : Covers nodes root query)
    (kind : AccessKind) (onlyForeign : Bool) :
    cache.accessRelatedness root query kind true onlyForeign = some
      (if onlyForeign || GeneralBorrowWildcardRelatednessBounds.count cache query kind == 0 then .ForeignAccess else .EitherAccess) := by
  apply GeneralBorrowWildcardRelatednessBounds.virtual_classify
  have bounded := dominates cache nodes levels coherent short root query covers kind
  cases kind <;> exact bounded
end DuplicatePrefix.GeneralBorrowExposureCardinalityUse
