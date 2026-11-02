import duplicate_prefix.GeneralBorrowFreshSharedPaths
namespace DuplicatePrefix.GeneralBorrowForestSharedPrefixPaths
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Extending an existing shared expression with the actual helper child
retains the old mutable path and derives the two-readonly-node prefixPath. -/
theorem extend (before after : TraversalTree) (target expr child : Nat)
    (attached : GeneralBorrowFreshSharedPaths.Attach before after expr child)
    (targetValid : target < before.nodes.size)
    (prefixPath : before.ancestorPath expr = expr :: before.ancestorPath target)
    (exprOutside : expr ∉ before.ancestorPath target) :
    after.ancestorPath child = child :: expr :: after.ancestorPath target ∧
      expr ∉ after.ancestorPath target ∧ child ∉ after.ancestorPath target ∧
      after.ancestorPath target = before.ancestorPath target := by
  have targetInExpr : target ∈ before.ancestorPath expr := by
    rw [prefixPath]
    exact List.mem_cons_of_mem expr (GeneralBorrowFreshSharedPaths.ancestor_self before target)
  have childOutside : child ∉ before.ancestorPath expr := by
    rw [←attached.oldPath expr attached.parentValid attached.parentDifferent]
    exact attached.outsideOld expr attached.parentValid attached.parentDifferent
  have targetDifferent : target ≠ child := by intro same;subst target;exact childOutside targetInExpr
  have old := attached.oldPath target targetValid targetDifferent
  refine ⟨?_,?_,attached.outsideOld target targetValid targetDifferent,old⟩
  · rw [attached.childPath,prefixPath,old]
  · rw [old];exact exprOutside
end DuplicatePrefix.GeneralBorrowForestSharedPrefixPaths
