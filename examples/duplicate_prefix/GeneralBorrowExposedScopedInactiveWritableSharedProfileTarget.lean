import duplicate_prefix.GeneralBorrowExposedInactiveConstructor
import duplicate_prefix.GeneralBorrowFreshSharedPaths
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedProfileTarget
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Removing two fresh hidden prefix nodes changes neither the Unique exposed
ancestor set nor the retained Disabled offpath handles. -/
theorem profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (child expr target : UniIndex) (support : Nat→Prop) (exprNode childNode : TreeNode)
    (exprPresent : tree.nodeAt expr=some exprNode) (childPresent : tree.nodeAt child=some childNode)
    (exprHidden : exprNode.isExposed=false) (childHidden : childNode.isExposed=false)
    (paths : (source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat)
    (initial : GeneralBorrowExposedInactiveConstructor.Profile tree location child support) :
    GeneralBorrowExposedInactiveConstructor.Profile tree location target support := by
  intro query node included present exposed
  have notExpr : query≠expr := by
    intro equal;subst query
    have equalNode:=Option.some.inj (present.symm.trans exprPresent)
    subst node;rw [exprHidden] at exposed;cases exposed
  have notChild : query≠child := by
    intro equal;subst query
    have equalNode:=Option.some.inj (present.symm.trans childPresent)
    subst node;rw [childHidden] at exposed;cases exposed
  have previous:=initial query node included present exposed
  change (query.toNat∈(source_normal_projection tree location protections).topology.ancestorPath child.toNat ∧_) ∨
    (query.toNat∉(source_normal_projection tree location protections).topology.ancestorPath child.toNat ∧_) at previous
  change (query.toNat∈(source_normal_projection tree location protections).topology.ancestorPath target.toNat ∧_) ∨
    (query.toNat∉(source_normal_projection tree location protections).topology.ancestorPath target.toNat ∧_)
  rw [paths] at previous
  rcases previous with good|bad
  · refine Or.inl ⟨?_,good.2⟩
    have member:=good.1
    simp only [List.mem_cons] at member
    rcases member with equal|equal|member
    · exact False.elim (notChild (GeneralBorrowNodeUpdate.index_injective _ _ equal))
    · exact False.elim (notExpr (GeneralBorrowNodeUpdate.index_injective _ _ equal))
    · exact member
  · exact Or.inr ⟨fun member=>bad.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)),bad.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedProfileTarget
