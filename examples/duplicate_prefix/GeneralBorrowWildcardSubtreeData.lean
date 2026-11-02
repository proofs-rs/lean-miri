import duplicate_prefix.GeneralBorrowGraph
import duplicate_prefix.GeneralBorrowWildcardVirtualLeafFold

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeData
open Miri.TreeBorrows Miri.TreeBorrows.Tree

/-- A raw finite-tree work potential. The child sum bounds the actual DFS
stack expansion; no permission, access or operation result occurs here. -/
structure Weights (tree : BorrowTree) where
  weight : UniIndex → Nat
  children : ∀ index node, tree.nodes.get index = some node →
    1 + (node.children.toList.map weight).sum ≤ weight index

/-- Initial location data for an unexposed component. The support need only
contain the selected root and be closed under its real child edges. -/
structure Data (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) where
  support : UniIndex → Prop
  root : support root
  present : ∀ index, support index → ∃ node, tree.nodes.get index = some node
  children : ∀ index node, support index → tree.nodes.get index = some node →
    ∀ child ∈ node.children.toList, support child
  unexposed : ∀ index node, support index → tree.nodes.get index = some node → node.isExposed = false
  zero : ∀ index, support index →
    GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index kind = 0
  owned : ∀ index node, support index → tree.nodes.get index = some node →
    GeneralBorrowPermissions.ForeignOwned (GeneralBorrowWildcardVirtualLeaf.effective location index node)
      (protections.contains node.tag)

end DuplicatePrefix.GeneralBorrowWildcardSubtreeData
