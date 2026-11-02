import duplicate_prefix.GeneralBorrowStructuralHistoryRootAuthorityState
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryRootAuthorityInsert
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryRootAuthorityAt
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] UniValMap.insert

/-- A real isolated-root insertion forms its lazy SIFA state from raw policy
consistency and physical vacancy Clean, without imposing any old permissions. -/
theorem insert (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (index : UniIndex) (newNode : TreeNode) (vacant : tree.nodes.get index=none)
    (initial : At tree location root)
    (newDefault : Allowed root index newNode.defaultLocationState) :
    At {tree with nodes:=tree.nodes.insert index newNode} location root := by
  constructor
  · intro query node present
    change (tree.nodes.insert index newNode).get query=some node at present
    by_cases same : query=index
    · subst query
      have equal : newNode=node := Option.some.inj ((GeneralBorrowFreshLocation.get_same tree.nodes index newNode).symm.trans present)
      subst node
      rw [initial.vacant index vacant]
      exact newDefault
    · rw [GeneralBorrowFreshLocation.get_other tree.nodes index query newNode same] at present
      exact initial.present query node present
  · intro query missing
    change (tree.nodes.insert index newNode).get query=none at missing
    have different : query≠index := by
      intro same
      subst query
      rw [GeneralBorrowFreshLocation.get_same] at missing
      cases missing
    rw [GeneralBorrowFreshLocation.get_other tree.nodes index query newNode different] at missing
    exact initial.vacant query missing
end DuplicatePrefix.GeneralBorrowStructuralHistoryRootAuthorityInsert
