import duplicate_prefix.GeneralBorrowExposedScopedInactiveMixedClosedData
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadData
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
/-- The selected exposed component retains exactly its source inactive profile:
Unique on the anchor path and Disabled off it. Other exposed leaf components
have effective local Write capability, including legal lazy defaults. -/
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop) (writable : Nat→Bool) where
  base : GeneralBorrowExposedScopedInactiveMixedRangeData.Data tree location protections anchor selected head tail support writable
  short : tree.nodes.size<65536
  leaves : ∀index,area.support index→∃node,tree.nodeAt index=some node ∧node.children=#[] ∧node.isExposed=true
  writableLeaves : ∀index node,area.support index→tree.nodeAt index=some node→
    GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location index node)
      .LocalAccess (protections.contains node.tag)
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadData
