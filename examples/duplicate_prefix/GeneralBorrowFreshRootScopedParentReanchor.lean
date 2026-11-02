import duplicate_prefix.GeneralBorrowParentPositiveReanchor
import duplicate_prefix.GeneralBorrowFreshRootScopedRow
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedParentReanchor
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Restore the parent Full Positive from current unprotected child Full
Positive while retaining every bounded callback support under the same table. -/
theorem positive (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (child parent selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (node : TreeNode) (present : tree.nodeAt child = some node) (edge : node.parent = some parent)
    (absent : protections.contains node.tag = false)
    (old : GeneralBorrowFreshRootScopedRow.Positive tree protections child selected maximum offset len) :
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree protections parent selected maximum offset len) := by
  obtain ⟨base⟩ := GeneralBorrowParentPositiveReanchor.positive tree protections formed child parent selected (some maximum) offset len
    node present edge absent old.base
  refine ⟨⟨base,?_⟩⟩
  intro position valid nonempty start stop
  obtain ⟨baseRow⟩ := base.rows position valid nonempty start stop
  obtain ⟨oldRow⟩ := old.rows position valid nonempty start stop
  exact ⟨⟨baseRow,oldRow.exposed,oldRow.callbacks⟩⟩

theorem twice (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (child parent grandparent selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (childNode parentNode : TreeNode)
    (childPresent : tree.nodeAt child = some childNode) (parentPresent : tree.nodeAt parent = some parentNode)
    (childEdge : childNode.parent = some parent) (parentEdge : parentNode.parent = some grandparent)
    (childAbsent : global.protectedTags.contains childNode.tag = false)
    (parentAbsent : global.protectedTags.contains parentNode.tag = false)
    (old : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags child selected maximum offset len) :
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags grandparent selected maximum offset len) := by
  obtain ⟨middle⟩ := positive tree global.protectedTags runtime.formed.toGraphState child parent selected maximum offset len
    childNode childPresent childEdge childAbsent old
  exact positive tree global.protectedTags runtime.formed.toGraphState parent grandparent selected maximum offset len
    parentNode parentPresent parentEdge parentAbsent middle
end DuplicatePrefix.GeneralBorrowFreshRootScopedParentReanchor
