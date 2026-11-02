import duplicate_prefix.GeneralBorrowParentRestoreNormal
import duplicate_prefix.GeneralBorrowReadObserverPath
namespace DuplicatePrefix.GeneralBorrowParentPositiveReanchor
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralBorrowAnchor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Reanchor one complete row under the SAME current protector table. Every
callback/root/cutoff fact is inherited from the child; parent path and Normal
permissions follow from the actual edge and the child's unprotected tag. -/
theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (child parent selected : UniIndex) (maximum : Option BorTag)
    (node : TreeNode) (present : tree.nodeAt child = some node) (edge : node.parent = some parent)
    (absent : protections.contains node.tag = false)
    (old : DuplicatePrefixBorrowAuthorization.Row tree location protections (some child) (some selected) maximum) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections (some parent) (some selected) maximum) := by
  refine ⟨{
    wildcard := by intro impossible;cases impossible
    rootPath := ?_
    rootPresent := old.rootPresent
    cutoff := old.cutoff
    normal := ?_
    callbacks := old.callbacks }⟩
  · intro anchor equal
    have equal : anchor = parent := Option.some.inj equal.symm
    subst anchor
    have sourcePath : ∀ otherLocation otherProtections,
        ((source_normal_projection tree otherLocation otherProtections).topology.ancestorPath child.toNat).getLast? = some selected.toNat := by
      intro otherLocation otherProtections
      have same : (source_normal_projection tree otherLocation otherProtections).topology =
          (source_normal_projection tree location protections).topology := by unfold_general_projection;rfl
      rw [same]
      exact old.rootPath child rfl
    exact GeneralBorrowReadObserverPath.edge_root tree formed child parent selected node present edge sourcePath location protections
  · intro anchor equal
    have equal : anchor = parent := Option.some.inj equal.symm
    subst anchor
    obtain ⟨normal⟩ := old.normal child rfl
    exact GeneralBorrowParentRestoreNormal.normal tree location protections protections child parent node formed present edge
      (fun _ held => held) absent normal

/-- Current child Positive and actual graph/protector data derive FULL parent
Positive on the same owner window. No parent permissions or future facts are
premises. No operation is run or assumed by this reanchoring lemma. -/
theorem positive (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (child parent selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (node : TreeNode) (present : tree.nodeAt child = some node) (edge : node.parent = some parent)
    (absent : protections.contains node.tag = false)
    (old : DuplicatePrefixBorrowAuthorization.Positive tree protections (some child) (some selected) maximum offset len) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree protections (some parent) (some selected) maximum offset len) := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨parentNode,parentPresent,_⟩ := depth.parent child node present parent edge
  refine ⟨{
    positive := old.positive
    bounds := old.bounds
    sourcePresent := ?_
    wildcardRoot := by intro impossible;cases impossible
    rows := ?_ }⟩
  · intro anchor equal
    have equal : anchor = parent := Option.some.inj equal.symm
    subst anchor
    exact ⟨parentNode,parentPresent⟩
  · intro position valid nonempty beforeUpper afterLower
    obtain ⟨oldRow⟩ := old.rows position valid nonempty beforeUpper afterLower
    exact row tree _ protections formed child parent selected maximum node present edge absent oldRow

/-- Two unprotected child edges restore the original grandparent's full
owner-window capability under the SAME current table. -/
theorem twice (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (child parent grandparent selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (childNode parentNode : TreeNode)
    (childPresent : tree.nodeAt child = some childNode) (parentPresent : tree.nodeAt parent = some parentNode)
    (childEdge : childNode.parent = some parent) (parentEdge : parentNode.parent = some grandparent)
    (childAbsent : global.protectedTags.contains childNode.tag = false)
    (parentAbsent : global.protectedTags.contains parentNode.tag = false)
    (old : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some child) (some selected) maximum offset len) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some grandparent) (some selected) maximum offset len) := by
  obtain ⟨parentPositive⟩ := positive tree global.protectedTags runtime.formed.toGraphState child parent selected maximum offset len
    childNode childPresent childEdge childAbsent old
  exact positive tree global.protectedTags runtime.formed.toGraphState parent grandparent selected maximum offset len
    parentNode parentPresent parentEdge parentAbsent parentPositive
end DuplicatePrefix.GeneralBorrowParentPositiveReanchor
