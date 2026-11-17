import duplicate_prefix.GeneralBorrowFreshReuseNode
import duplicate_prefix.GeneralBorrowFreshMetadata
namespace DuplicatePrefix.GeneralBorrowFreshReuseBudget
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Rank capacity reserved for a chain of fresh descendants. This is a data
certificate; it does not assume that any borrow operation succeeds. Arbitrary
ParentDepth certificates may have unnecessarily large ranks. -/
def Budget {nodes : UniValMap TreeNode} (depth : ParentDepth nodes) (parent : UniIndex) (remaining : Nat) : Prop :=
  depth.depth parent + remaining ≤ nodes.size

set_option autoImplicit false in
/-- One reserved descendant suffices for the reuse constructor's strict slack. -/
theorem slack {nodes : UniValMap TreeNode} (depth : ParentDepth nodes) (parent : UniIndex) (remaining : Nat)
    (budget : Budget depth parent (remaining+1)) : depth.depth parent < nodes.size := by
  unfold Budget at budget
  omega

set_option autoImplicit false in
/-- Inserting a reused child consumes exactly one unit of descendant rank
capacity. Remaining table slots are not allocated by extending the array. -/
theorem child (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (present : nodes.get parent = some parentNode) (edge : newNode.parent = some parent)
    (remaining : Nat) (budget : Budget depth parent (remaining+1)) :
    Budget (GeneralBorrowFreshReuseNode.attached_depth nodes depth index parent parentNode newNode
      valid vacant present edge (slack depth parent remaining budget)) index remaining := by
  have parentDifferent := GeneralBorrowFreshReuseNode.parent_not_vacant nodes index parent parentNode vacant present
  have parentAfter := (GeneralBorrowFreshLocation.get_other nodes index parent newNode parentDifferent).trans present
  unfold Budget
  change (if index = index then depth.depth parent+1 else depth.depth index) + remaining ≤ _
  simp only [ite_true]
  unfold GeneralBorrowFreshNode.attachedNodes
  rw [insert_existing_size (nodes.insert index newNode) parent parentNode _ parentAfter,
    GeneralBorrowFreshReuseNode.bounded_size nodes index newNode valid]
  unfold Budget at budget
  omega

set_option autoImplicit false in
/-- Every old nonreused anchor retains its complete rank budget. -/
theorem old (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (present : nodes.get parent = some parentNode) (edge : newNode.parent = some parent)
    (parentSlack : depth.depth parent < nodes.size) (different : query ≠ index)
    (remaining : Nat) (budget : Budget depth query remaining) :
    Budget (GeneralBorrowFreshReuseNode.attached_depth nodes depth index parent parentNode newNode
      valid vacant present edge parentSlack) query remaining := by
  have parentDifferent := GeneralBorrowFreshReuseNode.parent_not_vacant nodes index parent parentNode vacant present
  have parentAfter := (GeneralBorrowFreshLocation.get_other nodes index parent newNode parentDifferent).trans present
  unfold Budget
  change (if query = index then depth.depth parent+1 else depth.depth query) + remaining ≤ _
  simp only [different,ite_false]
  unfold GeneralBorrowFreshNode.attachedNodes
  rw [insert_existing_size (nodes.insert index newNode) parent parentNode _ parentAfter,
    GeneralBorrowFreshReuseNode.bounded_size nodes index newNode valid]
  exact budget

set_option autoImplicit false in
/-- The existing actual-constructor/SIFA treeShape bridge transports the budget
without inspecting locations, protections or the newChild operation outcome. -/
theorem shape (before after : BorrowTree)
    (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (depth : ParentDepth before.nodes) (parent : UniIndex) (remaining : Nat)
    (budget : Budget depth parent remaining) :
    Budget (GeneralBorrowFreshMetadata.parent_depth before after same depth) parent remaining := by
  unfold Budget
  change depth.depth parent + remaining ≤ after.nodes.size
  rw [GeneralBorrowFreshMetadata.node_size before after same]
  exact budget
set_option autoImplicit false in
/-- A parentless forest admits a deliberately saturated rank certificate,
even if its sparse table contains vacant slots. Graph validity alone cannot
force strict slack for the particular ParentDepth value supplied by a caller. -/
def saturated (nodes : UniValMap TreeNode)
    (parentless : ∀ index node, nodes.get index = some node → node.parent = none) : ParentDepth nodes where
  depth := fun _ => nodes.size
  bounded := by intro _ _ _; exact Nat.le_refl _
  parent := by
    intro index node present earlier edge
    rw [parentless index node present] at edge
    cases edge

set_option autoImplicit false in
theorem saturated_no_slack (nodes : UniValMap TreeNode)
    (parentless : ∀ index node, nodes.get index = some node → node.parent = none) (parent : UniIndex) :
    ¬ (saturated nodes parentless).depth parent < nodes.size := by
  change ¬ nodes.size < nodes.size
  omega

end DuplicatePrefix.GeneralBorrowFreshReuseBudget
