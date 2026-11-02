import duplicate_prefix.GeneralBorrowFreshNode
import duplicate_prefix.GeneralBorrowGraph
namespace DuplicatePrefix.GeneralBorrowFreshGraph
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The concrete-parent topology mutations performed by newChild, before its
range-state installation and SIFA update. The allocation's roots are retained. -/
def attached (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode) : BorrowTree :=
  {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}

def updatedParent (parentNode : TreeNode) (index : UniIndex) : TreeNode :=
  {parentNode with children := parentNode.children.push index}

theorem parent_lookup (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode) :
    (attached tree index parent parentNode newNode).nodeAt parent = some (updatedParent parentNode index) := by
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd
      (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  dsimp only [attached,BorrowTree.nodeAt,attachedNodes,updatedParent]
  exact insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode
    {parentNode with children := parentNode.children.push index} old

theorem new_lookup (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode) :
    (attached tree index parent parentNode newNode).nodeAt index = some newNode := by
  have different := parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd different).trans parentPresent
  dsimp only [attached,BorrowTree.nodeAt,attachedNodes]
  exact (insert_existing_get_other (tree.nodes.insert index newNode) parent index parentNode
    {parentNode with children := parentNode.children.push index} old (Ne.symm different)).trans (append_get_same tree.nodes index newNode atEnd)

theorem other_lookup (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (notParent : query ≠ parent) (notNew : query ≠ index) :
    (attached tree index parent parentNode newNode).nodeAt query = tree.nodeAt query := by
  have different := parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd different).trans parentPresent
  dsimp only [attached,BorrowTree.nodeAt,attachedNodes]
  exact (insert_existing_get_other (tree.nodes.insert index newNode) parent query parentNode
    {parentNode with children := parentNode.children.push index} old notParent).trans (append_get_other tree.nodes index query newNode atEnd notNew)

/-- Any old stored node remains stored; only the parent's children field changes. -/
theorem old_present (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode oldNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (present : tree.nodeAt query = some oldNode) :
    ∃ node, (attached tree index parent parentNode newNode).nodeAt query = some node := by
  by_cases same : query = parent
  · subst query
    exact ⟨_,parent_lookup tree index parent parentNode newNode atEnd parentPresent⟩
  · have notNew : query ≠ index := by
      intro equal
      have valid := lookup_valid tree.nodes query oldNode present
      rw [equal,atEnd] at valid
      omega
    exact ⟨oldNode,(other_lookup tree index parent query parentNode newNode atEnd parentPresent same notNew).trans present⟩

/-- Attaching a fresh leaf preserves the actual child-node lookup invariant
for every old node of an arbitrary caller topology. -/
theorem child_nodes (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (leaf : newNode.children = #[]) (before : GeneralBorrowGraph.ChildNodes tree) :
    GeneralBorrowGraph.ChildNodes (attached tree index parent parentNode newNode) := by
  intro query node lookup child member
  by_cases isParent : query = parent
  · subst query
    rw [parent_lookup tree index parent parentNode newNode atEnd parentPresent] at lookup
    cases lookup
    have split : child ∈ parentNode.children.toList ∨ child = index := by
      simpa only [updatedParent,Array.toList_push,List.mem_append,List.mem_singleton] using member
    rcases split with old | fresh
    · obtain ⟨childNode,present⟩ := before parent parentNode parentPresent child old
      exact old_present tree index parent child parentNode newNode childNode atEnd parentPresent present
    · subst child
      exact ⟨_,new_lookup tree index parent parentNode newNode atEnd parentPresent⟩
  · by_cases isNew : query = index
    · subst query
      rw [new_lookup tree index parent parentNode newNode atEnd parentPresent] at lookup
      cases lookup
      simp only [leaf,Array.toList_empty,List.not_mem_nil] at member
    · rw [other_lookup tree index parent query parentNode newNode atEnd parentPresent isParent isNew] at lookup
      obtain ⟨childNode,present⟩ := before query node lookup child member
      exact old_present tree index parent child parentNode newNode childNode atEnd parentPresent present

/-- A concrete child adds no root; all old parentless nodes remain covered by
the unchanged allocation root array. -/
theorem roots_cover (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (before : GeneralBorrowGraph.RootsCover tree) :
    GeneralBorrowGraph.RootsCover (attached tree index parent parentNode newNode) := by
  intro query node lookup parentless
  change query ∈ tree.roots.toList
  by_cases isParent : query = parent
  · subst query
    rw [parent_lookup tree index parent parentNode newNode atEnd parentPresent] at lookup
    cases lookup
    exact before parent parentNode parentPresent parentless
  · by_cases isNew : query = index
    · subst query
      rw [new_lookup tree index parent parentNode newNode atEnd parentPresent] at lookup
      cases lookup
      rw [childParent] at parentless
      cases parentless
    · rw [other_lookup tree index parent query parentNode newNode atEnd parentPresent isParent isNew] at lookup
      exact before query node lookup parentless

end DuplicatePrefix.GeneralBorrowFreshGraph
#print axioms DuplicatePrefix.GeneralBorrowFreshGraph.child_nodes
#print axioms DuplicatePrefix.GeneralBorrowFreshGraph.roots_cover
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshGraph." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fresh graph dependency {dependency}"
