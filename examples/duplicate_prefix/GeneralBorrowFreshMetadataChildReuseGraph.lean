import duplicate_prefix.GeneralBorrowFreshGraph
import duplicate_prefix.GeneralBorrowFreshReuseNode
namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildReuseGraph
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowFreshGraph (attached updatedParent)
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

theorem parent_lookup (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode) :
    (attached tree index parent parentNode newNode).nodeAt parent = some (updatedParent parentNode index) := by
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode
      (GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent)).trans parentPresent
  dsimp only [attached,BorrowTree.nodeAt,attachedNodes,updatedParent]
  exact insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode
    {parentNode with children := parentNode.children.push index} old

theorem new_lookup (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode) :
    (attached tree index parent parentNode newNode).nodeAt index = some newNode := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode different).trans parentPresent
  dsimp only [attached,BorrowTree.nodeAt,attachedNodes]
  exact (insert_existing_get_other (tree.nodes.insert index newNode) parent index parentNode
    {parentNode with children := parentNode.children.push index} old (Ne.symm different)).trans (GeneralBorrowFreshLocation.get_same tree.nodes index newNode)

theorem other_lookup (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (notParent : query ≠ parent) (notNew : query ≠ index) :
    (attached tree index parent parentNode newNode).nodeAt query = tree.nodeAt query := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent
  have old : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode different).trans parentPresent
  dsimp only [attached,BorrowTree.nodeAt,attachedNodes]
  exact (insert_existing_get_other (tree.nodes.insert index newNode) parent query parentNode
    {parentNode with children := parentNode.children.push index} old notParent).trans (GeneralBorrowFreshLocation.get_other tree.nodes index query newNode notNew)

/-- Any old stored node remains stored; only the parent's children field changes. -/
theorem old_present (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode oldNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (present : tree.nodeAt query = some oldNode) :
    ∃ node, (attached tree index parent parentNode newNode).nodeAt query = some node := by
  by_cases same : query = parent
  · subst query
    exact ⟨_,parent_lookup tree index parent parentNode newNode vacant parentPresent⟩
  · have notNew : query ≠ index := by
      intro equal
      change tree.nodes.get query = some oldNode at present
      rw [equal,vacant] at present
      cases present
    exact ⟨oldNode,(other_lookup tree index parent query parentNode newNode vacant parentPresent same notNew).trans present⟩

/-- Attaching a fresh leaf preserves the actual child-node lookup invariant
for every old node of an arbitrary caller topology. -/
theorem child_nodes (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (leaf : newNode.children = #[]) (before : GeneralBorrowGraph.ChildNodes tree) :
    GeneralBorrowGraph.ChildNodes (attached tree index parent parentNode newNode) := by
  intro query node lookup child member
  by_cases isParent : query = parent
  · subst query
    rw [parent_lookup tree index parent parentNode newNode vacant parentPresent] at lookup
    cases lookup
    have split : child ∈ parentNode.children.toList ∨ child = index := by
      simpa only [updatedParent,Array.toList_push,List.mem_append,List.mem_singleton] using member
    rcases split with old | fresh
    · obtain ⟨childNode,present⟩ := before parent parentNode parentPresent child old
      exact old_present tree index parent child parentNode newNode childNode vacant parentPresent present
    · subst child
      exact ⟨_,new_lookup tree index parent parentNode newNode vacant parentPresent⟩
  · by_cases isNew : query = index
    · subst query
      rw [new_lookup tree index parent parentNode newNode vacant parentPresent] at lookup
      cases lookup
      simp only [leaf,Array.toList_empty,List.not_mem_nil] at member
    · rw [other_lookup tree index parent query parentNode newNode vacant parentPresent isParent isNew] at lookup
      obtain ⟨childNode,present⟩ := before query node lookup child member
      exact old_present tree index parent child parentNode newNode childNode vacant parentPresent present

/-- A concrete child adds no root; all old parentless nodes remain covered by
the unchanged allocation root array. -/
theorem roots_cover (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (before : GeneralBorrowGraph.RootsCover tree) :
    GeneralBorrowGraph.RootsCover (attached tree index parent parentNode newNode) := by
  intro query node lookup parentless
  change query ∈ tree.roots.toList
  by_cases isParent : query = parent
  · subst query
    rw [parent_lookup tree index parent parentNode newNode vacant parentPresent] at lookup
    cases lookup
    exact before parent parentNode parentPresent parentless
  · by_cases isNew : query = index
    · subst query
      rw [new_lookup tree index parent parentNode newNode vacant parentPresent] at lookup
      cases lookup
      rw [childParent] at parentless
      cases parentless
    · rw [other_lookup tree index parent query parentNode newNode vacant parentPresent isParent isNew] at lookup
      exact before query node lookup parentless

end DuplicatePrefix.GeneralBorrowFreshMetadataChildReuseGraph
#print axioms DuplicatePrefix.GeneralBorrowFreshMetadataChildReuseGraph.child_nodes
#print axioms DuplicatePrefix.GeneralBorrowFreshMetadataChildReuseGraph.roots_cover
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildReuseGraph." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fresh graph dependency {dependency}"
