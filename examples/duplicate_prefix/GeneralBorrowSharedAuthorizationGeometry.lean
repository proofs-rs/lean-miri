import duplicate_prefix.GeneralBorrowSharedAuthorizationAttach

namespace DuplicatePrefix.GeneralBorrowSharedAuthorizationGeometry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowFreshNode GeneralBorrowNodeUpdate
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] UniValMap.insert

theorem path_trans {tree : BorrowTree} {root middle target : UniIndex}
    (first : Path tree root middle) (second : Path tree middle target) : Path tree root target := by
  induction second with
  | refl node present => exact first
  | step earlier node present edge ih => exact .step ih node present edge

/-- Parent-path domination implies complete ancestor-walk coverage, including
new hidden descendants and arbitrary source walk budgets justified by depth. -/
theorem covers_of_path (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (root query : UniIndex) (path : Path tree root query) : Covers tree.nodes root query := by
  intro row member ancestor
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  have tail := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query row.1 row.2 present _ ancestor
  exact (path_trans path tail).walk depth

theorem path_extension (before after : BorrowTree)
    (parents : ∀ index node,before.nodes.get index = some node →
      ∃ next,after.nodes.get index = some next ∧ next.parent = node.parent)
    (root query : UniIndex) (path : Path before root query) : Path after root query := by
  induction path with
  | refl node present =>
    obtain ⟨next,found,_⟩ := parents _ node present
    exact .refl _ next found
  | step earlier node present edge ih =>
    obtain ⟨next,found,parent⟩ := parents _ node present
    exact .step ih next found (parent.trans edge)

/-- Actual child attachment preserves every old domination claim. The new
child is covered automatically by path transitivity whenever it descends from
an old query; no post-extension Covers premise or exact fuel equality is used. -/
theorem attached_covers (tree : BorrowTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode newNode))
    (root query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node)
    (covered : Covers tree.nodes root query) :
    Covers (attachedNodes tree.nodes index parent parentNode newNode) root query := by
  apply covers_of_path {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} nextDepth root query
  apply path_extension tree _ _ root query
    (GeneralBorrowWildcardControlWitness.path_of_covers tree depth root query node present covered)
  intro old oldNode found
  have different : parent ≠ index := by intro same;rw [same,vacant] at parentPresent;cases parentPresent
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode different).trans parentPresent
  have neqIndex : old ≠ index := by intro same;rw [same,vacant] at found;cases found
  by_cases isParent : old = parent
  · subst old
    have equal := Option.some.inj (found.symm.trans parentPresent)
    subst oldNode
    exact ⟨{parentNode with children := parentNode.children.push index},
      insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ parentAfter,rfl⟩
  · refine ⟨oldNode,?_,rfl⟩
    change ((tree.nodes.insert index newNode).insert parent _).get old = _
    rw [GeneralBorrowFreshLocation.get_other _ parent old _ isParent,
      GeneralBorrowFreshLocation.get_other _ index old _ neqIndex,found]

/-- Full arbitrary-kind/cutoff authorization transport through the actual
attachment. Coverage is derived from physical parent paths; depth certificates
are the standard append/reuse graph data, not operation-success assumptions. -/
theorem authorization (tree : BorrowTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode newNode))
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree before protections root position maximum kind support)
    (notParent : ¬support parent) :
    Authorization {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
      after protections root position maximum kind support := by
  apply GeneralBorrowSharedAuthorizationAttach.authorization tree depth index parent parentNode newNode vacant
    parentPresent hidden size before after protections slots root position maximum kind support old notParent
  intro query included
  obtain ⟨node,present⟩ := old.present query included
  exact attached_covers tree depth index parent parentNode newNode vacant parentPresent nextDepth root query node present
    (old.covers query included)

/-- An opposite physical-root authorization cannot contain the constructor
parent. Separation follows from the raw selected-root path and reciprocal graph. -/
theorem other_not_parent (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags)
    (selected other parent : UniIndex) (parentNode : TreeNode)
    (present : tree.nodes.get parent = some parentNode)
    (selectedMember : selected ∈ tree.roots.toList) (otherMember : other ∈ tree.roots.toList)
    (different : selected ≠ other)
    (selectedPath : selected ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) parent)
    (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections other position maximum kind support) :
    ¬support parent := by
  intro included
  have own : parent ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) parent := by
    simp [GeneralBorrowExposureAncestorFold.walk]
  have otherPath := old.covers parent included (parent,parentNode)
    ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes parent parentNode).mpr present) own
  exact GeneralBorrowRootLocalCounterFrame.components_disjoint tree location protections formed selected other parent parentNode
    present selectedMember otherMember different selectedPath otherPath

end DuplicatePrefix.GeneralBorrowSharedAuthorizationGeometry
