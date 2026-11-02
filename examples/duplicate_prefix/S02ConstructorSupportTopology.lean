import duplicate_prefix.GeneralBorrowSharedCallbacksAttach
import duplicate_prefix.GeneralBorrowFreshMetadataChildReuseGraph

namespace DuplicatePrefix.S02ConstructorSupportTopology
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowFreshNode GeneralBorrowFreshGraph
open GeneralBorrowFreshMetadataChildReuseGraph
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- A foreign destination callback can contain the constructor parent. Its
support must then include the fresh child, independently of the destination's
selected root or concrete source. -/
def Extended (support : UniIndex → Prop) (index parent : UniIndex) (query : UniIndex) : Prop :=
  support query ∨ query = index ∧ support parent

/-- Physical attachment changes only the old parent's children field. -/
theorem old_fields (tree : BorrowTree) (index parent query : UniIndex)
    (parentNode newNode node : TreeNode) (vacant : tree.nodes.get index = none)
    (parentPresent : tree.nodeAt parent = some parentNode) (present : tree.nodeAt query = some node) :
    ∃ next, (attached tree index parent parentNode newNode).nodeAt query = some next ∧
      next = (if query = parent then {node with children := node.children.push index} else node) := by
  by_cases same : query = parent
  · subst query
    have equal := Option.some.inj (present.symm.trans parentPresent)
    subst node
    exact ⟨_,parent_lookup tree index parent parentNode newNode vacant parentPresent,by simp [updatedParent]⟩
  · have notNew : query ≠ index := by
      intro equal
      change tree.nodes.get query = some node at present
      rw [equal,vacant] at present
      cases present
    exact ⟨node,(other_lookup tree index parent query parentNode newNode vacant parentPresent same notNew).trans present,by simp [same]⟩

/-- Adding the fresh child precisely when its parent belongs to support
preserves all presence, child closure and physical-root coverage obligations.
The callback's root need not be the constructor parent's selected root. -/
theorem extend (tree : BorrowTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (leaf : newNode.children = #[]) (childParent : newNode.parent = some parent)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attached tree index parent parentNode newNode).nodes)
    (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop) (old : Authorization tree location protections root position maximum kind support) :
    Extended support index parent root ∧
    (∀ query, Extended support index parent query →
      ∃ node, (attached tree index parent parentNode newNode).nodeAt query = some node) ∧
    (∀ query node, Extended support index parent query →
      (attached tree index parent parentNode newNode).nodeAt query = some node →
      ∀ child ∈ node.children.toList, Extended support index parent child) ∧
    (∀ query, Extended support index parent query →
      Covers (attached tree index parent parentNode newNode).nodes root query) := by
  refine ⟨Or.inl old.rooted,?_,?_,?_⟩
  · intro query included
    rcases included with included | ⟨same,_⟩
    · obtain ⟨node,present⟩ := old.present query included
      exact old_present tree index parent query parentNode newNode node vacant parentPresent present
    · subst query
      exact ⟨newNode,new_lookup tree index parent parentNode newNode vacant parentPresent⟩
  · intro query node included present child member
    by_cases same : query = index
    · subst query
      rw [new_lookup tree index parent parentNode newNode vacant parentPresent] at present
      cases present
      simp only [leaf,Array.toList_empty,List.not_mem_nil] at member
    · have includedOld : support query := included.resolve_right (by intro h;exact same h.1)
      obtain ⟨oldNode,oldPresent⟩ := old.present query includedOld
      obtain ⟨next,nextPresent,nextFields⟩ := old_fields tree index parent query parentNode newNode oldNode vacant parentPresent oldPresent
      have equal := Option.some.inj (present.symm.trans nextPresent)
      subst node
      by_cases isParent : query = parent
      · simp only [isParent,ite_true] at nextFields
        rw [nextFields] at member
        have split : child ∈ oldNode.children.toList ∨ child = index := by
          simpa only [Array.toList_push,List.mem_append,List.mem_singleton] using member
        rcases split with previous | fresh
        · exact Or.inl (old.children query oldNode includedOld oldPresent child previous)
        · exact Or.inr ⟨fresh,by simpa only [isParent] using includedOld⟩
      · simp only [isParent,ite_false] at nextFields
        rw [nextFields] at member
        exact Or.inl (old.children query oldNode includedOld oldPresent child member)
  · intro query included
    rcases included with included | ⟨same,parentIncluded⟩
    · obtain ⟨node,present⟩ := old.present query included
      exact GeneralBorrowSharedAuthorizationGeometry.attached_covers tree depth index parent parentNode newNode
        vacant parentPresent nextDepth root query node present (old.covers query included)
    · subst query
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root parent parentNode
        parentPresent (old.covers parent parentIncluded)
      have extended := GeneralBorrowSharedAuthorizationGeometry.path_extension tree
        (attached tree index parent parentNode newNode)
        (GeneralBorrowSharedCallbacksAttach.parents tree index parent parentNode newNode vacant parentPresent)
        root parent path
      exact GeneralBorrowSharedAuthorizationGeometry.covers_of_path _ nextDepth root index
        (.step extended newNode (new_lookup tree index parent parentNode newNode vacant parentPresent) childParent)

end DuplicatePrefix.S02ConstructorSupportTopology

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02ConstructorSupportTopology.old_fields,
      ``DuplicatePrefix.S02ConstructorSupportTopology.extend] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
