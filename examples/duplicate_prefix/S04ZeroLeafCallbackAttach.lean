import duplicate_prefix.S04ZeroLeafCallbackData
import duplicate_prefix.GeneralBorrowSharedCallbacksAttach

namespace DuplicatePrefix.S04ZeroLeafCallbackAttach
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralBorrowNodeUpdate GeneralBorrowSharedAuthorizationGeometry
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- A callback component grows by the fresh leaf exactly when it contains the
constructor parent. Existing support cannot contain the initially vacant slot. -/
def extended (support : UniIndex → Prop) (parent child : UniIndex) (query : UniIndex) : Prop :=
  support query ∨ query = child ∧ support parent

def liftNode (parent child query : UniIndex) (node : TreeNode) : TreeNode :=
  if query = parent then {node with children := node.children.push child} else node

theorem old_lookup (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node) :
    (attachedNodes tree.nodes index parent parentNode newNode).get query = some (liftNode parent index query node) := by
  have different : parent ≠ index := by intro same;rw [same,vacant] at parentPresent;cases parentPresent
  have queryDifferent : query ≠ index := by intro same;rw [same,vacant] at present;cases present
  by_cases isParent : query = parent
  · subst query
    have same := Option.some.inj (present.symm.trans parentPresent)
    subst node
    simp only [liftNode,ite_true]
    exact insert_existing_get_same _ parent parentNode _
      ((GeneralBorrowFreshLocation.get_other _ index parent _ different).trans parentPresent)
  · simp only [liftNode,isParent,ite_false]
    unfold attachedNodes
    rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
      GeneralBorrowFreshLocation.get_other _ index query _ queryDifferent,present]

theorem fresh_lookup (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode) :
    (attachedNodes tree.nodes index parent parentNode newNode).get index = some newNode := by
  have different : parent ≠ index := by intro same;rw [same,vacant] at parentPresent;cases parentPresent
  unfold attachedNodes
  rw [GeneralBorrowFreshLocation.get_other _ parent index _ (Ne.symm different),GeneralBorrowFreshLocation.get_same]

/-- An untouched protected Default leaf can be added to ANY old callback
component, including the component containing the constructor parent. Unlike
other-component-only transport, no support/parent separation is assumed. -/
theorem authorization (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode (GeneralBorrowFreshChild.child tag parent)).size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode (GeneralBorrowFreshChild.child tag parent)))
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop) (old : Authorization tree location protections root position maximum kind support) :
    Authorization {tree with nodes := attachedNodes tree.nodes index parent parentNode (GeneralBorrowFreshChild.child tag parent)}
      location protections root position maximum kind (extended support parent index) := by
  let newNode := GeneralBorrowFreshChild.child tag parent
  let after := {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
  change Authorization after location protections root position maximum kind (extended support parent index)
  have oldDifferent (query : UniIndex) (inside : support query) : query ≠ index := by
    obtain ⟨node,present⟩ := old.present query inside
    intro same;rw [same,vacant] at present;cases present
  have metadata (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node) :=
    old_lookup tree index parent parentNode newNode vacant parentPresent query node present
  have fresh : after.nodes.get index = some newNode := fresh_lookup tree index parent parentNode newNode vacant parentPresent
  have count (removed : List UniIndex) (query : UniIndex) :
      residualCount after location protections kind removed query = residualCount tree location protections kind removed query :=
    GeneralBorrowSharedAuthorizationExtension.attached_masked_count tree depth index parent parentNode newNode
      vacant parentPresent rfl size location location protections (by intro query node present;rfl) removed query kind
  have removal (removed : List UniIndex) (legal : Removal after location protections maximum kind removed) :=
    GeneralBorrowSharedAuthorizationRemoval.attached_removal tree index parent parentNode newNode vacant parentPresent rfl
      location location protections (by intro query node present;rfl) maximum kind removed legal
  have newState : (location.perms.get index).getD newNode.defaultLocationState = ⟨.ReservedFrz false,false,.None⟩ := by
    rw [clean];rfl
  have newRelation (removed : List UniIndex) (legal : Removal after location protections maximum kind removed) :
      residualRelation after location protections root index newNode maximum kind position removed = some .ForeignAccess := by
    have total := S04ZeroLeafCallbackData.total_positive tree depth location protections root position maximum kind support old removed (removal removed legal)
    have localZero := S04ZeroLeafCallbackData.vacant_count tree depth location protections index vacant kind removed
    simp only [residualRelation,count,localZero]
    exact S04ZeroLeafCallbackData.zero_foreign _ _ _ total
  refine ⟨Or.inl old.rooted,?_,?_,?_,?_,?_,?_⟩
  · intro query included
    rcases included with inside | ⟨same,parentInside⟩
    · obtain ⟨node,present⟩ := old.present query inside
      exact ⟨liftNode parent index query node,metadata query node present⟩
    · subst query;exact ⟨newNode,fresh⟩
  · intro query node included present child member
    by_cases isNew : query = index
    · subst query
      have same := Option.some.inj (fresh.symm.trans present)
      subst node
      simp [newNode,GeneralBorrowFreshChild.child] at member
    · have inside : support query := included.resolve_right (by intro both;exact isNew both.1)
      obtain ⟨oldNode,oldPresent⟩ := old.present query inside
      have same := Option.some.inj ((metadata query oldNode oldPresent).symm.trans present)
      subst node
      by_cases isParent : query = parent
      · subst query
        simp only [liftNode,ite_true,Array.toList_push,List.mem_append,List.mem_singleton] at member
        rcases member with previous | equal
        · exact .inl (old.children parent oldNode inside oldPresent child previous)
        · exact .inr ⟨equal,inside⟩
      · simp only [liftNode,isParent,ite_false] at member
        exact .inl (old.children query oldNode inside oldPresent child member)
  · intro query included
    rcases included with inside | ⟨same,parentInside⟩
    · obtain ⟨node,present⟩ := old.present query inside
      exact attached_covers tree depth index parent parentNode newNode vacant parentPresent nextDepth root query node present (old.covers query inside)
    · subst query
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root parent parentNode parentPresent (old.covers parent parentInside)
      have extendedPath := path_extension tree after
        (GeneralBorrowSharedCallbacksAttach.parents tree index parent parentNode newNode vacant parentPresent) root parent path
      exact covers_of_path after nextDepth root index (.step extendedPath newNode fresh rfl)
  · intro query node included present
    by_cases isNew : query = index
    · subst query
      have same := Option.some.inj (fresh.symm.trans present)
      subst node
      rw [newState];rfl
    · have inside : support query := included.resolve_right (by intro both;exact isNew both.1)
      obtain ⟨oldNode,oldPresent⟩ := old.present query inside
      have same := Option.some.inj ((metadata query oldNode oldPresent).symm.trans present)
      subst node
      have possible := old.possible query oldNode inside oldPresent
      by_cases isParent : query = parent <;> simpa only [liftNode,isParent,ite_true,ite_false,TreeNode.defaultLocationState] using possible
  · intro entry exit legalEntry legalExit subset query node included present retained
    by_cases isNew : query = index
    · subst query
      have same := Option.some.inj (fresh.symm.trans present)
      subst node
      rw [newRelation entry legalEntry,newRelation exit legalExit,newState]
      exact S04ZeroLeafCallbackData.foreign_authorized kind _
    · have inside : support query := included.resolve_right (by intro both;exact isNew both.1)
      obtain ⟨oldNode,oldPresent⟩ := old.present query inside
      have same := Option.some.inj ((metadata query oldNode oldPresent).symm.trans present)
      subst node
      have authorized := old.queries entry exit (removal entry legalEntry) (removal exit legalExit) subset query oldNode inside oldPresent retained
      by_cases isParent : query = parent <;>
        simpa only [residualRelation,count,aboveMaximum,liftNode,isParent,ite_true,ite_false,TreeNode.defaultLocationState] using authorized
  · intro primary
    obtain ⟨query,node,inside,present,eligible⟩ := old.witness primary
    refine ⟨query,liftNode parent index query node,.inl inside,metadata query node present,?_⟩
    by_cases isParent : query = parent <;>
      simpa only [Supports,effective,aboveMaximum,liftNode,isParent,ite_true,ite_false,TreeNode.defaultLocationState] using eligible

end DuplicatePrefix.S04ZeroLeafCallbackAttach
