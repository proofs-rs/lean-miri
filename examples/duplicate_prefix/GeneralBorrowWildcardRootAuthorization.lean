import duplicate_prefix.GeneralBorrowSharedAuthorizationGeometry
import duplicate_prefix.GeneralBorrowWildcardRootCache
import duplicate_prefix.GeneralBorrowFreshRootCutoff
namespace DuplicatePrefix.GeneralBorrowWildcardRootAuthorization
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowNodeUpdate
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
attribute [local irreducible] UniValMap.insert

/-- A fresh hidden isolated root preserves each old full callback authorization
with the SAME support/root-position/maximum and arbitrary old forest. Real
inside materialization supplies the slot-frame premise; no post-capability or
exposure profile is assumed. -/
theorem insert (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index : UniIndex) (newNode : TreeNode) (vacant : tree.nodes.get index = none)
    (hidden : newNode.isExposed = false) (parentless : newNode.parent = none)
    (size : tree.nodes.size ≤ (tree.nodes.insert index newNode).size)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree before protections root position maximum kind support) :
    Authorization {tree with nodes := tree.nodes.insert index newNode} after protections root position maximum kind support := by
  let nextTree := {tree with nodes := tree.nodes.insert index newNode}
  have different (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node) : query ≠ index := by
    intro same
    rw [same,vacant] at present
    contradiction
  have frame : ∀ query,support query → nextTree.nodes.get query = tree.nodes.get query := by
    intro query included
    obtain ⟨node,present⟩ := old.present query included
    exact GeneralBorrowFreshLocation.get_other _ index query newNode (different query node present)
  have parents : ∀ query node,tree.nodes.get query = some node →
      ∃ next,nextTree.nodes.get query = some next ∧ next.parent = node.parent := by
    intro query node present
    exact ⟨node,(GeneralBorrowFreshLocation.get_other _ index query newNode (different query node present)).trans present,rfl⟩
  have nextDepth := GeneralBorrowWildcardRootCache.rootDepth tree.nodes depth index newNode vacant parentless size
  have count (query : UniIndex) (removed : List UniIndex) :
      residualCount nextTree after protections kind removed query = residualCount tree before protections kind removed query := by
    apply GeneralBorrowSharedAuthorizationExtension.masked_count_extension tree nextTree before after protections depth size
    · intro query node present
      refine ⟨node,(GeneralBorrowFreshLocation.get_other _ index query newNode (different query node present)).trans present,rfl,rfl,?_⟩
      simp only [effective,slots query node present]
    · intro query node present exposed
      by_cases same : query = index
      · subst query
        change (tree.nodes.insert index newNode).get index = some node at present
        rw [GeneralBorrowFreshLocation.get_same] at present
        cases present
        rw [hidden] at exposed
        contradiction
      · exact ⟨node,(GeneralBorrowFreshLocation.get_other _ index query newNode same).symm.trans present⟩
  have removal (removed : List UniIndex) (legal : Removal nextTree after protections maximum kind removed) :
      Removal tree before protections maximum kind removed := by
    refine ⟨legal.distinct,?_⟩
    intro query member
    obtain ⟨node,present,allowed⟩ := legal.allowed query member
    by_cases same : query = index
    · subst query
      change (tree.nodes.insert index newNode).get index = some node at present
      rw [GeneralBorrowFreshLocation.get_same] at present
      cases present
      cases kind <;> simp [removable,hidden] at allowed
    · have original : tree.nodes.get query = some node := (GeneralBorrowFreshLocation.get_other _ index query newNode same).symm.trans present
      exact ⟨node,original,by simpa only [removable,effective,slots query node original] using allowed⟩
  refine ⟨old.rooted,?_,?_,?_,?_,?_,?_⟩
  · intro query included
    rw [frame query included]
    exact old.present query included
  · intro query node included present child member
    rw [frame query included] at present
    exact old.children query node included present child member
  · intro query included
    obtain ⟨node,present⟩ := old.present query included
    apply GeneralBorrowSharedAuthorizationGeometry.covers_of_path nextTree nextDepth root query
    exact GeneralBorrowSharedAuthorizationGeometry.path_extension tree nextTree parents root query
      (GeneralBorrowWildcardControlWitness.path_of_covers tree depth root query node present (old.covers query included))
  · intro query node included present
    rw [frame query included] at present
    simpa only [slots query node present] using old.possible query node included present
  · intro entry exit legalEntry legalExit subset query node included present retained
    rw [frame query included] at present
    have original := old.queries entry exit (removal entry legalEntry) (removal exit legalExit) subset query node included present retained
    change DuplicatePrefixCallbackVisitAuthorization.Authorized
      ((after.perms.get query).getD node.defaultLocationState) kind (protections.contains node.tag)
      (residualRelation nextTree after protections root query node maximum kind position entry)
      (residualRelation nextTree after protections root query node maximum kind position exit)
    simpa only [residualRelation,count,slots query node present] using original
  · intro primary
    obtain ⟨query,node,included,present,witness⟩ := old.witness primary
    refine ⟨query,node,included,?_,?_⟩
    · rw [frame query included];exact present
    · simpa only [Supports,slots query node present] using witness

/-- Initial wildcard callbacks become new-root concrete callbacks with the
actual fresh maximum. The old-root position/virtual bit is unchanged. -/
theorem fresh (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index : UniIndex) (newNode : TreeNode) (vacant : tree.nodes.get index = none)
    (hidden : newNode.isExposed = false) (parentless : newNode.parent = none)
    (size : tree.nodes.size ≤ (tree.nodes.insert index newNode).size)
    (maximum : BorTag) (aboveOld : GeneralBorrowFreshRootCutoff.Bound tree maximum) (sameTag : newNode.tag = maximum)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree before protections root position none kind support) :
    Authorization {tree with nodes := tree.nodes.insert index newNode} after protections root position (some maximum) kind support := by
  apply GeneralBorrowFreshRootCutoff.authorization _ after protections maximum
    (GeneralBorrowFreshRootCutoff.insert tree maximum aboveOld index newNode (by rw [sameTag];exact UInt64.le_refl _))
    root position kind support
  exact insert tree depth index newNode vacant hidden parentless size before after protections slots root position none kind support old
end DuplicatePrefix.GeneralBorrowWildcardRootAuthorization
