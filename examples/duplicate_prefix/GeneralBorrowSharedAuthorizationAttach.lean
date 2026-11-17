import duplicate_prefix.GeneralBorrowSharedAuthorizationRemoval

namespace DuplicatePrefix.GeneralBorrowSharedAuthorizationAttach
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowFreshNode GeneralBorrowNodeUpdate
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] UniValMap.insert

/-- Full arbitrary-cutoff authorization on an unaffected support. The only
remaining geometric input is coverage in the extended parent graph; neither
operation success nor a post-operation permission capability is assumed. -/
theorem authorization (tree : BorrowTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree before protections root position maximum kind support)
    (notParent : ¬support parent)
    (covers : ∀ query,support query → Covers (attachedNodes tree.nodes index parent parentNode newNode) root query) :
    Authorization {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
      after protections root position maximum kind support := by
  let attached := attachedNodes tree.nodes index parent parentNode newNode
  have frame : ∀ query,support query → attached.get query = tree.nodes.get query := by
    intro query included
    obtain ⟨node,present⟩ := old.present query included
    have neqIndex : query ≠ index := by intro same;rw [same,vacant] at present;cases present
    have neqParent : query ≠ parent := by intro same;subst query;exact notParent included
    dsimp only [attached]
    unfold attachedNodes
    rw [GeneralBorrowFreshLocation.get_other _ parent query _ neqParent,
      GeneralBorrowFreshLocation.get_other _ index query _ neqIndex]
  have count (query : UniIndex) (removed : List UniIndex) :=
    GeneralBorrowSharedAuthorizationExtension.attached_masked_count tree depth index parent parentNode newNode
      vacant parentPresent hidden size before after protections slots removed query kind
  have removal (removed : List UniIndex) :=
    GeneralBorrowSharedAuthorizationRemoval.attached_removal tree index parent parentNode newNode
      vacant parentPresent hidden before after protections slots maximum kind removed
  refine ⟨old.rooted,?_,?_,covers,?_,?_,?_⟩
  · intro query included
    rw [frame query included]
    exact old.present query included
  · intro query node included present child member
    rw [frame query included] at present
    exact old.children query node included present child member
  · intro query node included present
    rw [frame query included] at present
    simpa only [slots query node present] using old.possible query node included present
  · intro entry exit legalEntry legalExit subset query node included present retained
    rw [frame query included] at present
    have initial := old.queries entry exit (removal entry legalEntry) (removal exit legalExit)
      subset query node included present retained
    change DuplicatePrefixCallbackVisitAuthorization.Authorized
      ((after.perms.get query).getD node.defaultLocationState) kind (protections.contains node.tag)
      (residualRelation _ after protections root query node maximum kind position entry)
      (residualRelation _ after protections root query node maximum kind position exit)
    simpa only [residualRelation,count,slots query node present] using initial
  · intro physical
    obtain ⟨query,node,included,present,witness⟩ := old.witness physical
    refine ⟨query,node,included,?_,?_⟩
    · rw [frame query included];exact present
    · simpa only [Supports,slots query node present] using witness

end DuplicatePrefix.GeneralBorrowSharedAuthorizationAttach
