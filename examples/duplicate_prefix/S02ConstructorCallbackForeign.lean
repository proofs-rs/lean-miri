import duplicate_prefix.S02ConstructorCallbackExtension

namespace DuplicatePrefix.S02ConstructorCallbackForeign
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowFreshNode GeneralBorrowFreshGraph
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCallbackAuthorization S02ConstructorSupportTopology S02ConstructorCallbackExtension
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] UniValMap.insert

/-- Outside the constructor window, attachment extends full callback support
through the lazy mutable fresh child. The callback root and cutoff are arbitrary;
no equality with the constructor's source or selected root is required. -/
theorem authorization (tree : BorrowTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (hidden : newNode.isExposed = false) (leaf : newNode.children = #[])
    (childParent : newNode.parent = some parent)
    (size : tree.nodes.size ≤ (attached tree index parent parentNode newNode).nodes.size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attached tree index parent parentNode newNode).nodes)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (state : LocationState)
    (freshState : (after.perms.get index).getD newNode.defaultLocationState = state)
    (freshAuthorized : ∀ kind held,DuplicatePrefixCallbackVisitAuthorization.Authorized state kind held
      (some .ForeignAccess) (some .ForeignAccess))
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop) (old : Authorization tree before protections root position maximum kind support) :
    Authorization (attached tree index parent parentNode newNode) after protections root position maximum kind
      (Extended support index parent) := by
  have topology := extend tree depth index parent parentNode newNode vacant parentPresent leaf childParent
    nextDepth before protections root position maximum kind support old
  have count (removed : List UniIndex) (query : UniIndex) :
      residualCount (attached tree index parent parentNode newNode) after protections kind removed query =
        residualCount tree before protections kind removed query :=
    GeneralBorrowSharedAuthorizationExtension.attached_masked_count tree depth index parent parentNode newNode
      vacant parentPresent hidden size before after protections slots removed query kind
  have removal (removed : List UniIndex) :=
    GeneralBorrowSharedAuthorizationRemoval.attached_removal tree index parent parentNode newNode vacant parentPresent
      hidden before after protections slots maximum kind removed
  have scalar (query : UniIndex) (node next : TreeNode)
      (present : tree.nodeAt query = some node)
      (nextPresent : (attached tree index parent parentNode newNode).nodeAt query = some next) :
      next.tag = node.tag ∧ next.isExposed = node.isExposed ∧
      (after.perms.get query).getD next.defaultLocationState = (before.perms.get query).getD node.defaultLocationState := by
    obtain ⟨known,found,fields⟩ := old_fields tree index parent query parentNode newNode node vacant parentPresent present
    have equal := Option.some.inj (nextPresent.symm.trans found)
    subst next
    rw [fields]
    split <;> refine ⟨rfl,rfl,?_⟩ <;> simp only [TreeNode.defaultLocationState,slots query node present]
  refine ⟨topology.1,topology.2.1,topology.2.2.1,topology.2.2.2,?_,?_,?_⟩
  · intro query node included present
    rcases included with included | ⟨same,_⟩
    · obtain ⟨previous,found⟩ := old.present query included
      rw [(scalar query previous node found present).2.2]
      exact old.possible query previous included found
    · subst query
      change (attached tree index parent parentNode newNode).nodeAt index = some node at present
      rw [GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index parent parentNode newNode vacant parentPresent] at present
      cases present
      rw [freshState]
      exact (freshAuthorized kind (protections.contains newNode.tag)).1
  · intro entry exit legalEntry legalExit subset query node included present retained
    have entryOld := removal entry legalEntry
    have exitOld := removal exit legalExit
    rcases included with included | ⟨same,_⟩
    · obtain ⟨previous,found⟩ := old.present query included
      have fields := scalar query previous node found present
      have authorized := old.queries entry exit entryOld exitOld subset query previous included found retained
      change DuplicatePrefixCallbackVisitAuthorization.Authorized
        ((after.perms.get query).getD node.defaultLocationState) kind (protections.contains node.tag)
        (residualRelation _ after protections root query node maximum kind position entry)
        (residualRelation _ after protections root query node maximum kind position exit)
      simpa only [residualRelation,count,fields.1,fields.2.2,aboveMaximum] using authorized
    · subst query
      change (attached tree index parent parentNode newNode).nodeAt index = some node at present
      rw [GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index parent parentNode newNode vacant parentPresent] at present
      cases present
      have entryForeign := vacant_foreign tree depth before protections root index vacant position maximum kind support old entry entryOld newNode
      have exitForeign := vacant_foreign tree depth before protections root index vacant position maximum kind support old exit exitOld newNode
      change DuplicatePrefixCallbackVisitAuthorization.Authorized
        ((after.perms.get index).getD newNode.defaultLocationState) kind (protections.contains newNode.tag)
        (residualRelation _ after protections root index newNode maximum kind position entry)
        (residualRelation _ after protections root index newNode maximum kind position exit)
      simpa only [residualRelation,count,entryForeign,exitForeign,freshState] using freshAuthorized kind (protections.contains newNode.tag)
  · intro physical
    obtain ⟨query,node,included,present,eligible⟩ := old.witness physical
    obtain ⟨next,found⟩ := topology.2.1 query (Or.inl included)
    have fields := scalar query node next present found
    refine ⟨query,next,Or.inl included,found,?_⟩
    simpa only [Supports,effective,fields.1,fields.2.1,fields.2.2] using eligible

end DuplicatePrefix.S02ConstructorCallbackForeign

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02ConstructorCallbackForeign.authorization) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
