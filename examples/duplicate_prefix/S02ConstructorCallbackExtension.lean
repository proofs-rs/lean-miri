import duplicate_prefix.S02ConstructorSupportTopology
import duplicate_prefix.GeneralBorrowResidualPrimaryWitness

namespace DuplicatePrefix.S02ConstructorCallbackExtension
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowFreshNode GeneralBorrowFreshGraph
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCallbackAuthorization S02ConstructorSupportTopology
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] UniValMap.insert

theorem root_present {tree : BorrowTree} {root query : UniIndex} (path : Path tree root query) :
    ∃ node, tree.nodes.get root = some node := by
  induction path with
  | refl node found => exact ⟨node,found⟩
  | step _ _ _ _ ih => exact ih

/-- No exposed contribution has a vacant physical slot as an ancestor. -/
theorem vacant_count (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (location : LocationTree) (protections : ProtectedTags) (index : UniIndex)
    (vacant : tree.nodes.get index = none) (removed : List UniIndex) (kind : AccessKind) :
    residualCount tree location protections kind removed index = 0 := by
  unfold residualCount
  change List.length _ = List.length ([] : List (UniIndex × TreeNode))
  apply congrArg List.length
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  obtain ⟨filtered,_⟩ := List.mem_filter.mp member
  obtain ⟨entry,contribution⟩ := List.mem_filter.mp filtered
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp entry
  simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at contribution
  have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth index row.1 row.2 present _ contribution.2
  have rootPresent := root_present path
  obtain ⟨node,found⟩ := rootPresent
  rw [vacant] at found
  cases found

/-- The primary callback's cutoff-eligible witness survives every legal mask;
other physical roots retain their virtual contribution. -/
theorem total_positive (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (location : LocationTree) (protections : ProtectedTags) (root : UniIndex)
    (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum kind support)
    (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed) :
    0 < residualCount tree location protections kind removed root + if position != 0 then 1 else 0 := by
  by_cases primary : position = 0
  · obtain ⟨witness,node,included,present,eligible⟩ := old.witness primary
    have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present
      (old.covers witness included)
    have positive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum kind
      removed legal root witness node present eligible path
    simpa only [primary,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] using positive
  · have nonzero : (position != 0) = true := by simp [primary]
    simp only [nonzero,ite_true]
    omega

/-- A fresh hidden child's zero local count is classified foreign for every
legal residual mask, even when the callback root contains its new parent. -/
theorem vacant_foreign (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (location : LocationTree) (protections : ProtectedTags) (root index : UniIndex)
    (vacant : tree.nodes.get index = none) (position : Nat) (maximum : Option BorTag)
    (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum kind support)
    (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed)
    (node : TreeNode) :
    classify (residualCount tree location protections kind removed root)
      (residualCount tree location protections kind removed index) (position != 0)
      (aboveMaximum node maximum) = some .ForeignAccess := by
  have positive := total_positive tree depth location protections root position maximum kind support old removed legal
  rw [vacant_count tree depth location protections index vacant removed kind]
  have nz : (residualCount tree location protections kind removed root + (if position != 0 then 1 else 0) == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have zero : residualCount tree location protections kind removed root + (if position != 0 then 1 else 0) = 0 := by
      exact Nat.eq_of_beq_eq_true equal
    omega
  simp only [classify,nz,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true]
  cases aboveMaximum node maximum <;> rfl

/-- A lazy mutable fresh child accepts an exact foreign callback for either
kind, including its registered protector. -/
theorem fresh_query (kind : AccessKind) (held : Bool) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized
      ⟨.ReservedFrz false,false,.None⟩ kind held (some .ForeignAccess) (some .ForeignAccess) := by
  cases kind <;> cases held <;>
    simp [DuplicatePrefixCallbackVisitAuthorization.Authorized,DuplicatePrefixCallbackVisitAuthorization.entrySkip,
      skip,DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique,
      IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,AccessRelatedness.isForeign,
      Permission.isDisabled,Permission.isFrozen]

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
    (freshState : (after.perms.get index).getD newNode.defaultLocationState = ⟨.ReservedFrz false,false,.None⟩)
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
      rfl
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
      simpa only [residualRelation,count,entryForeign,exitForeign,freshState] using fresh_query kind (protections.contains newNode.tag)
  · intro physical
    obtain ⟨query,node,included,present,eligible⟩ := old.witness physical
    obtain ⟨next,found⟩ := topology.2.1 query (Or.inl included)
    have fields := scalar query node next present found
    refine ⟨query,next,Or.inl included,found,?_⟩
    simpa only [Supports,effective,fields.1,fields.2.1,fields.2.2] using eligible

end DuplicatePrefix.S02ConstructorCallbackExtension

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02ConstructorCallbackExtension.vacant_count,
      ``DuplicatePrefix.S02ConstructorCallbackExtension.total_positive,
      ``DuplicatePrefix.S02ConstructorCallbackExtension.vacant_foreign,
      ``DuplicatePrefix.S02ConstructorCallbackExtension.fresh_query,
      ``DuplicatePrefix.S02ConstructorCallbackExtension.authorization] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
