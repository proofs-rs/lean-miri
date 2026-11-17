import duplicate_prefix.S05CompletedAncestryWriteAccess
import duplicate_prefix.S05CompletedAncestryReadQueries
import duplicate_prefix.S05RawForeignAuthorizationBridge
import duplicate_prefix.CompletedBorrowAncestry
import duplicate_prefix.S04ZeroRootObserverCallbacks
import duplicate_prefix.DuplicatePrefixResidualWriteRepaired
import duplicate_prefix.GeneralBorrowWildcardRootAuthorization

/-! Repaired callback clauses transported through ONE actual hidden dormant
zero root. No completion edge or exposed source origin is invented for it. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowNodeUpdate GeneralBorrowFreshNode
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

private theorem inserted_repaired (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index : UniIndex) (newNode : TreeNode) (vacant : tree.nodes.get index = none)
    (hidden : newNode.isExposed = false) (parentless : newNode.parent = none)
    (size : tree.nodes.size ≤ (tree.nodes.insert index newNode).size)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization tree before protections root position maximum kind support) :
    DuplicatePrefixResidualWriteRepaired.Authorization {tree with nodes := tree.nodes.insert index newNode} after protections root position maximum kind support := by
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
    change DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
      ((after.perms.get query).getD node.defaultLocationState) kind (protections.contains node.tag)
      (residualRelation nextTree after protections root query node maximum kind position entry)
      (residualRelation nextTree after protections root query node maximum kind position exit)
    simpa only [residualRelation,count,slots query node present] using original
  · intro primary
    obtain ⟨query,node,included,present,witness⟩ := old.witness primary
    refine ⟨query,node,included,?_,?_⟩
    · rw [frame query included];exact present
    · simpa only [Supports,slots query node present] using witness

/-- All old-root repaired callback queries keep their actual root position,
cutoff and masked counts across the exact zero wildcard constructor. -/
theorem old_write (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (initial : DuplicatePrefixResidualWriteRepaired.Authorization tree location protections root position maximum .Write support) :
    DuplicatePrefixResidualWriteRepaired.Authorization (slot.after tag) location protections root position maximum .Write support := by
  have growth : tree.nodes.size ≤ (tree.nodes.insert slot.index
      (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).size := by
    change tree.nodes.size ≤ (slot.after tag).nodes.size
    rw [slot.size tag]
    omega
  have got := inserted_repaired tree depth slot.index
    (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) slot.vacant rfl rfl growth
    location location protections (by intros;rfl) root position maximum .Write support initial
  refine ⟨got.rooted,got.present,got.children,got.covers,got.possible,?_,got.witness⟩
  intro entry exit legalEntry legalExit subset query node included found retained
  exact got.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩
    ⟨legalExit.distinct,legalExit.allowed⟩ subset query node included found retained

/-- The exact added root remains a Foreign callback even after real Read or
Write materialization. Its current scalar data, rather than an unchanged-state
assumption, discharge the transition table. -/
theorem new_foreign (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (nonempty : 0 < tree.roots.size) (maximum : Option BorTag) (kind : AccessKind)
    (foreign : OrdinaryBorrowAuthority.ForeignWrite
      ((location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
      (protections.contains tag))
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent
      ((location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
      (protections.contains tag)) :
    DuplicatePrefixResidualWriteRepaired.Authorization (slot.after tag) location protections slot.index tree.roots.size maximum kind
      (fun query => query = slot.index) := by
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  have present : (slot.after tag).nodes.get slot.index = some node := GeneralBorrowFreshLocation.get_same _ _ _
  have relation (removed : List UniIndex) :
      residualRelation (slot.after tag) location protections slot.index slot.index node maximum kind tree.roots.size removed =
        some .ForeignAccess := by
    unfold residualRelation
    rw [S04ZeroRootObserverCallbacks.count tree slot tag depth location protections kind removed slot.index,
      S04ZeroLeafCallbackData.vacant_count tree depth location protections slot.index slot.vacant kind removed]
    apply S04ZeroLeafCallbackData.zero_foreign
    have virtual : (tree.roots.size != 0) = true := by simp [Nat.ne_of_gt nonempty]
    simp only [virtual,ite_true]
    omega
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · intro query same;subst query;exact ⟨node,present⟩
  · intro query value same found child member
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    cases member
  · intro query same;subst query;intro row member walked;exact walked
  · intro query value same found
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    exact foreign.1
  · intro entry exit legalEntry legalExit subset query value same found retained
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    rw [relation,relation]
    cases kind with
    | Write => exact S05RawForeignAuthorizationBridge.foreign_write_authorized _ _ _ consistent foreign
    | Read =>
      apply DuplicatePrefixCallbackVisitAuthorizationRepaired.old_inclusion
      apply (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ _ _ _).mpr
      exact ⟨foreign.1,Or.inr (S05CompletedAncestryReadQueries.foreign_read _ _ foreign)⟩
  · intro zero;omega


private theorem attached_repaired (tree : BorrowTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualWriteRepaired.Authorization tree before protections root position maximum kind support)
    (notParent : ¬support parent)
    (covers : ∀ query,support query → Covers (attachedNodes tree.nodes index parent parentNode newNode) root query) :
    DuplicatePrefixResidualWriteRepaired.Authorization {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
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
    change DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
      ((after.perms.get query).getD node.defaultLocationState) kind (protections.contains node.tag)
      (residualRelation _ after protections root query node maximum kind position entry)
      (residualRelation _ after protections root query node maximum kind position exit)
    simpa only [residualRelation,count,slots query node present] using initial
  · intro physical
    obtain ⟨query,node,included,present,witness⟩ := old.witness physical
    refine ⟨query,node,included,?_,?_⟩
    · rw [frame query included];exact present
    · simpa only [Supports,slots query node present] using witness

theorem write_of_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (support : UniIndex → Prop)
    (auth : DuplicatePrefixResidualWriteRepaired.Authorization tree location protections root position maximum .Write support)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) :
    let result := tree.performWildcardAccessAt location root maximum .Write protections (position != 0)
    result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      ∀ query, ¬support query → result.location.perms.get query = location.perms.get query := by
  obtain ⟨forest⟩ := formed.forest location protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree location protections forest depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree location protections forest
  let area : GeneralBorrowWildcardControlStack.Support tree root :=
    ⟨support,auth.rooted,auth.present,auth.children⟩
  have plans : Nonempty (DuplicatePrefixResidualWriteWitnessPlan.Plan tree location protections root position maximum) := by
    by_cases zero : position = 0
    · obtain ⟨witness,node,included,present,eligible⟩ := auth.witness zero
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present (auth.covers witness included)
      subst position
      exact ⟨DuplicatePrefixResidualVisibleWritePlan.ordered tree location protections root maximum depth graph short witness node present
        (GeneralBorrowPrimaryWitnessVisibility.of_order tree order location protections maximum .Write witness node present eligible) eligible path⟩
    · exact ⟨DuplicatePrefixResidualWriteWitnessPlan.virtual tree location protections root position maximum zero⟩
  obtain ⟨plan⟩ := plans
  obtain ⟨done,_,_,_,afterCoherent,outside,afterProfile,afterPossible,_⟩ :=
    DuplicatePrefixResidualWriteRepaired.access tree location protections root position maximum weights
      (GeneralBorrowWildcardForestWeights.bounded tree location protections forest root) area plan auth depth forest coherent short profile possible
  exact ⟨done,afterCoherent,afterProfile,afterPossible,outside⟩

/-- The actual production Write callback on an OLD root after the exact zero
extension. Repaired pair queries and the real DFS supply completion and frames. -/
theorem old_write_access (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (initial : DuplicatePrefixResidualWriteRepaired.Authorization tree location protections root position maximum .Write support)
    (formed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder (slot.after tag))
    (coherent : LocationCoherent (slot.after tag) location protections) (short : (slot.after tag).nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) location) :
    let result := (slot.after tag).performWildcardAccessAt location root maximum .Write protections (position != 0)
    result.status = .Completed ∧ LocationCoherent (slot.after tag) result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) result.location ∧
      ∀ query, ¬support query → result.location.perms.get query = location.perms.get query := by
  obtain ⟨nextDepth⟩ := formed.depth
  exact write_of_authorization (slot.after tag) location protections formed order nextDepth root position maximum support
    (old_write tree slot tag depth location protections root position maximum support initial) coherent short profile possible

/-- The actual production Write on the new dormant root. It may materialize
or disable that node; no no-op or future state is supplied as a premise. -/
theorem new_write_access (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (nonempty : 0 < tree.roots.size) (maximum : Option BorTag)
    (foreign : OrdinaryBorrowAuthority.ForeignWrite
      ((location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
      (protections.contains tag))
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent
      ((location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
      (protections.contains tag))
    (formed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder (slot.after tag))
    (coherent : LocationCoherent (slot.after tag) location protections) (short : (slot.after tag).nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) location) :
    let result := (slot.after tag).performWildcardAccessAt location slot.index maximum .Write protections (tree.roots.size != 0)
    result.status = .Completed ∧ LocationCoherent (slot.after tag) result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) result.location ∧
      ∀ query, query ≠ slot.index → result.location.perms.get query = location.perms.get query := by
  obtain ⟨nextDepth⟩ := formed.depth
  exact write_of_authorization (slot.after tag) location protections formed order nextDepth slot.index tree.roots.size maximum
    (fun query => query = slot.index) (new_foreign tree slot tag depth location protections nonempty maximum .Write foreign consistent)
    coherent short profile possible

theorem new_read (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (nonempty : 0 < tree.roots.size) (maximum : Option BorTag)
    (foreign : OrdinaryBorrowAuthority.ForeignWrite
      ((location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
      (protections.contains tag))
 :
    Authorization (slot.after tag) location protections slot.index tree.roots.size maximum .Read
      (fun query => query = slot.index) := by
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  have present : (slot.after tag).nodes.get slot.index = some node := GeneralBorrowFreshLocation.get_same _ _ _
  have relation (removed : List UniIndex) :
      residualRelation (slot.after tag) location protections slot.index slot.index node maximum .Read tree.roots.size removed =
        some .ForeignAccess := by
    unfold residualRelation
    rw [S04ZeroRootObserverCallbacks.count tree slot tag depth location protections .Read removed slot.index,
      S04ZeroLeafCallbackData.vacant_count tree depth location protections slot.index slot.vacant .Read removed]
    apply S04ZeroLeafCallbackData.zero_foreign
    have virtual : (tree.roots.size != 0) = true := by simp [Nat.ne_of_gt nonempty]
    simp only [virtual,ite_true]
    omega
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · intro query same;subst query;exact ⟨node,present⟩
  · intro query value same found child member
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    cases member
  · intro query same;subst query;intro row member walked;exact walked
  · intro query value same found
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    exact foreign.1
  · intro entry exit legalEntry legalExit subset query value same found retained
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    rw [relation,relation]
    apply (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ _ _ _).mpr
    exact ⟨foreign.1,Or.inr (S05CompletedAncestryReadQueries.foreign_read _ _ foreign)⟩
  · intro zero;omega


/-- Actual Read DFS from the original Read authorization, retaining the
pointwise transfer and real scalar effects needed by Bool authority. -/
theorem read_of_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (support : UniIndex → Prop)
    (auth : Authorization tree location protections root position maximum .Read support)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) :
    let result := tree.performWildcardAccessAt location root maximum .Read protections (position != 0)
    result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame location result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree location result.location protections ∧
      (∀ query, ¬support query → result.location.perms.get query = location.perms.get query) ∧
      GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections location result.location ∧
      GeneralBorrowSnapshotReadTransfer.Global tree location result.location protections root position maximum support := by
  let area : GeneralBorrowWildcardControlStack.Support tree root := ⟨support,auth.rooted,auth.present,auth.children⟩
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections root position maximum .Read support auth coherent short
  obtain ⟨forest⟩ := formed.forest location protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree location protections forest depth
  have plans : Nonempty (GeneralBorrowSnapshotReadDFSPlan.WitnessPlan tree location protections root position maximum) := by
    by_cases zero : position = 0
    · subst position
      exact GeneralBorrowSnapshotOrderedPrimaryReadPlan.of_authorization tree location protections root maximum support order depth graph coherent short auth
    · exact ⟨GeneralBorrowSnapshotVirtualReadAccess.plan tree location protections root position maximum zero⟩
  obtain ⟨plan⟩ := plans
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree location protections forest
  have bound := GeneralBorrowWildcardForestWeights.bounded tree location protections forest root
  obtain ⟨done,frame,_,pointwise,afterCoherent,outside,runtime,_,transfer,effects⟩ :=
    S05SemanticReadDFS.access true false tree location protections root position maximum
      weights bound area snapshot depth coherent plan (fun _ => ⟨profile,possible⟩) (by simp)
  exact ⟨done,frame,afterCoherent,(runtime rfl).1,(runtime rfl).2,effects,outside,pointwise,transfer⟩


/-- The real dormant-root Read preserves its ForeignWrite authority, including
materialized states. This is extracted from DFS transfer and scalar effects. -/
theorem new_read_access (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (nonempty : 0 < tree.roots.size) (maximum : Option BorTag)
    (foreign : OrdinaryBorrowAuthority.ForeignWrite
      ((location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
      (protections.contains tag))
    (formed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder (slot.after tag))
    (coherent : LocationCoherent (slot.after tag) location protections) (short : (slot.after tag).nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) location) :
    let result := (slot.after tag).performWildcardAccessAt location slot.index maximum .Read protections (tree.roots.size != 0)
    result.status = .Completed ∧ LocationCoherent (slot.after tag) result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) result.location ∧
      (∀ query, query ≠ slot.index → result.location.perms.get query = location.perms.get query) ∧
      OrdinaryBorrowAuthority.ForeignWrite
        ((result.location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
        (protections.contains tag) := by
  obtain ⟨nextDepth⟩ := formed.depth
  obtain ⟨done,_,cache,sifa,gp,effects,outside,pointwise,transfer⟩ := read_of_authorization
    (slot.after tag) location protections formed order nextDepth slot.index tree.roots.size maximum
    (fun query => query = slot.index) (new_read tree slot tag depth location protections nonempty maximum foreign)
    coherent short profile possible
  refine ⟨done,cache,sifa,gp,outside,?_⟩
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  have present : (slot.after tag).nodes.get slot.index = some node := GeneralBorrowFreshLocation.get_same _ _ _
  have classified : residualRelation (slot.after tag) location protections slot.index slot.index node maximum .Read tree.roots.size [] = some .ForeignAccess := by
    unfold residualRelation
    rw [S04ZeroRootObserverCallbacks.count tree slot tag depth location protections .Read [] slot.index,
      S04ZeroLeafCallbackData.vacant_count tree depth location protections slot.index slot.vacant .Read []]
    apply S04ZeroLeafCallbackData.zero_foreign
    have virtual : (tree.roots.size != 0) = true := by simp [Nat.ne_of_gt nonempty]
    simp only [virtual,ite_true]
    omega
  rw [DuplicatePrefixResidualSupportAuthorization.initial_relation (slot.after tag) location protections slot.index slot.index node maximum .Read tree.roots.size coherent short] at classified
  apply S05ReadRawAuthorityEndpoint.foreign_right _ _ _
    (relation location slot.index slot.index node maximum .Read tree.roots.size) foreign
  · simp [classified]
  · exact transfer slot.index node rfl present
  · exact effects slot.index node present
  · exact pointwise slot.index node present
  · exact profile.present slot.index node present
  · exact gp slot.index node present


/-- Original completed ancestry supplies OLD-root Read queries after the exact
zero extension. Mutable rights are extracted from actual Read effects. -/
theorem old_read_access (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : CandidateStableCallOwnership.Completion) (location : LocationTree) (protections : ProtectedTags)
    (complete : CandidateStableCallOwnership.Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (oldOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (position selectedPosition : Nat) (root selectedRoot source : UniIndex) (selectedNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode) (different : root ≠ selectedRoot)
    (selectedPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selectedRoot source)
    (localRights : ∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
      CandidateStableCallOwnership.Below completion index source → OrdinaryBorrowAuthority.LocalWrite
        ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
      ¬CandidateStableCallOwnership.Below completion index source → OrdinaryBorrowAuthority.ForeignWrite
        ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (formed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder (slot.after tag))
    (coherent : LocationCoherent (slot.after tag) location protections) (short : (slot.after tag).nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) location) :
    let result := (slot.after tag).performWildcardAccessAt location root (some selectedNode.tag) .Read protections (position != 0)
    result.status = .Completed ∧ LocationCoherent (slot.after tag) result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) result.location ∧
      (∀ query, ¬GeneralBorrowExposedNonleafPrimaryPath.Path tree root query → result.location.perms.get query = location.perms.get query) ∧
      (∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
        CandidateStableCallOwnership.Below completion index source → OrdinaryBorrowAuthority.LocalWrite
          ((result.location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
      (∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
        ¬CandidateStableCallOwnership.Below completion index source → OrdinaryBorrowAuthority.ForeignWrite
          ((result.location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) := by
  have initial := S05CompletedAncestryReadQueries.authorization_root tree completion location protections complete depth oldOrder
    position selectedPosition root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights
  have auth := S04ZeroRootObserverCallbacks.old tree slot tag depth location protections root position (some selectedNode.tag) .Read
    (GeneralBorrowExposedNonleafPrimaryPath.Path tree root) initial
  obtain ⟨nextDepth⟩ := formed.depth
  obtain ⟨done,_,cache,sifa,gp,effects,outside,pointwise,transfer⟩ := read_of_authorization
    (slot.after tag) location protections formed order nextDepth root position (some selectedNode.tag)
    (GeneralBorrowExposedNonleafPrimaryPath.Path tree root) auth coherent short profile possible
  have shapes (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
      (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index) :=
    S05CompletedAncestryReadQueries.query_shape tree completion location protections complete depth oldOrder position selectedPosition
      root selectedRoot source index node selectedNode rootSlot selectedSlot selectedPresent different selectedPath path present localRights
  have classification (index : UniIndex) (node : TreeNode) :
      residualRelation tree location protections root index node (some selectedNode.tag) .Read position [] =
      relation location root index node (some selectedNode.tag) .Read position := by
    rw [←initial_relation (slot.after tag) location protections root index node (some selectedNode.tag) .Read position coherent short]
    unfold residualRelation
    rw [S04ZeroRootObserverCallbacks.count tree slot tag depth location protections .Read [] root,
      S04ZeroRootObserverCallbacks.count tree slot tag depth location protections .Read [] index]
  refine ⟨done,cache,sifa,gp,outside,?_,?_⟩
  · intro index node present path below
    have shape := shapes index node present path
    dsimp only at shape
    rw [classification] at shape
    have nextPresent := S04ZeroRootObserverNormal.old_node tree slot tag index node present
    apply S05ReadRawAuthorityEndpoint.local_right _ _ _
      (relation location root index node (some selectedNode.tag) .Read position) (localRights index node present path below)
    · rcases shape.1 below with classified | classified <;> simp [classified]
    · exact transfer index node path nextPresent
  · intro index node present path below
    have shape := shapes index node present path
    dsimp only at shape
    rw [classification] at shape
    have nextPresent := S04ZeroRootObserverNormal.old_node tree slot tag index node present
    apply S05ReadRawAuthorityEndpoint.foreign_right _ _ _
      (relation location root index node (some selectedNode.tag) .Read position) (foreignRights index node present path below)
    · rcases shape.2 below with classified | classified <;> simp [classified]
    · exact transfer index node path nextPresent
    · exact effects index node nextPresent
    · exact pointwise index node nextPresent
    · exact profile.present index node nextPresent
    · exact gp index node nextPresent


/-- Actual old-root Write after the genuine Bool child attachment. Hidden-child
counts and legal masks are transported through repaired clauses directly. -/
theorem old_write_after_child (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (initial : DuplicatePrefixResidualWriteRepaired.Authorization tree before protections root position maximum .Write support)
    (notParent : ¬support parent)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode newNode)) :
    DuplicatePrefixResidualWriteRepaired.Authorization
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode,tagMapping := mapping,locations := locations}
      after protections root position maximum .Write support := by
  have auth := attached_repaired tree depth index parent parentNode newNode vacant parentPresent hidden size before after protections slots
    root position maximum .Write support initial notParent (fun query included => by
      obtain ⟨node,present⟩ := initial.present query included
      exact GeneralBorrowSharedAuthorizationGeometry.attached_covers tree depth index parent parentNode newNode vacant parentPresent
        nextDepth root query node present (initial.covers query included))
  refine ⟨auth.rooted,auth.present,auth.children,auth.covers,auth.possible,?_,auth.witness⟩
  intro entry exit legalEntry legalExit subset query node included present retained
  exact auth.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩ ⟨legalExit.distinct,legalExit.allowed⟩ subset query node included present retained

theorem old_write_after_child_access (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (initial : DuplicatePrefixResidualWriteRepaired.Authorization tree before protections root position maximum .Write support)
    (notParent : ¬support parent)
    (formed : GeneralBorrowStructuralHistoryState.GraphState
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode,tagMapping := mapping,locations := locations})
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode,tagMapping := mapping,locations := locations})
    (coherent : LocationCoherent
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode,tagMapping := mapping,locations := locations} after protections)
    (short : (attachedNodes tree.nodes index parent parentNode newNode).size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode,tagMapping := mapping,locations := locations} after protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode,tagMapping := mapping,locations := locations} after) :
    let nextTree := {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode,tagMapping := mapping,locations := locations}
    let result := nextTree.performWildcardAccessAt after root maximum .Write protections (position != 0)
    result.status = .Completed ∧ LocationCoherent nextTree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile nextTree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible nextTree result.location ∧
      ∀ query, ¬support query → result.location.perms.get query = after.perms.get query := by
  obtain ⟨nextDepth⟩ := formed.depth
  have auth := attached_repaired tree depth index parent parentNode newNode vacant parentPresent hidden size before after protections slots
    root position maximum .Write support initial notParent (fun query included => by
      obtain ⟨node,present⟩ := initial.present query included
      exact GeneralBorrowSharedAuthorizationGeometry.attached_covers tree depth index parent parentNode newNode vacant parentPresent
        nextDepth root query node present (initial.covers query included))
  have contextual : DuplicatePrefixResidualWriteRepaired.Authorization
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode,tagMapping := mapping,locations := locations}
      after protections root position maximum .Write support := by
    refine ⟨auth.rooted,auth.present,auth.children,auth.covers,auth.possible,?_,auth.witness⟩
    intro entry exit legalEntry legalExit subset query node included present retained
    exact auth.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩ ⟨legalExit.distinct,legalExit.allowed⟩ subset query node included present retained
  exact write_of_authorization _ after protections formed order nextDepth root position maximum support contextual coherent short profile possible

end DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.old_read_access,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.new_read_access,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.new_read,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.read_of_authorization,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.old_write_after_child,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.old_write_after_child_access,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.old_write,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.new_foreign,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.old_write_access,
      ``DuplicatePrefix.CurrentCallEmptyEntryZeroRootQueries.new_write_access] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "empty zero-root query transport depends on unapproved axiom {dependency}"
