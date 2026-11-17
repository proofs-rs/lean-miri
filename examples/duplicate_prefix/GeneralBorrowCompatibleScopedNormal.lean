import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowExposedScopedNormal

namespace DuplicatePrefix.GeneralBorrowCompatibleScopedNormal
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowPresence
open GeneralBorrowExposedScopedNormal (Component)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Exact source scalar permission compatibility only inside the actual graph
component. This is broader than the legacy ownership/profile predicates and
contains no operation-success or final-permission field. -/
def Owned (tree : NormalTreeState) (anchor : Nat) (kind : AccessKind)
    (component : Component tree.topology anchor) : Prop :=
  ∀ index, component.support index → index < tree.topology.nodes.size →
    ∃ state, tree.stateAt index = some state ∧
      DuplicatePrefixScalarAuthorization.Compatible state kind
        (GeneralBorrowAnchor.relation tree anchor index) (tree.protectedNodes.contains index)

private theorem event_cons (tree : NormalTreeState) (root : Nat) (kind : AccessKind)
    (event : TraversalEvent) (state : LocationState)
    (present : tree.stateAt event.node = some state) (valid : event.node < tree.locationStates.size)
    (initial : DuplicatePrefixScalarAuthorization.Compatible state kind event.relatedness (tree.protectedNodes.contains event.node))
    (scheduled : Scheduled state kind event.relatedness) :
    ∃ next, ∀ rest, sourceNormalEvents tree root kind (event :: rest) =
      let later := sourceNormalEvents {tree with locationStates := tree.locationStates.set event.node (some next) valid} root kind rest
      {later with visited := event :: later.visited} := by
  let recorded := {state with idempotentForeignAccess := (
    IdempotentForeignAccess.recordNew state.idempotentForeignAccess
      (IdempotentForeignAccess.fromAccessAndRelatedness kind event.relatedness))}
  have compatible : DuplicatePrefixScalarAuthorization.Compatible recorded kind event.relatedness (tree.protectedNodes.contains event.node) := by
    cases kind <;> exact initial
  have possible : recorded.possible = true := by
    cases kind <;> exact initial.1
  obtain ⟨next, transition, performed⟩ :=
    (DuplicatePrefixScalarAuthorization.compatible_iff recorded kind event.relatedness _ possible).mp compatible
  have record : state.recordNewAccess kind event.relatedness = .Recorded recorded := by
    simp only [LocationState.recordNewAccess, scheduled_recurse state kind event.relatedness scheduled, beq_self_eq_true, ↓reduceIte]
    rfl
  refine ⟨next, ?_⟩
  intro rest
  unfold_normal_events
  simp only [present, record, performed, valid, ↓reduceDIte]
  rfl

private theorem events (items : List TraversalEvent) (root : Nat) (kind : AccessKind) (tree : NormalTreeState)
    (distinct : (items.map TraversalEvent.node).Nodup)
    (initial : ∀ event ∈ items, ∃ state, tree.stateAt event.node = some state ∧ event.node < tree.locationStates.size ∧
      DuplicatePrefixScalarAuthorization.Compatible state kind event.relatedness (tree.protectedNodes.contains event.node) ∧
      Scheduled state kind event.relatedness) :
    (sourceNormalEvents tree root kind items).status = .Completed := by
  induction items generalizing tree with
  | nil => unfold_normal_events
  | cons event rest ih =>
    obtain ⟨state, present, valid, compatible, scheduled⟩ := initial event (by simp)
    obtain ⟨next, step⟩ := event_cons tree root kind event state present valid compatible scheduled
    rw [step]
    simp only [List.map_cons, List.nodup_cons] at distinct
    apply ih _ distinct.2
    intro later member
    obtain ⟨old, oldPresent, oldValid, oldCompatible, oldScheduled⟩ := initial later (by simp [member])
    have different : later.node ≠ event.node := by
      intro same
      exact distinct.1 (List.mem_map.mpr ⟨later, member, same⟩)
    refine ⟨old, ?_, ?_, oldCompatible, oldScheduled⟩
    · rw [stateAt_update_other tree event.node later.node next valid different]
      exact oldPresent
    · simpa using oldValid

/-- The real normal visitor completes under exact raw scalar compatibility on
its graph component, for either kind and either child-visit mode. Neither
Unique ancestors nor Disabled foreign/exposed nodes are required. Permissions
in other components are unconstrained by this theorem. -/
theorem normal (tree : NormalTreeState) (anchor : Nat) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest tree.topology) (valid : anchor < tree.topology.nodes.size)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (component : Component tree.topology anchor) (owned : Owned tree anchor kind component) :
    (tree.performAccess anchor kind mode).status = .Completed := by
  have shape := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree kind)
  have confined := traversal_present tree.topology component.support component.parents component.children
    anchor component.anchor mode (sourceNormalSkipped tree kind)
  unfold NormalTreeState.performAccess
  apply events _ _ _ tree shape.1
  intro event member
  have inside := confined event member
  have facts := shape.2 event member
  obtain ⟨state, present, compatible⟩ := owned event.node inside facts.1
  refine ⟨state, present, by rw [aligned]; exact facts.1, ?_, ?_⟩
  · simpa only [GeneralBorrowAnchor.relation, ←facts.2] using compatible
  · apply recurse_scheduled
    cases related : event.relatedness with
    | LocalAccess => rfl
    | ForeignAccess =>
      have unskipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology
        (sourceNormalSkipped tree kind) anchor mode event member related
      have cannotSkip : state.skipIfKnownNoop kind .ForeignAccess ≠ .SkipSelfAndChildren := by
        intro skip
        exact unskipped ((skipped_iff tree kind event.node state present facts.1).mpr skip)
      cases skip : state.skipIfKnownNoop kind .ForeignAccess with
      | Recurse => rfl
      | SkipSelfAndChildren => exact False.elim (cannotSkip skip)

/-- Actual normal-access completion, including the real permission write-back
and exposed-cache loop. Only the selected component carries initial permission
compatibility; outside physical components retain arbitrary permissions. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () := by
  let projection := source_normal_projection tree location protections
  let normalResult := projection.performAccess anchor.toNat kind mode
  let schedule := projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)
  have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor anchorNode anchorPresent
  have topologySize : projection.topology.nodes.size = tree.nodes.data.size := by
    dsimp only [projection]
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have sizes := projection_sizes tree location protections
  have completed : normalResult.status = .Completed := normal projection anchor.toNat kind mode forest
    (by rw [topologySize];exact bounded) (sizes.1.trans topologySize.symm) component owned
  refine ⟨completed,?_⟩
  have visited : normalResult.visited = schedule.2 := GeneralBorrowStorage.events_visited schedule.2 schedule.1 kind projection completed
  have aligned : projection.defaultStates.size = projection.locationStates.size := sizes.2.trans sizes.1.symm
  have metadata : ∀ event ∈ normalResult.visited, ∃ index node oldState newState,
      UniIndex.ofNat? event.node = some index ∧ tree.nodeAt index = some node ∧
      tree.locationStateAt location index = some oldState ∧ normalResult.tree.stateAt event.node = some newState := by
    intro event member
    rw [visited] at member
    obtain ⟨index,node,converted,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location protections
      depth children anchor anchorNode anchorPresent kind mode event member
    obtain ⟨indexValid,_⟩ := array_of_node tree index node present
    have eventValid : event.node < projection.locationStates.size := by rw [sizes.1];omega
    obtain ⟨newState,newPresent⟩ := GeneralBorrowStorage.events_total schedule.2 schedule.1 kind projection aligned event.node eventValid
    exact ⟨index,node,(location.perms.get index).getD node.defaultLocationState,newState,converted,present,
      by simp [BorrowTree.locationStateAt,present],newPresent⟩
  unfold BorrowTree.performNormalAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_normal_cache_scan
  have step : ∀ event member state, state.2 = (.ok () : Except ExposedCacheError Unit) → (scan event member state).value.2 = .ok () := by
    intro event member state good
    rcases state with ⟨current,outcome⟩
    dsimp only at good
    subst outcome
    obtain ⟨index,node,oldState,newState,converted,present,oldPresent,newPresent⟩ := metadata event member
    have cacheOK : ∀ oldLevel newLevel, (current.exposedCache.updateExposure tree.nodes index oldLevel newLevel).outcome = .ok () :=
      fun oldLevel newLevel => update_exposure_succeeds current.exposedCache tree.nodes depth index node present oldLevel newLevel
    dsimp only [normalResult,projection] at newPresent
    simp only [scan,converted,present,oldPresent,newPresent,↓reduceIte]
    split
    · cases transition : performAccessTransition kind event.relatedness oldState.permission (protections.contains node.tag) with
      | UndefinedBehavior => rfl
      | ImpossibleProtectedReservedIM => rfl
      | Transition change => cases noop : change.isNoop <;> simp [noop,ForInStep.value,cacheOK]
    · rfl
  exact DuplicatePrefix.GeneralBorrowLoop.list_invariant' _ scan (fun state => state.2 = (.ok () : Except ExposedCacheError Unit)) step _ rfl

/-- Concrete call-time normal authorization from S01 now supplies the actual
normal operation, including real permission write-back and cache updates. This
is one phase: other-root callbacks and later-operation preservation remain
separate obligations, not hidden success premises. -/
theorem of_call_authorization (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (anchor : UniIndex) (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags anchor)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    (tree.performNormalAccessAt location anchor kind global.protectedTags mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind global.protectedTags mode).outcome = .ok () := by
  obtain ⟨forest⟩ := runtime.formed.forest location global.protectedTags
  obtain ⟨depth⟩ := runtime.formed.depth
  apply access tree location global.protectedTags anchor kind mode forest authorization.component _ depth runtime.formed.children anchorNode present
  intro index included valid
  have topologySize : (source_normal_projection tree location global.protectedTags).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  exact authorization.permissions kind index included (by rw [←topologySize]; exact valid)

end DuplicatePrefix.GeneralBorrowCompatibleScopedNormal
