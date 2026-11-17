import duplicate_prefix.GeneralBorrowSnapshotReadRuntime
import duplicate_prefix.DuplicatePrefixNormalKind
import duplicate_prefix.GeneralBorrowCompatibleScopedPreservation
import duplicate_prefix.GeneralBorrowCompatibleLocationSifaConsistency
import duplicate_prefix.GeneralBorrowCompatibleNormalPossible

namespace DuplicatePrefix.GeneralBorrowReadCapabilityNormal
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess GeneralBorrowProjection GeneralBorrowEvents
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

abbrev ReadCompatible (state : LocationState) (related : AccessRelatedness) (held : Bool) : Prop :=
  DuplicatePrefixScalarAuthorization.Compatible state .Read related held

/-- A real scalar Read preserves its exact Read table at the same relation.
Foreign Disabled is admitted wherever the raw table admits it. -/
theorem transition (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : ReadCompatible state related held) :
    ∃ next delta, state.performAccess .Read related held = .Success next delta ∧
      ReadCompatible next related held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [ReadCompatible,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_⟩;simp [ReadCompatible,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [ReadCompatible,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_⟩;simp [ReadCompatible,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])

/-- Real skip/record/access from the Read table alone. -/
theorem visit (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : ReadCompatible state related held) :
    state.skipIfKnownNoop .Read related = .SkipSelfAndChildren ∨
      ∃ recorded next delta, state.recordNewAccess .Read related = .Recorded recorded ∧
        recorded.performAccess .Read related held = .Success next delta ∧
        ReadCompatible next related held := by
  cases skip : state.skipIfKnownNoop .Read related with
  | SkipSelfAndChildren => exact .inl rfl
  | Recurse =>
    let recorded := {state with idempotentForeignAccess := (IdempotentForeignAccess.recordNew
      state.idempotentForeignAccess (IdempotentForeignAccess.fromAccessAndRelatedness .Read related))}
    have inherited : ReadCompatible recorded related held := by cases related <;> exact initial
    obtain ⟨next,delta,actual,preserved⟩ := transition recorded related held inherited
    exact .inr ⟨recorded,next,delta,by simp [LocationState.recordNewAccess,skip,recorded],actual,preserved⟩

/-- Ownership labels constrain only the selected graph component. -/
def Pointwise (support : Nat → Prop) (tree : NormalTreeState) (related : Nat → AccessRelatedness) : Prop :=
  ∀ index, support index → index < tree.locationStates.size → ∃ state, tree.stateAt index = some state ∧
    ReadCompatible state (related index) (tree.protectedNodes.contains index)

theorem update_pointwise (support : Nat → Prop) (tree : NormalTreeState) (related : Nat → AccessRelatedness)
    (owned : Pointwise support tree related) (index : Nat) (valid : index < tree.locationStates.size)
    (next : LocationState) (nextOwned : ReadCompatible next (related index) (tree.protectedNodes.contains index)) :
    Pointwise support {tree with locationStates := tree.locationStates.set index (some next) valid} related := by
  intro position positionSupported positionValid
  have beforeValid : position < tree.locationStates.size := by simpa using positionValid
  by_cases same : position = index
  · subst position
    exact ⟨next,by simp [NormalTreeState.stateAt,valid],nextOwned⟩
  · obtain ⟨old,present,oldOwned⟩ := owned position positionSupported beforeValid
    exact ⟨old,(stateAt_update_other tree index position next valid same).trans present,oldOwned⟩

theorem event_cons (tree : NormalTreeState) (root : Nat) (event : TraversalEvent)
    (state : LocationState)
    (present : tree.stateAt event.node = some state) (valid : event.node < tree.locationStates.size)
    (owned : ReadCompatible state event.relatedness (tree.protectedNodes.contains event.node))
    (scheduled : Scheduled state .Read event.relatedness) :
    ∃ next, ReadCompatible next event.relatedness (tree.protectedNodes.contains event.node) ∧
      ∀ rest, sourceNormalEvents tree root .Read (event :: rest) =
        let later := sourceNormalEvents {tree with locationStates := tree.locationStates.set event.node (some next) valid} root .Read rest
        {later with visited := event :: later.visited} := by
  obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
    (visit state event.relatedness (tree.protectedNodes.contains event.node) owned).resolve_left
      (by rw [scheduled_recurse state .Read event.relatedness scheduled]; decide)
  refine ⟨next,preserved,?_⟩
  intro rest
  unfold_normal_events
  simp only [present,record,access,valid,↓reduceDIte]
  rfl

theorem events_preserve (support : Nat → Prop) (events : List TraversalEvent) (root : Nat)
    (tree : NormalTreeState) (related : Nat → AccessRelatedness)
    (owned : Pointwise support tree related) (distinct : (events.map TraversalEvent.node).Nodup)
    (recordable : GeneralBorrowOwnership.Recordable tree .Read events)
    (confined : ∀ event ∈ events, support event.node)
    (relations : ∀ event ∈ events, event.relatedness = related event.node) :
    (sourceNormalEvents tree root .Read events).status = .Completed ∧
      Pointwise support (sourceNormalEvents tree root .Read events).tree related := by
  induction events generalizing tree with
  | nil => unfold_normal_events; exact ⟨trivial,owned⟩
  | cons event rest ih =>
    obtain ⟨state,present,valid,scheduled⟩ := recordable event (by simp)
    obtain ⟨old,oldPresent,oldOwned⟩ := owned event.node (confined event (by simp)) valid
    have oldEq : old = state := Option.some.inj (oldPresent.symm.trans present)
    subst old
    have relationEq := relations event (by simp)
    have eventOwned : ReadCompatible state event.relatedness (tree.protectedNodes.contains event.node) := by
      rw [relationEq]; exact oldOwned
    obtain ⟨next,preserved,step⟩ := event_cons tree root event state present valid eventOwned scheduled
    have nextOwned := update_pointwise support tree related owned event.node valid next (by rw [←relationEq]; exact preserved)
    rw [step]
    simp only [List.map_cons,List.nodup_cons] at distinct
    apply ih _ nextOwned distinct.2
    · intro later member
      obtain ⟨old,oldPresent,oldValid,oldScheduled⟩ := recordable later (by simp [member])
      have different : later.node ≠ event.node := by
        intro same
        exact distinct.1 (List.mem_map.mpr ⟨later,member,same⟩)
      exact ⟨old,(stateAt_update_other tree event.node later.node next valid different).trans oldPresent,
        by simpa using oldValid,oldScheduled⟩
    · exact fun later member => confined later (by simp [member])
    · exact fun later member => relations later (by simp [member])

/-- Actual normal execution preserves the exact Read scalar capability inside the
selected component; outside nodes have no permission assumptions. -/
theorem normal_preserves (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (valid : anchor < tree.topology.nodes.size) (mode : ChildrenVisitMode)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (component : GeneralBorrowExposedScopedNormal.Component tree.topology anchor)
    (owned : Pointwise component.support tree (GeneralBorrowAnchor.relation tree anchor)) :
    (tree.performAccess anchor .Read mode).status = .Completed ∧
      Pointwise component.support (tree.performAccess anchor .Read mode).tree (GeneralBorrowAnchor.relation tree anchor) := by
  let schedule := tree.topology.traverse anchor mode (sourceNormalSkipped tree .Read)
  have data := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree .Read)
  have confined := GeneralBorrowPresence.traversal_present tree.topology component.support
    component.parents component.children anchor component.anchor mode (sourceNormalSkipped tree .Read)
  apply events_preserve component.support schedule.2 schedule.1 tree (GeneralBorrowAnchor.relation tree anchor) owned data.1
  · intro event member
    have eventValid : event.node < tree.locationStates.size := by rw [aligned]; exact (data.2 event member).1
    obtain ⟨state,present,_⟩ := owned event.node (confined event member) eventValid
    refine ⟨state,present,eventValid,?_⟩
    apply recurse_scheduled
    cases relatedEq : event.relatedness with
    | LocalAccess => rfl
    | ForeignAccess =>
      have notSkipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology
        (sourceNormalSkipped tree .Read) anchor mode event member relatedEq
      have noSkip : state.skipIfKnownNoop .Read .ForeignAccess ≠ .SkipSelfAndChildren := by
        intro skipped
        exact notSkipped ((skipped_iff tree .Read event.node state present (data.2 event member).1).mpr skipped)
      cases skip : state.skipIfKnownNoop .Read .ForeignAccess with
      | Recurse => rfl
      | SkipSelfAndChildren => exact False.elim (noSkip skip)
  · exact confined
  · exact fun event member => (data.2 event member).2
/-- Real stored-row write-back retains the selected component’s Read capability.
The relation is the immutable initial topology relation. Other roots may be
exposed and protected and need no ownership hypothesis. -/
theorem access_preserves (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (aligned : (source_normal_projection tree location protections).locationStates.size =
      (source_normal_projection tree location protections).topology.nodes.size)
    (component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : Pointwise component.support (source_normal_projection tree location protections)
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat)) :
    Pointwise component.support
      (source_normal_projection tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections)
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
  rw [GeneralBorrowRangePreserves.normal_projection tree location protections anchor .Read mode fits]
  exact (normal_preserves _ forest anchor.toNat valid mode aligned component owned).2

/-- Actual normal Read preserves the same operation-specific capability and
all physical runtime fields from its raw component/table. No source Write
capability, hidden topology or successful-operation premise is required. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (capability : DuplicatePrefixNormalKind.Capability tree location protections anchor .Read)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let result := tree.performNormalAccessAt location anchor .Read protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    ∃ next : DuplicatePrefixNormalKind.Capability tree result.location protections anchor .Read,
      next.component = capability.component := by
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨depth⟩ := formed.depth
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections anchor anchorNode present
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    change tree.nodes.data.size < 65536 at short
    omega
  have aligned : (source_normal_projection tree location protections).locationStates.size =
      (source_normal_projection tree location protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_mapIdx,Array.size_map]
  have initial : Pointwise capability.component.support (source_normal_projection tree location protections)
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
    intro index supported valid
    exact capability.permissions index supported (by rw [←(projection_sizes tree location protections).1];exact valid)
  have preserved := access_preserves tree location protections anchor mode fits forest geometry.1 aligned capability.component initial
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      anchor.toNat .Read capability.component := by
    intro index supported valid
    apply capability.permissions index supported
    have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    simpa only [size] using valid
  have completed := DuplicatePrefixNormalKind.access tree location protections anchor .Read mode capability formed anchorNode present coherent
  have sifa := GeneralBorrowCompatibleLocationSifaConsistency.normal tree location protections anchor .Read mode
    fits depth formed.children anchorNode present forest capability.component owned profile
  let next : DuplicatePrefixNormalKind.Capability tree
      (tree.performNormalAccessAt location anchor .Read protections mode).location protections anchor .Read := {
    component := capability.component
    permissions := by
      intro index supported valid
      have afterValid : index < (source_normal_projection tree
          (tree.performNormalAccessAt location anchor .Read protections mode).location protections).locationStates.size := by
        rw [(projection_sizes tree _ protections).1]
        exact valid
      exact preserved index supported afterValid }
  refine ⟨completed.1,completed.2.1,completed.2.2,sifa.2.2,?_,next,rfl⟩
  · intro index node present
    change (((tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get index).getD
      node.defaultLocationState).possible = true
    by_cases inside : capability.component.support index.toNat
    · have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
      have afterValid : index.toNat < (source_normal_projection tree
          (tree.performNormalAccessAt location anchor .Read protections mode).location protections).locationStates.size := by
        rw [(projection_sizes tree _ protections).1]
        exact bounded
      obtain ⟨state,stored,compatible⟩ := preserved index.toNat inside afterValid
      rw [projection_location_state tree _ protections index node present] at stored
      have equal : ((tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get index).getD
          node.defaultLocationState = state := by
        simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,Option.some.injEq] using stored
      rw [equal]
      exact compatible.1
    · rw [GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor .Read mode capability.component index node present inside]
      exact possible index node present

end DuplicatePrefix.GeneralBorrowReadCapabilityNormal
