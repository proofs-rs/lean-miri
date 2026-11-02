import duplicate_prefix.GeneralBorrowOwnership
import duplicate_prefix.DuplicatePrefixScalarBothAuthorization
import duplicate_prefix.GeneralBorrowRangePreserves
import duplicate_prefix.GeneralBorrowExposedScopedNormal
namespace DuplicatePrefix.GeneralBorrowCompatibleScopedPreservation
open Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.DuplicatePrefixScalarBothAuthorization DuplicatePrefix.GeneralBorrowEvents
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Ownership labels constrain only the selected graph component. -/
def Pointwise (support : Nat → Prop) (tree : NormalTreeState) (related : Nat → AccessRelatedness) : Prop :=
  ∀ index, support index → index < tree.locationStates.size → ∃ state, tree.stateAt index = some state ∧
    Both state (related index) (tree.protectedNodes.contains index)

theorem update_pointwise (support : Nat → Prop) (tree : NormalTreeState) (related : Nat → AccessRelatedness)
    (owned : Pointwise support tree related) (index : Nat) (valid : index < tree.locationStates.size)
    (next : LocationState) (nextOwned : Both next (related index) (tree.protectedNodes.contains index)) :
    Pointwise support {tree with locationStates := tree.locationStates.set index (some next) valid} related := by
  intro position positionSupported positionValid
  have beforeValid : position < tree.locationStates.size := by simpa using positionValid
  by_cases same : position = index
  · subst position
    exact ⟨next,by simp [NormalTreeState.stateAt,valid],nextOwned⟩
  · obtain ⟨old,present,oldOwned⟩ := owned position positionSupported beforeValid
    exact ⟨old,(stateAt_update_other tree index position next valid same).trans present,oldOwned⟩

theorem event_cons (tree : NormalTreeState) (root : Nat) (event : TraversalEvent)
    (kind : AccessKind) (state : LocationState)
    (present : tree.stateAt event.node = some state) (valid : event.node < tree.locationStates.size)
    (owned : Both state event.relatedness (tree.protectedNodes.contains event.node))
    (scheduled : Scheduled state kind event.relatedness) :
    ∃ next, Both next event.relatedness (tree.protectedNodes.contains event.node) ∧
      ∀ rest, sourceNormalEvents tree root kind (event :: rest) =
        let later := sourceNormalEvents {tree with locationStates := tree.locationStates.set event.node (some next) valid} root kind rest
        {later with visited := event :: later.visited} := by
  obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
    (visit state event.relatedness (tree.protectedNodes.contains event.node) kind owned).resolve_left
      (by rw [scheduled_recurse state kind event.relatedness scheduled]; decide)
  refine ⟨next,preserved,?_⟩
  intro rest
  unfold_normal_events
  simp only [present,record,access,valid,↓reduceDIte]
  rfl

theorem events_preserve (support : Nat → Prop) (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (related : Nat → AccessRelatedness)
    (owned : Pointwise support tree related) (distinct : (events.map TraversalEvent.node).Nodup)
    (recordable : GeneralBorrowOwnership.Recordable tree kind events)
    (confined : ∀ event ∈ events, support event.node)
    (relations : ∀ event ∈ events, event.relatedness = related event.node) :
    (sourceNormalEvents tree root kind events).status = .Completed ∧
      Pointwise support (sourceNormalEvents tree root kind events).tree related := by
  induction events generalizing tree with
  | nil => unfold_normal_events; exact ⟨trivial,owned⟩
  | cons event rest ih =>
    obtain ⟨state,present,valid,scheduled⟩ := recordable event (by simp)
    obtain ⟨old,oldPresent,oldOwned⟩ := owned event.node (confined event (by simp)) valid
    have oldEq : old = state := Option.some.inj (oldPresent.symm.trans present)
    subst old
    have relationEq := relations event (by simp)
    have eventOwned : Both state event.relatedness (tree.protectedNodes.contains event.node) := by
      rw [relationEq]; exact oldOwned
    obtain ⟨next,preserved,step⟩ := event_cons tree root event kind state present valid eventOwned scheduled
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

/-- Actual normal execution preserves both exact scalar capabilities inside the
selected component; outside nodes have no permission assumptions. -/
theorem normal_preserves (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (valid : anchor < tree.topology.nodes.size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (component : GeneralBorrowExposedScopedNormal.Component tree.topology anchor)
    (owned : Pointwise component.support tree (GeneralBorrowAnchor.relation tree anchor)) :
    (tree.performAccess anchor kind mode).status = .Completed ∧
      Pointwise component.support (tree.performAccess anchor kind mode).tree (GeneralBorrowAnchor.relation tree anchor) := by
  let schedule := tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)
  have data := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree kind)
  have confined := GeneralBorrowPresence.traversal_present tree.topology component.support
    component.parents component.children anchor component.anchor mode (sourceNormalSkipped tree kind)
  apply events_preserve component.support schedule.2 schedule.1 kind tree (GeneralBorrowAnchor.relation tree anchor) owned data.1
  · intro event member
    have eventValid : event.node < tree.locationStates.size := by rw [aligned]; exact (data.2 event member).1
    obtain ⟨state,present,_⟩ := owned event.node (confined event member) eventValid
    refine ⟨state,present,eventValid,?_⟩
    apply recurse_scheduled
    cases relatedEq : event.relatedness with
    | LocalAccess => rfl
    | ForeignAccess =>
      have notSkipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology
        (sourceNormalSkipped tree kind) anchor mode event member relatedEq
      have noSkip : state.skipIfKnownNoop kind .ForeignAccess ≠ .SkipSelfAndChildren := by
        intro skipped
        exact notSkipped ((skipped_iff tree kind event.node state present (data.2 event member).1).mpr skipped)
      cases skip : state.skipIfKnownNoop kind .ForeignAccess with
      | Recurse => rfl
      | SkipSelfAndChildren => exact False.elim (noSkip skip)
  · exact confined
  · exact fun event member => (data.2 event member).2
/-- Real stored-row write-back retains the selected component’s two scalar capabilities.
The relation is the immutable initial topology relation. Other roots may be
exposed and protected and need no ownership hypothesis. -/
theorem access_preserves (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
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
      (source_normal_projection tree (tree.performNormalAccessAt location anchor kind protections mode).location protections)
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
  rw [GeneralBorrowRangePreserves.normal_projection tree location protections anchor kind mode fits]
  exact (normal_preserves _ forest anchor.toNat valid kind mode aligned component owned).2

private theorem slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (index : UniIndex) (converted : UniIndex.ofNat? position = some index) (equal : index.toNat = position)
    (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get index).getD
        (((tree.nodeAt index).map TreeNode.defaultLocationState).getD ⟨.Disabled,false,.None⟩)) := by
  have nodeValue : tree.nodeAt index = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,converted,Option.map_some]
  rw [nodeValue]
  cases stored : location.perms.get index <;> cases tree.nodes.data[position] <;> rfl

/-- Exact raw permission framing on the selected component transfers its
two scalar capabilities independently of cache changes in other components. -/
theorem row_frame (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (support : Nat → Prop) (related : Nat → AccessRelatedness)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (owned : Pointwise support (source_normal_projection tree before protections) related)
    (same : ∀ index, support index.toNat → after.perms.get index = before.perms.get index) :
    Pointwise support (source_normal_projection tree after protections) related := by
  intro position supported valid
  have bound : position < tree.nodes.data.size := by
    rw [(GeneralBorrowProjection.projection_sizes tree after protections).1] at valid
    exact valid
  have oldValid : position < (source_normal_projection tree before protections).locationStates.size := by
    rw [(GeneralBorrowProjection.projection_sizes tree before protections).1]
    exact bound
  obtain ⟨index,converted,equal⟩ := GeneralBorrowProjection.index_nat position (by omega)
  obtain ⟨state,present,permission⟩ := owned position supported oldValid
  refine ⟨state,?_,permission⟩
  rw [slot tree after protections position index converted equal bound,
    same index (by simpa only [equal] using supported),
    ←slot tree before protections position index converted equal bound]
  exact present

end DuplicatePrefix.GeneralBorrowCompatibleScopedPreservation
