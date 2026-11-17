import duplicate_prefix.GeneralBorrowObserverReadScalar

namespace DuplicatePrefix.GeneralBorrowObserverReadNormal
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess GeneralBorrowProjection GeneralBorrowEvents DuplicatePrefixScalarBothAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- An independent observer Both capability evaluated under virtual protectors,
while the actual normal Read uses the tree's physical protector list. -/
def Pointwise (support : Nat → Prop) (tree : NormalTreeState)
    (related : Nat → AccessRelatedness) (held : Nat → Bool) : Prop :=
  ∀ index,support index → index < tree.locationStates.size →
    ∃ state,tree.stateAt index = some state ∧ Both state (related index) (held index)

theorem update (support : Nat → Prop) (tree : NormalTreeState)
    (related : Nat → AccessRelatedness) (held : Nat → Bool)
    (owned : Pointwise support tree related held) (index : Nat) (valid : index < tree.locationStates.size)
    (next : LocationState) (preserved : support index → Both next (related index) (held index)) :
    Pointwise support {tree with locationStates := tree.locationStates.set index (some next) valid} related held := by
  intro query included bounded
  have oldBound : query < tree.locationStates.size := by simpa using bounded
  by_cases same : query = index
  · subst query
    exact ⟨next,by simp [NormalTreeState.stateAt,valid],preserved included⟩
  · obtain ⟨state,present,both⟩ := owned query included oldBound
    exact ⟨state,(stateAt_update_other tree index query next valid same).trans present,both⟩

theorem event_cons (support : Nat → Prop) (tree : NormalTreeState) (root : Nat) (event : TraversalEvent)
    (related : Nat → AccessRelatedness) (held : Nat → Bool)
    (observer : Pointwise support tree related held)
    (state : LocationState) (present : tree.stateAt event.node = some state) (valid : event.node < tree.locationStates.size)
    (source : GeneralBorrowReadCapabilityNormal.ReadCompatible state event.relatedness (tree.protectedNodes.contains event.node))
    (scheduled : Scheduled state .Read event.relatedness)
    (localSource : support event.node → related event.node = .LocalAccess → event.relatedness = .LocalAccess)
    (foreignLocal : support event.node → related event.node = .ForeignAccess → event.relatedness = .LocalAccess → held event.node = false)
    (foreignHeld : support event.node → event.relatedness = .ForeignAccess → tree.protectedNodes.contains event.node = held event.node) :
    ∃ next,(support event.node → Both next (related event.node) (held event.node)) ∧
      ∀ rest,sourceNormalEvents tree root .Read (event::rest) =
        let later := sourceNormalEvents {tree with locationStates := tree.locationStates.set event.node (some next) valid} root .Read rest
        {later with visited := event::later.visited} := by
  have recurse : state.skipIfKnownNoop .Read event.relatedness ≠ .SkipSelfAndChildren := by
    rw [scheduled_recurse state .Read event.relatedness scheduled];decide
  have step : ∃ recorded next delta,state.recordNewAccess .Read event.relatedness = .Recorded recorded ∧
      recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node) = .Success next delta ∧
      (support event.node → Both next (related event.node) (held event.node)) := by
    by_cases included : support event.node
    · obtain ⟨old,oldPresent,both⟩ := observer event.node included valid
      have equal := Option.some.inj (oldPresent.symm.trans present)
      subst old
      obtain ⟨recorded,next,delta,record,access,preserved⟩ :=
        (GeneralBorrowObserverReadScalar.visit state (related event.node) event.relatedness _ _ both source
          (localSource included) (foreignLocal included) (foreignHeld included)).resolve_left recurse
      exact ⟨recorded,next,delta,record,access,fun _ => preserved⟩
    · obtain ⟨recorded,next,delta,record,access,_⟩ :=
        (GeneralBorrowReadCapabilityNormal.visit state event.relatedness _ source).resolve_left recurse
      exact ⟨recorded,next,delta,record,access,fun impossible => False.elim (included impossible)⟩
  obtain ⟨recorded,next,delta,record,access,preserved⟩ := step
  refine ⟨next,preserved,?_⟩
  intro rest
  unfold_normal_events
  simp only [present,record,access,valid,↓reduceDIte]
  rfl

/-- One traversal of the actual event list carries the observer's independent
Both table. Source Read permissions derive every executed scalar transition. -/
theorem events (support : Nat → Prop) (items : List TraversalEvent) (root : Nat)
    (tree : NormalTreeState) (related sourceRelated : Nat → AccessRelatedness) (held : Nat → Bool)
    (observer : Pointwise support tree related held)
    (distinct : (items.map TraversalEvent.node).Nodup)
    (source : ∀ event ∈ items,∃ state,tree.stateAt event.node = some state ∧ event.node < tree.locationStates.size ∧
      GeneralBorrowReadCapabilityNormal.ReadCompatible state event.relatedness (tree.protectedNodes.contains event.node) ∧
      Scheduled state .Read event.relatedness)
    (relations : ∀ event ∈ items,event.relatedness = sourceRelated event.node)
    (localSource : ∀ index,support index → related index = .LocalAccess → sourceRelated index = .LocalAccess)
    (foreignLocal : ∀ index,support index → related index = .ForeignAccess → sourceRelated index = .LocalAccess → held index = false)
    (foreignHeld : ∀ index,support index → sourceRelated index = .ForeignAccess → tree.protectedNodes.contains index = held index) :
    (sourceNormalEvents tree root .Read items).status = .Completed ∧
      Pointwise support (sourceNormalEvents tree root .Read items).tree related held := by
  induction items generalizing tree with
  | nil => unfold_normal_events;exact ⟨trivial,observer⟩
  | cons event rest ih =>
    obtain ⟨state,present,valid,compatible,scheduled⟩ := source event (by simp)
    have relation := relations event (by simp)
    obtain ⟨next,preserved,actual⟩ := event_cons support tree root event related held observer state present valid compatible scheduled
      (by rw [relation];exact localSource event.node)
      (by rw [relation];exact foreignLocal event.node)
      (by rw [relation];exact foreignHeld event.node)
    have nextObserver := update support tree related held observer event.node valid next preserved
    rw [actual]
    simp only [List.map_cons,List.nodup_cons] at distinct
    apply ih _ nextObserver distinct.2
    · intro later member
      obtain ⟨old,oldPresent,oldValid,oldCompatible,oldScheduled⟩ := source later (by simp [member])
      have different : later.node ≠ event.node := by
        intro same
        exact distinct.1 (List.mem_map.mpr ⟨later,member,same⟩)
      exact ⟨old,(stateAt_update_other tree event.node later.node next valid different).trans oldPresent,
        by simpa using oldValid,oldCompatible,oldScheduled⟩
    · exact fun later member => relations later (by simp [member])
    · exact foreignHeld

/-- Pure actual normal Read preserves an arbitrary observer Both component
under virtual protection. Geometry/protector guards are local data, and source
normal authorization requires Read only. -/
theorem normal (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (valid : anchor < tree.topology.nodes.size) (mode : ChildrenVisitMode)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (component : GeneralBorrowExposedScopedNormal.Component tree.topology anchor)
    (source : GeneralBorrowReadCapabilityNormal.Pointwise component.support tree (GeneralBorrowAnchor.relation tree anchor))
    (support : Nat → Prop) (related : Nat → AccessRelatedness) (held : Nat → Bool)
    (observer : Pointwise support tree related held)
    (localSource : ∀ index,support index → related index = .LocalAccess → GeneralBorrowAnchor.relation tree anchor index = .LocalAccess)
    (foreignLocal : ∀ index,support index → related index = .ForeignAccess → GeneralBorrowAnchor.relation tree anchor index = .LocalAccess → held index = false)
    (foreignHeld : ∀ index,support index → GeneralBorrowAnchor.relation tree anchor index = .ForeignAccess → tree.protectedNodes.contains index = held index) :
    (tree.performAccess anchor .Read mode).status = .Completed ∧
      Pointwise support (tree.performAccess anchor .Read mode).tree related held := by
  let schedule := tree.topology.traverse anchor mode (sourceNormalSkipped tree .Read)
  have data := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree .Read)
  have confined := GeneralBorrowPresence.traversal_present tree.topology component.support component.parents component.children
    anchor component.anchor mode (sourceNormalSkipped tree .Read)
  apply events support schedule.2 schedule.1 tree related (GeneralBorrowAnchor.relation tree anchor) held observer data.1
  · intro event member
    have eventValid : event.node < tree.locationStates.size := by rw [aligned];exact (data.2 event member).1
    obtain ⟨state,present,compatible⟩ := source event.node (confined event member) eventValid
    have compatible' : GeneralBorrowReadCapabilityNormal.ReadCompatible state event.relatedness (tree.protectedNodes.contains event.node) := by
      rw [(data.2 event member).2];exact compatible
    refine ⟨state,present,eventValid,compatible',?_⟩
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
  · exact fun event member => (data.2 event member).2
  · exact localSource
  · exact foreignLocal
  · exact foreignHeld

end DuplicatePrefix.GeneralBorrowObserverReadNormal
