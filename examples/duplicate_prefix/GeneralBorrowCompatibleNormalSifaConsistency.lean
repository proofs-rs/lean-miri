import duplicate_prefix.GeneralBorrowCompatibleScopedNormalMetadata
import duplicate_prefix.GeneralBorrowNormalSifaConsistency
namespace DuplicatePrefix.GeneralBorrowCompatibleNormalSifaConsistency
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowEvents GeneralBorrowStorage GeneralBorrowFreshActiveOnClean
open GeneralBorrowSifaPermissionConsistency
open GeneralBorrowNormalSifaConsistency (Profile)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual distinct scheduled event processing preserves every formed scalar
SIFA bound. Initial ownership supplies each real record/access branch; no
operation-success equation is a premise. -/
theorem events (items : List TraversalEvent) (root : Nat) (kind : AccessKind) (tree : NormalTreeState)
    (distinct : (items.map TraversalEvent.node).Nodup) (owned : GeneralBorrowCompatibleEventEndpoints.EventsCompatible tree kind items) (initial : Profile tree) :
    (sourceNormalEvents tree root kind items).status = .Completed ∧ Profile (sourceNormalEvents tree root kind items).tree := by
  induction items generalizing tree with
  | nil => exact ⟨rfl,initial⟩
  | cons head rest ih =>
    obtain ⟨old,present,valid,compatible,scheduled⟩ := owned head (by simp)
    let recorded := {old with idempotentForeignAccess := (
      IdempotentForeignAccess.recordNew old.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness kind head.relatedness))}
    have compatibleRecorded : DuplicatePrefixScalarAuthorization.Compatible recorded kind head.relatedness
        (tree.protectedNodes.contains head.node) := by
      cases kind <;> exact compatible
    have possible : recorded.possible = true := by
      cases kind <;> exact compatible.1
    obtain ⟨next,transition,access⟩ :=
      (DuplicatePrefixScalarAuthorization.compatible_iff recorded kind head.relatedness _ possible).mp compatibleRecorded
    have record : old.recordNewAccess kind head.relatedness = .Recorded recorded := by
      simp only [LocationState.recordNewAccess,scheduled_recurse old kind head.relatedness scheduled,beq_self_eq_true,↓reduceIte]
      rfl
    have consistent := GeneralBorrowSifaPermissionConsistency.pipeline old recorded next transition kind head.relatedness
      (tree.protectedNodes.contains head.node) (initial head.node old present) record access
    let updated := {tree with locationStates := tree.locationStates.set head.node (some next) valid}
    have step : sourceNormalEvents tree root kind (head :: rest) =
        {sourceNormalEvents updated root kind rest with visited := head :: (sourceNormalEvents updated root kind rest).visited} := by
      unfold_normal_events
      simp only [present,record,access,valid,↓reduceDIte]
      rfl
    have nextProfile : Profile updated := by
      intro position state found
      by_cases same : position = head.node
      · subst position
        have actual : updated.stateAt head.node = some next := by
          simp only [updated,NormalTreeState.stateAt,Array.getElem?_set_self]
        have equal : state = next := Option.some.inj (found.symm.trans actual)
        subst state
        exact consistent
      · have previous : tree.stateAt position = some state :=
          (stateAt_update_other tree head.node position next valid same).symm.trans found
        exact initial position state previous
    have nodup := List.nodup_cons.mp distinct
    have laterOwned : GeneralBorrowCompatibleEventEndpoints.EventsCompatible updated kind rest := by
      intro later member
      obtain ⟨state,found,bounded,compatible,scheduled⟩ := owned later (by simp [member])
      have different : later.node ≠ head.node := by
        intro same;exact nodup.1 (List.mem_map.mpr ⟨later,member,same⟩)
      exact ⟨state,(stateAt_update_other tree head.node later.node next valid different).trans found,
        by simpa only [updated,Array.size_set] using bounded,compatible,scheduled⟩
    rw [step]
    exact ih updated nodup.2 laterOwned nextProfile

/-- The actual component-confined normal visitor preserves all scalar SIFA
bounds under exact single-kind compatibility. No Unique/Disabled profile or
successful-operation input is used. Other components need SIFA consistency,
not access ownership. -/
theorem normal (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (kind : AccessKind) (mode : ChildrenVisitMode)
    (valid : anchor < tree.topology.nodes.size)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (component : GeneralBorrowExposedScopedNormal.Component tree.topology anchor)
    (owned : GeneralBorrowCompatibleScopedNormal.Owned tree anchor kind component)
    (initial : Profile tree) :
    (tree.performAccess anchor kind mode).status = .Completed ∧ Profile (tree.performAccess anchor kind mode).tree := by
  have schedule := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree kind)
  have pointwise := GeneralBorrowCompatibleScopedNormalMetadata.schedule_owned tree forest anchor kind mode
    valid aligned component owned
  exact events (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2
    (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).1 kind tree schedule.1 pointwise initial

end DuplicatePrefix.GeneralBorrowCompatibleNormalSifaConsistency
