import duplicate_prefix.GeneralBorrowSifaPermissionConsistency
import duplicate_prefix.GeneralBorrowNormalPermissionMetadata
namespace DuplicatePrefix.GeneralBorrowNormalSifaConsistency
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowStorage
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean DuplicatePrefix.GeneralBorrowSifaPermissionConsistency
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Scalar SIFA bounds at every actual optional/lazy normal-tree location. -/
def Profile (tree : NormalTreeState) : Prop :=
  ∀ position state,tree.stateAt position = some state → Consistent state (tree.protectedNodes.contains position)

/-- Actual distinct scheduled event processing preserves every formed scalar
SIFA bound. Initial ownership supplies each real record/access branch; no
operation-success equation is a premise. -/
theorem events (items : List TraversalEvent) (root : Nat) (kind : AccessKind) (tree : NormalTreeState)
    (distinct : (items.map TraversalEvent.node).Nodup) (owned : EventsOwned tree kind items) (initial : Profile tree) :
    (sourceNormalEvents tree root kind items).status = .Completed ∧ Profile (sourceNormalEvents tree root kind items).tree := by
  induction items generalizing tree with
  | nil => exact ⟨rfl,initial⟩
  | cons head rest ih =>
    obtain ⟨old,present,valid,compatible,scheduled⟩ := owned head (by simp)
    obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
      (visit_for_success old kind head.relatedness (tree.protectedNodes.contains head.node) compatible).resolve_left
        (by rw [scheduled_recurse old kind head.relatedness scheduled];decide)
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
    have laterOwned : EventsOwned updated kind rest := by
      intro later member
      obtain ⟨state,found,bounded,compatible,scheduled⟩ := owned later (by simp [member])
      have different : later.node ≠ head.node := by
        intro same;exact nodup.1 (List.mem_map.mpr ⟨later,member,same⟩)
      exact ⟨state,(stateAt_update_other tree head.node later.node next valid different).trans found,
        by simpa only [updated,Array.size_set] using bounded,compatible,scheduled⟩
    rw [step]
    exact ih updated nodup.2 laterOwned nextProfile

/-- The real normal interpreter access preserves the scalar SIFA profile for
arbitrary finite forest/ownership data and either visit mode/access kind. -/
theorem normal (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (kind : AccessKind) (mode : ChildrenVisitMode)
    (owned : GeneralBorrowAnchor.AnchorOwned tree anchor kind) (initial : Profile tree) :
    (tree.performAccess anchor kind mode).status = .Completed ∧ Profile (tree.performAccess anchor kind mode).tree := by
  have schedule := GeneralBorrowTraversal.traversal_data tree.topology forest anchor owned.anchorValid mode (sourceNormalSkipped tree kind)
  have pointwise := GeneralBorrowNormalPermissionMetadata.schedule_owned tree forest anchor kind mode owned
  exact events (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2
    (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).1 kind tree schedule.1 pointwise initial

end DuplicatePrefix.GeneralBorrowNormalSifaConsistency
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowNormalSifaConsistency.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved normal SIFA consistency dependency {dependency}"
