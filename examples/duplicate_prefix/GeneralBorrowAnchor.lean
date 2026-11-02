import duplicate_prefix.GeneralBorrowTopology
namespace DuplicatePrefix.GeneralBorrowAnchor
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
/-- The accessed tag and its ancestors are local; every other node is foreign. -/
def relation (tree : NormalTreeState) (anchor index : Nat) : AccessRelatedness :=
  if index ∈ tree.topology.ancestorPath anchor then .LocalAccess else .ForeignAccess

/-- Data-only ownership of an anchor in an arbitrary normal tree. It permits
arbitrary foreign unprotected permissions and inactive protected foreign
children; active conflicting foreign protectors are ruled out pointwise.
The kind parameter also describes a shared read path with a Frozen anchor. -/
structure AnchorOwned (tree : NormalTreeState) (anchor : Nat) (kind : AccessKind) : Prop where
  anchorValid : anchor < tree.topology.nodes.size
  locationsAligned : tree.locationStates.size = tree.topology.nodes.size
  defaultsAligned : tree.defaultStates.size = tree.topology.nodes.size
  permissions : ∀ index, index < tree.topology.nodes.size →
    ∃ state, tree.stateAt index = some state ∧
      AccessOwned state kind (relation tree anchor index) (tree.protectedNodes.contains index)

/-- Bridge from the anchor invariant and pure visitor-schedule facts to the
actual normal-tree operation. This does not assert that arbitrary Rust caller
histories already satisfy the schedule facts or the ownership invariant. -/
theorem normal_access_of_anchor_schedule (tree : NormalTreeState) (anchor : Nat)
    (kind : AccessKind) (mode : ChildrenVisitMode) (owned : AnchorOwned tree anchor kind)
    (distinct : ((tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2.map
      TraversalEvent.node).Nodup)
    (shape : ∀ event ∈ (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2,
      event.node < tree.topology.nodes.size ∧ event.relatedness = relation tree anchor event.node)
    (caches : ∀ event ∈ (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2,
      ∀ state, tree.stateAt event.node = some state → Scheduled state kind event.relatedness) :
    (tree.performAccess anchor kind mode).status = .Completed := by
  apply normal_access_complete tree anchor kind mode distinct
  intro event member
  have eventShape := shape event member
  obtain ⟨state,present,compatible⟩ := owned.permissions event.node eventShape.1
  refine ⟨state,present,?_,?_,caches event member state present⟩
  · rw [owned.locationsAligned]
    exact eventShape.1
  · rw [eventShape.2]
    exact compatible
/-- Cache scheduling follows from the actual visitor: foreign noop nodes are
pruned before processing. Only structural schedule facts remain as inputs. -/
theorem normal_access_of_anchor (tree : NormalTreeState) (anchor : Nat)
    (kind : AccessKind) (mode : ChildrenVisitMode) (owned : AnchorOwned tree anchor kind)
    (distinct : ((tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2.map
      TraversalEvent.node).Nodup)
    (shape : ∀ event ∈ (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2,
      event.node < tree.topology.nodes.size ∧ event.relatedness = relation tree anchor event.node) :
    (tree.performAccess anchor kind mode).status = .Completed := by
  apply normal_access_of_anchor_schedule tree anchor kind mode owned distinct shape
  intro event member state present
  apply recurse_scheduled
  cases related : event.relatedness with
  | LocalAccess => rfl
  | ForeignAccess =>
    have notSkipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology
      (sourceNormalSkipped tree kind) anchor mode event member related
    have noSkip : state.skipIfKnownNoop kind .ForeignAccess ≠ .SkipSelfAndChildren := by
      intro skipped
      exact notSkipped ((skipped_iff tree kind event.node state present (shape event member).1).mpr skipped)
    cases skip : state.skipIfKnownNoop kind .ForeignAccess with
    | Recurse => rfl
    | SkipSelfAndChildren => exact False.elim (noSkip skip)

end DuplicatePrefix.GeneralBorrowAnchor
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowAnchor." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general anchor dependency {dependency}"
