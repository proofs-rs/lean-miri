import duplicate_prefix.GeneralBorrowNodeUpdate
import duplicate_prefix.GeneralBorrowPresence
import duplicate_prefix.GeneralBorrowNormalLocation
namespace DuplicatePrefix.GeneralBorrowExposedScopedNormal
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowPresence
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A graph-only component certificate: closure in both parent and child
 directions includes the selected anchor's component, with no permission,
 exposure, visitor schedule or successful-operation field. -/
structure Component (tree : TraversalTree) (anchor : Nat) where
  support : Nat → Prop
  anchor : support anchor
  parents : ParentClosed tree support
  children : ChildClosed tree support

def Owned (tree : NormalTreeState) (anchor : Nat) (kind : AccessKind)
    (component : Component tree.topology anchor) : Prop :=
  ∀ index, component.support index → index < tree.topology.nodes.size →
    ∃ state,tree.stateAt index = some state ∧ GeneralBorrowPermissions.AccessOwned state kind
      (GeneralBorrowAnchor.relation tree anchor index) (tree.protectedNodes.contains index)

/-- Raw compatibility is required only inside the graph component. Actual
normal visitors are proved confined to it, including skipped subtrees in either
mode; arbitrary protected/exposed permissions outside it impose no condition. -/
theorem normal (tree : NormalTreeState) (anchor : Nat) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest tree.topology) (valid : anchor < tree.topology.nodes.size)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (component : Component tree.topology anchor) (owned : Owned tree anchor kind component) :
    (tree.performAccess anchor kind mode).status = .Completed := by
  have shape := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree kind)
  have confined := traversal_present tree.topology component.support component.parents component.children anchor component.anchor mode (sourceNormalSkipped tree kind)
  apply normal_access_complete tree anchor kind mode shape.1
  intro event member
  have inside := confined event member
  have facts := shape.2 event member
  obtain ⟨state,present,permission⟩ := owned event.node inside facts.1
  refine ⟨state,present,?_,?_,?_⟩
  · rw [aligned];exact facts.1
  · rw [facts.2];exact permission
  · apply recurse_scheduled
    cases related : event.relatedness with
    | LocalAccess => rfl
    | ForeignAccess =>
      have unskipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology (sourceNormalSkipped tree kind) anchor mode event member related
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
end DuplicatePrefix.GeneralBorrowExposedScopedNormal
