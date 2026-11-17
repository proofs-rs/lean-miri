import duplicate_prefix.GeneralBorrowGraph
import duplicate_prefix.GeneralBorrowStorage
namespace DuplicatePrefix.GeneralBorrowNormalLocation
open Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
elab "name_normal_cache_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``ForIn'.forIn')
      | throwError "no actual List.forIn cache loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← Lean.Meta.inferType body) body
    let (scan,goal) ← goal.intro1P
    let target ← goal.getType
    let target := target.replace fun expr => if expr == body then some (mkFVar scan) else none
    return [← goal.change target]
theorem cache_succeeds (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) :
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () := by
  let projection := source_normal_projection tree location protections
  let normal := projection.performAccess anchor.toNat kind mode
  let schedule := projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)
  have completed : normal.status = .Completed := GeneralBorrowTraversal.normal_access projection forest anchor.toNat kind mode owned
  have visited : normal.visited = schedule.2 := GeneralBorrowStorage.events_visited schedule.2 schedule.1 kind projection completed
  have aligned : projection.defaultStates.size = projection.locationStates.size := by
    have sizes := projection_sizes tree location protections
    exact sizes.2.trans sizes.1.symm
  have metadata : ∀ event ∈ normal.visited, ∃ index node oldState newState,
      UniIndex.ofNat? event.node = some index ∧ tree.nodeAt index = some node ∧
      tree.locationStateAt location index = some oldState ∧ normal.tree.stateAt event.node = some newState := by
    intro event member
    rw [visited] at member
    obtain ⟨index,node,converted,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location protections
      depth children anchor anchorNode anchorPresent kind mode event member
    obtain ⟨indexValid,_⟩ := array_of_node tree index node present
    have eventValid : event.node < projection.locationStates.size := by
      have sizes := projection_sizes tree location protections
      dsimp only [projection]
      rw [sizes.1]
      omega
    obtain ⟨newState,newPresent⟩ := GeneralBorrowStorage.events_total schedule.2 schedule.1 kind projection aligned event.node eventValid
    exact ⟨index,node,(location.perms.get index).getD node.defaultLocationState,newState,converted,present,
      by simp [BorrowTree.locationStateAt,present],newPresent⟩
  unfold BorrowTree.performNormalAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_normal_cache_scan
  have step : ∀ event member state, state.2 = (.ok () : Except ExposedCacheError Unit) →
      (scan event member state).value.2 = .ok () := by
    intro event member state good
    rcases state with ⟨current,outcome⟩
    dsimp only at good
    subst outcome
    obtain ⟨index,node,oldState,newState,converted,present,oldPresent,newPresent⟩ := metadata event member
    have cacheOK : ∀ oldLevel newLevel, (current.exposedCache.updateExposure tree.nodes index oldLevel newLevel).outcome = .ok () :=
      fun oldLevel newLevel => update_exposure_succeeds current.exposedCache tree.nodes depth index node present oldLevel newLevel
    dsimp only [normal,projection] at newPresent
    simp only [scan,converted,present,oldPresent,newPresent,↓reduceIte]
    split
    · cases transition : performAccessTransition kind event.relatedness oldState.permission (protections.contains node.tag) with
      | UndefinedBehavior => rfl
      | ImpossibleProtectedReservedIM => rfl
      | Transition change =>
        cases noop : change.isNoop <;> simp [noop,ForInStep.value,cacheOK]
    · rfl
  exact GeneralBorrowLoop.list_invariant' _ scan (fun state => state.2 = (.ok () : Except ExposedCacheError Unit)) step _ rfl
theorem normal_succeeds (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () := by
  constructor
  · exact GeneralBorrowTraversal.normal_access _ forest anchor.toNat kind mode owned
  · exact cache_succeeds tree location protections anchor kind mode forest owned depth children anchorNode anchorPresent

end DuplicatePrefix.GeneralBorrowNormalLocation

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowNormalLocation." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic normal-location dependency {dependency}"
