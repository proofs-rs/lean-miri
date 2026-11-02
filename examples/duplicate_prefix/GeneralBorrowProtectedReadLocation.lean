import duplicate_prefix.GeneralBorrowProtectedReadCompatible
import duplicate_prefix.GeneralBorrowNormalLocation
namespace DuplicatePrefix.GeneralBorrowProtectedReadLocation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowNormalLocation
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem cache_succeeds (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (initial : ∀ index,index < (source_normal_projection tree location protections).topology.nodes.size → ∃ state,
      (source_normal_projection tree location protections).stateAt index = some state ∧
      GeneralBorrowProtectedReadCompatible.Compatible state
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index))
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) :
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () := by
  let projection := source_normal_projection tree location protections
  let normal := projection.performAccess anchor.toNat .Read mode
  let schedule := projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection .Read)
  have completed : normal.status = .Completed := GeneralBorrowProtectedReadCompatible.normal projection forest anchor.toNat valid mode
    (by dsimp only [projection];unfold_general_projection;unfold_general_topology;simp only [Array.size_mapIdx,Array.size_map]) initial
  have visited : normal.visited = schedule.2 := GeneralBorrowStorage.events_visited schedule.2 schedule.1 .Read projection completed
  have aligned : projection.defaultStates.size = projection.locationStates.size := by
    have sizes := projection_sizes tree location protections
    exact sizes.2.trans sizes.1.symm
  have metadata : ∀ event ∈ normal.visited, ∃ index node oldState newState,
      UniIndex.ofNat? event.node = some index ∧ tree.nodeAt index = some node ∧
      tree.locationStateAt location index = some oldState ∧ normal.tree.stateAt event.node = some newState := by
    intro event member
    rw [visited] at member
    obtain ⟨index,node,converted,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location protections
      depth children anchor anchorNode anchorPresent .Read mode event member
    obtain ⟨indexValid,_⟩ := array_of_node tree index node present
    have eventValid : event.node < projection.locationStates.size := by
      have sizes := projection_sizes tree location protections
      dsimp only [projection]
      rw [sizes.1]
      omega
    obtain ⟨newState,newPresent⟩ := GeneralBorrowStorage.events_total schedule.2 schedule.1 .Read projection aligned event.node eventValid
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
    · cases transition : performAccessTransition .Read event.relatedness oldState.permission (protections.contains node.tag) with
      | UndefinedBehavior => rfl
      | ImpossibleProtectedReservedIM => rfl
      | Transition change =>
        cases noop : change.isNoop <;> simp [noop,ForInStep.value,cacheOK]
    · rfl
  exact GeneralBorrowLoop.list_invariant' _ scan (fun state => state.2 = (.ok () : Except ExposedCacheError Unit)) step _ rfl
theorem normal_succeeds (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (initial : ∀ index,index < (source_normal_projection tree location protections).topology.nodes.size → ∃ state,
      (source_normal_projection tree location protections).stateAt index = some state ∧
      GeneralBorrowProtectedReadCompatible.Compatible state
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index))
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) :
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () := by
  constructor
  · exact GeneralBorrowProtectedReadCompatible.normal _ forest anchor.toNat valid mode
      (by unfold_general_projection;unfold_general_topology;simp only [Array.size_mapIdx,Array.size_map]) initial
  · exact cache_succeeds tree location protections anchor mode forest valid initial depth children anchorNode anchorPresent

/-- Full physical normal-access writeback of the earlier reservation conflict. -/
theorem root_conflict (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root earlier : UniIndex) (rootNode earlierNode : TreeNode) (state : LocationState)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (rootPresent : tree.nodeAt root = some rootNode) (parentless : rootNode.parent = none)
    (earlierPresent : tree.nodeAt earlier = some earlierNode) (listed : earlier ∈ rootNode.children)
    (oldPresent : tree.locationStateAt location earlier = some state) (reservation : state.permission = .ReservedFrz false)
    (held : protections.contains earlierNode.tag = true)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (compatible : ∀ index,index < (source_normal_projection tree location protections).topology.nodes.size → ∃ state,
      (source_normal_projection tree location protections).stateAt index = some state ∧
      GeneralBorrowProtectedReadCompatible.Compatible state
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) root.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index))
    (initial : GeneralBorrowLocationSifaConsistency.Profile tree location protections) :
    (tree.performNormalAccessAt location root .Read protections .VisitChildrenOfAccessed).access.status = .Completed ∧
    (tree.performNormalAccessAt location root .Read protections .VisitChildrenOfAccessed).outcome = .ok () ∧
    ∃ next,(tree.performNormalAccessAt location root .Read protections .VisitChildrenOfAccessed).location.perms.get earlier = some next ∧
      next.permission = .ReservedFrz true := by
  let normal := source_normal_projection tree location protections
  have rootValid : root.toNat < normal.topology.nodes.size := by
    obtain ⟨valid,_⟩ := array_of_node tree root rootNode rootPresent
    dsimp only [normal]
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_mapIdx,Array.size_map] using valid
  have rootShape : normal.topology.nodes[root.toNat] =
      ⟨rootNode.parent.map UniIndex.toNat,rootNode.children.toList.map UniIndex.toNat⟩ := by
    have shape := projection_topology_node tree location protections root.toNat root rootNode rfl rootPresent
    change normal.topology.nodes[root.toNat]?.getD _ = _ at shape
    simpa only [Array.getElem?_eq_getElem rootValid,Option.getD_some] using shape
  have noParent : normal.topology.nodes[root.toNat].parent = none := by
    rw [rootShape,parentless];rfl
  have childMember : earlier.toNat ∈ normal.topology.nodes[root.toNat].children := by
    rw [rootShape]
    exact List.mem_map.mpr ⟨earlier,Array.mem_def.mp listed,rfl⟩
  have rawState : normal.stateAt earlier.toNat = some state := by
    rw [projection_location_state tree location protections earlier earlierNode earlierPresent]
    exact oldPresent
  have protection : normal.protectedNodes.contains earlier.toNat = true :=
    (GeneralBorrowNormalPermissionMetadata.held tree location protections earlier earlierNode earlierPresent).trans held
  have consistent := GeneralBorrowLocationSifaConsistency.projection tree location protections fits initial earlier.toNat state rawState
  rw [protection] at consistent
  have conflict := GeneralBorrowProtectedReadCompatible.root_conflict normal forest root.toNat earlier.toNat rootValid
    noParent childMember (by dsimp only [normal];unfold_general_projection;unfold_general_topology;simp only [Array.size_mapIdx,Array.size_map])
    compatible state rawState protection reservation consistent
  have complete := normal_succeeds tree location protections root .VisitChildrenOfAccessed forest rootValid compatible
    depth children rootNode rootPresent
  obtain ⟨next,stored,permission⟩ := conflict.2
  have written := GeneralBorrowNormalStoredWriteback.stored tree location protections root earlier .Read
    .VisitChildrenOfAccessed next stored
  exact ⟨complete.1,complete.2,next,written,permission⟩

end DuplicatePrefix.GeneralBorrowProtectedReadLocation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadLocation.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read location dependency {dependency}"
