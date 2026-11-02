import duplicate_prefix.GeneralBorrowProtectedReadExposureCache
namespace DuplicatePrefix.GeneralBorrowProtectedVirtualReadCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposureLevelUpdate
open DuplicatePrefix.GeneralBorrowNormalExposureTodo DuplicatePrefix.GeneralBorrowNormalPermissionMetadataData
open DuplicatePrefix.GeneralBorrowEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem completed_failure : source_failure_node .Completed = none := rfl

private theorem old_effective (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (state : LocationState)
    (present : tree.nodeAt index = some node) (oldPresent : tree.locationStateAt location index = some state) :
    effective location protections index node = state.permission.strongestAllowedLocalAccess (protections.contains node.tag) := by
  have same : (location.perms.get index).getD node.defaultLocationState = state := by
    simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,Option.some.injEq] using oldPresent
  simp only [effective,same]

private theorem same_level (cache : ExposedCache) (nodes : UniValMap TreeNode) (index : UniIndex) (level : WildcardAccessLevel) :
    cache.updateExposure nodes index level level = ⟨cache,.ok ()⟩ := by
  simp only [ExposedCache.updateExposure,beq_self_eq_true,ite_true,Id.run,pure]


/-- Permissions stable under either relatedness of a Read. Already-conflicted
held reservations are included; unconflicted reservations are deliberately absent. -/
def StablePermission (permission : Permission) : Prop :=
  permission = .ReservedFrz true ∨ permission = .Frozen ∨ permission = .Cell

/-- Exposed tags whose actual and virtual held flags differ must already have
Read-stable permissions. This is a physical initial-state condition, not an
access-success, visitor-exclusion or final-coherence premise. -/
def Stable (tree : BorrowTree) (location : LocationTree) (actual virtual : ProtectedTags) : Prop :=
  ∀ index node,tree.nodeAt index = some node → node.isExposed = true →
    actual.contains node.tag ≠ virtual.contains node.tag →
    ∃ state,tree.locationStateAt location index = some state ∧ StablePermission state.permission

private theorem virtual_new (tree : BorrowTree) (location : LocationTree) (actual virtual : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode) (event : TraversalEvent)
    (facts : EventMetadata tree location actual anchor .Read mode event) :
    effective (tree.performNormalAccessAt location anchor .Read actual mode).location virtual facts.index facts.node =
      facts.newState.permission.strongestAllowedLocalAccess (virtual.contains facts.node.tag) := by
  have stored := GeneralBorrowNormalStoredWriteback.stored tree location actual anchor facts.index .Read mode facts.newState facts.finalStored
  simp only [effective,stored,Option.getD_some]

private theorem virtual_noop (tree : BorrowTree) (location : LocationTree) (actual virtual : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode) (event : TraversalEvent)
    (facts : EventMetadata tree location actual anchor .Read mode event) (noop : facts.transition.isNoop = true) :
    facts.oldState.permission.strongestAllowedLocalAccess (virtual.contains facts.node.tag) =
      facts.newState.permission.strongestAllowedLocalAccess (virtual.contains facts.node.tag) := by
  have same : facts.transition.fromPermission = facts.transition.toPermission := by
    simpa only [PermTransition.isNoop,beq_iff_eq] using noop
  rw [←facts.fromPermission,←facts.finalEndpoint,same]

private theorem stable_noop (tree : BorrowTree) (location : LocationTree) (actual virtual : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode) (event : TraversalEvent)
    (facts : EventMetadata tree location actual anchor .Read mode event) (stable : Stable tree location actual virtual)
    (exposed : facts.node.isExposed = true) (different : actual.contains facts.node.tag ≠ virtual.contains facts.node.tag) :
    facts.transition.isNoop = true := by
  obtain ⟨state,present,permission⟩ := stable facts.index facts.node facts.present exposed different
  have old : facts.oldState = state := Option.some.inj (facts.oldPresent.symm.trans present)
  have expected : performAccessTransition .Read event.relatedness facts.oldState.permission (actual.contains facts.node.tag) =
      .Transition ⟨facts.oldState.permission,facts.oldState.permission⟩ := by
    rw [old]
    rcases permission with reserved | frozen | cell
    · rw [reserved];cases event.relatedness <;> cases actual.contains facts.node.tag <;> rfl
    · rw [frozen];cases event.relatedness <;> cases actual.contains facts.node.tag <;> rfl
    · rw [cell];cases event.relatedness <;> cases actual.contains facts.node.tag <;> rfl
  have same := PermTransitionOutcome.Transition.inj (facts.performed.symm.trans expected)
  simp only [same,PermTransition.isNoop,beq_self_eq_true]

private theorem virtual_unvisited (tree : BorrowTree) (location : LocationTree) (actual virtual : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location actual).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location actual))
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (outside : index.toNat ∉ ((source_normal_projection tree location actual).performAccess anchor.toNat .Read mode).visited.map TraversalEvent.node) :
    effective (tree.performNormalAccessAt location anchor .Read actual mode).location virtual index node =
      effective location virtual index node := by
  let projected := source_normal_projection tree location actual
  let schedule := projected.topology.traverse anchor.toNat mode (sourceNormalSkipped projected .Read)
  have complete := (GeneralBorrowProtectedReadInvariant.normal projected forest anchor.toNat
    (GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location actual anchor anchorNode anchorPresent) mode
    (GeneralBorrowProtectedReadPermissionMetadata.projection_aligned tree location actual) initial).1
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 .Read projected complete
  change (projected.performAccess anchor.toNat .Read mode).visited = schedule.2 at visited
  have excluded : ∀ event ∈ schedule.2,event.node ≠ index.toNat := by
    intro event member same
    exact outside (List.mem_map.mpr ⟨event,by rw [visited];exact member,same⟩)
  have same := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location actual anchor index node .Read mode present excluded
  simp only [effective,same]
private theorem normal (tree : BorrowTree) (location : LocationTree) (protections virtual : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (depth : ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (coherent : LocationCoherent tree location virtual)
    (stable : Stable tree location protections virtual)
    (unique : (((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited.map TraversalEvent.node).Nodup)
    (metadata : ∀ event ∈ ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited,
      Nonempty (EventMetadata tree location protections anchor .Read mode event))
    (unvisited : ∀ index node,tree.nodeAt index = some node → index.toNat ∉
      ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited.map TraversalEvent.node →
      effective (tree.performNormalAccessAt location anchor .Read protections mode).location virtual index node = effective location virtual index node) :
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () ∧
    LocationCoherent tree (tree.performNormalAccessAt location anchor .Read protections mode).location virtual := by
  have completed := (GeneralBorrowProtectedReadInvariant.normal _ forest anchor.toNat valid mode
    (GeneralBorrowProtectedReadPermissionMetadata.projection_aligned tree location protections) initial).1
  let after := (tree.performNormalAccessAt location anchor .Read protections mode).location
  let events := ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited
  have core : (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () ∧
      Coherent (tree.performNormalAccessAt location anchor .Read protections mode).location.exposedCache tree.nodes
        (levels [] location after virtual) := by
    unfold BorrowTree.performNormalAccessAt
    simp only [Id.run,bind,pure,ForIn.forIn]
    name_normal_cache_scan
    have go : ∀ todo (included : ∀ event ∈ todo,event ∈ events) (current : LocationTree),
        (todo.map TraversalEvent.node).Nodup → Coherent current.exposedCache tree.nodes (levels todo location after virtual) →
        let result := forIn' todo (current,.ok ()) (fun event member => scan event (included event member))
        result.2 = .ok () ∧ Coherent result.1.exposedCache tree.nodes (levels [] location after virtual) := by
      intro todo
      induction todo with
      | nil =>
        intro included current distinct good
        simp only [List.forIn'_nil,pure]
        exact ⟨trivial,good⟩
      | cons event rest ih =>
        intro included current distinct good
        obtain ⟨facts⟩ := metadata event (included event (by simp))
        have oldLevel := (head_old tree location after virtual event rest facts.index facts.node facts.converted).trans
          (old_effective tree location virtual facts.index facts.node facts.oldState facts.present facts.oldPresent)
        let level := facts.newState.permission.strongestAllowedLocalAccess (virtual.contains facts.node.tag)
        let changed := GeneralBorrowExposureLevelTransition.operation current.exposedCache tree.nodes
          (levels (event::rest) location after virtual) facts.index facts.node level
        let next := {current with exposedCache := changed.cache}
        have preserved := GeneralBorrowExposureLevelTransition.preserves current.exposedCache tree.nodes depth
          (levels (event::rest) location after virtual) good facts.index facts.node facts.present level
        have nextGood : Coherent next.exposedCache tree.nodes (levels rest location after virtual) := by
          apply coherent_congr _ _ _ _ preserved.2
          intro query node present
          exact advance tree location after virtual event rest distinct facts.index facts.node facts.converted facts.present level
            (virtual_new tree location protections virtual anchor mode event facts).symm query node present
        have actual : scan event (included event (by simp)) (current,.ok ()) = .yield (next,.ok ()) := by
          simp only [scan,facts.converted,facts.present,completed,facts.oldPresent,facts.newPresent,facts.performed,completed_failure]
          cases exposed : facts.node.isExposed with
          | false =>
            simp only [Bool.false_and,Bool.false_eq_true,↓reduceIte]
            simp only [next,changed,GeneralBorrowExposureLevelTransition.operation,exposed,Bool.false_eq_true,↓reduceIte]
          | true =>
            simp only [Bool.true_and]
            cases noop : facts.transition.isNoop with
            | true =>
              have equal := virtual_noop tree location protections virtual anchor mode event facts noop
              simp only [Bool.not_true,Bool.false_eq_true,ite_false]
              dsimp only [next,changed,GeneralBorrowExposureLevelTransition.operation]
              simp [exposed,oldLevel,equal,level,same_level]
            | false =>
              have flags : protections.contains facts.node.tag = virtual.contains facts.node.tag := by
                by_cases equal : protections.contains facts.node.tag = virtual.contains facts.node.tag
                · exact equal
                · have same := stable_noop tree location protections virtual anchor mode event facts stable exposed equal
                  rw [noop] at same
                  cases same
              simp only [flags]
              have succeeded := update_exposure_succeeds current.exposedCache tree.nodes depth facts.index facts.node facts.present
                (facts.oldState.permission.strongestAllowedLocalAccess (virtual.contains facts.node.tag)) level
              simp only [Bool.not_false,ite_true]
              erw [succeeded]
              dsimp only [next,changed,GeneralBorrowExposureLevelTransition.operation]
              simp only [exposed,↓reduceIte,oldLevel]
              rfl
        rw [List.forIn'_cons,actual]
        simp only [bind]
        exact ih (fun other member => included other (by simp [member])) next (List.nodup_cons.mp distinct).2 nextGood
    let initialLocation := source_write_states location
      ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).tree.locationStates
    have initialCache : initialLocation.exposedCache = location.exposedCache := checked_materialized_cache location _
    have initialGood : Coherent initialLocation.exposedCache tree.nodes (levels events location after virtual) := by
      rw [initialCache]
      exact GeneralBorrowNormalExposureTodo.initial tree location after virtual events coherent unvisited
    exact go events (fun _ member => member) initialLocation unique initialGood
  have emptyLevels : levels [] location after virtual = effective after virtual := by
    funext index node
    simp only [levels,List.map_nil,List.not_mem_nil,↓reduceIte]
  exact ⟨completed,core.1,by
    change Coherent _ tree.nodes (effective after virtual)
    rw [←emptyLevels]
    exact core.2⟩

/-- The actual normal Read uses the full actual table but preserves coherent
counts under a virtual table with previously released tags removed. Every
actual event, transition endpoint and completion is derived from initial data.
Difference-tag Read stability is essential: a held unconflicted reservation
would change its source level and is not admitted by this theorem. -/
theorem access (tree : BorrowTree) (location : LocationTree) (actual virtual : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location actual).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location actual))
    (coherent : LocationCoherent tree location virtual) (stable : Stable tree location actual virtual) :
    (tree.performNormalAccessAt location anchor .Read actual mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read actual mode).outcome = .ok () ∧
    LocationCoherent tree (tree.performNormalAccessAt location anchor .Read actual mode).location virtual := by
  have metadata := GeneralBorrowProtectedReadPermissionMetadata.metadata tree location actual anchor mode forest initial depth children anchorNode anchorPresent
  exact normal tree location actual virtual anchor mode depth forest
    (GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location actual anchor anchorNode anchorPresent)
    initial coherent stable metadata.1 metadata.2
    (virtual_unvisited tree location actual virtual anchor mode forest initial anchorNode anchorPresent)

end DuplicatePrefix.GeneralBorrowProtectedVirtualReadCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedVirtualReadCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected virtual Read cache dependency {dependency}"
