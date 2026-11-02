import duplicate_prefix.GeneralBorrowNormalExposureTodo
import duplicate_prefix.GeneralBorrowNormalPermissionMetadata
import duplicate_prefix.GeneralBorrowNormalEventCacheFrame
namespace DuplicatePrefix.GeneralBorrowNormalExposureCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposureLevelUpdate
open DuplicatePrefix.GeneralBorrowNormalExposureTodo DuplicatePrefix.GeneralBorrowNormalPermissionMetadataData
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab Term in
elab "source_failure_node" : term => do
  let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.failingNode?" then some name else none
  match found with
  | [name] => return mkConst name
  | _ => throwError "expected pinned normal-access failure-node function"

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

/-- Source cache-loop preservation, consuming raw source visitor metadata.
The independent permission proof supplies metadata/unique/unvisited; normal
completion is derived here from initial Forest and AnchorOwned. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (depth : ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (coherent : LocationCoherent tree location protections)
    (unique : (((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited.map TraversalEvent.node).Nodup)
    (metadata : ∀ event ∈ ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited,
      Nonempty (EventMetadata tree location protections anchor kind mode event))
    (unvisited : ∀ index node,tree.nodeAt index = some node → index.toNat ∉
      ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited.map TraversalEvent.node →
      effective (tree.performNormalAccessAt location anchor kind protections mode).location protections index node = effective location protections index node) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () ∧
    LocationCoherent tree (tree.performNormalAccessAt location anchor kind protections mode).location protections := by
  have completed := GeneralBorrowTraversal.normal_access _ forest anchor.toNat kind mode owned
  let after := (tree.performNormalAccessAt location anchor kind protections mode).location
  let events := ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited
  have core : (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () ∧
      Coherent (tree.performNormalAccessAt location anchor kind protections mode).location.exposedCache tree.nodes
        (levels [] location after protections) := by
    unfold BorrowTree.performNormalAccessAt
    simp only [Id.run,bind,pure,ForIn.forIn]
    name_normal_cache_scan
    have go : ∀ todo (included : ∀ event ∈ todo,event ∈ events) (current : LocationTree),
        (todo.map TraversalEvent.node).Nodup → Coherent current.exposedCache tree.nodes (levels todo location after protections) →
        let result := forIn' todo (current,.ok ()) (fun event member => scan event (included event member))
        result.2 = .ok () ∧ Coherent result.1.exposedCache tree.nodes (levels [] location after protections) := by
      intro todo
      induction todo with
      | nil =>
        intro included current distinct good
        simp only [List.forIn'_nil,pure]
        exact ⟨trivial,good⟩
      | cons event rest ih =>
        intro included current distinct good
        obtain ⟨facts⟩ := metadata event (included event (by simp))
        have oldLevel := (head_old tree location after protections event rest facts.index facts.node facts.converted).trans
          (old_effective tree location protections facts.index facts.node facts.oldState facts.present facts.oldPresent)
        let level := facts.newState.permission.strongestAllowedLocalAccess (protections.contains facts.node.tag)
        let changed := GeneralBorrowExposureLevelTransition.operation current.exposedCache tree.nodes
          (levels (event::rest) location after protections) facts.index facts.node level
        let next := {current with exposedCache := changed.cache}
        have preserved := GeneralBorrowExposureLevelTransition.preserves current.exposedCache tree.nodes depth
          (levels (event::rest) location after protections) good facts.index facts.node facts.present level
        have nextGood : Coherent next.exposedCache tree.nodes (levels rest location after protections) := by
          apply coherent_congr _ _ _ _ preserved.2
          intro query node present
          exact advance tree location after protections event rest distinct facts.index facts.node facts.converted facts.present level
            facts.newEffective.symm query node present
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
              have equal := facts.noopLevel noop
              simp only [Bool.not_true,Bool.false_eq_true,ite_false]
              dsimp only [next,changed,GeneralBorrowExposureLevelTransition.operation]
              simp [exposed,oldLevel,equal,level,same_level]
            | false =>
              have succeeded := update_exposure_succeeds current.exposedCache tree.nodes depth facts.index facts.node facts.present
                (facts.oldState.permission.strongestAllowedLocalAccess (protections.contains facts.node.tag)) level
              simp only [Bool.not_false,ite_true]
              erw [succeeded]
              dsimp only [next,changed,GeneralBorrowExposureLevelTransition.operation]
              simp only [exposed,↓reduceIte,oldLevel]
              rfl
        rw [List.forIn'_cons,actual]
        simp only [bind]
        exact ih (fun other member => included other (by simp [member])) next (List.nodup_cons.mp distinct).2 nextGood
    let initialLocation := source_write_states location
      ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates
    have initialCache : initialLocation.exposedCache = location.exposedCache := checked_materialized_cache location _
    have initialGood : Coherent initialLocation.exposedCache tree.nodes (levels events location after protections) := by
      rw [initialCache]
      exact GeneralBorrowNormalExposureTodo.initial tree location after protections events coherent unvisited
    exact go events (fun _ member => member) initialLocation unique initialGood
  have emptyLevels : levels [] location after protections = effective after protections := by
    funext index node
    simp only [levels,List.map_nil,List.not_mem_nil,↓reduceIte]
  exact ⟨completed,core.1,by
    change Coherent _ tree.nodes (effective after protections)
    rw [←emptyLevels]
    exact core.2⟩
/-- Arbitrary normal forest access preserves the exposed-support cardinality
invariant. Visitor metadata, distinctness, completion and unvisited permission
frames all follow from the initial graph and anchor ownership. No successful
access or cache-update result is assumed. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (coherent : LocationCoherent tree location protections) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () ∧
    LocationCoherent tree (tree.performNormalAccessAt location anchor kind protections mode).location protections := by
  have metadata := GeneralBorrowNormalPermissionMetadata.metadata tree location protections anchor kind mode
    forest owned depth children anchorNode anchorPresent
  exact normal tree location protections anchor kind mode depth forest owned coherent metadata.1 metadata.2
    (GeneralBorrowNormalPermissionMetadata.unvisited tree location protections anchor kind mode forest owned)

end DuplicatePrefix.GeneralBorrowNormalExposureCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowNormalExposureCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generic normal cache dependency {dependency}"
