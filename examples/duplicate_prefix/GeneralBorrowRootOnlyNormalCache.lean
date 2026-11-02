import duplicate_prefix.GeneralBorrowRootOnlyExposureExact
import duplicate_prefix.GeneralBorrowReadNoopCache
namespace DuplicatePrefix.GeneralBorrowRootOnlyNormalCache
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- An exact initial-state transition frame for the actual normal cache loop.
Every exposed visitor has a source no-op permission transition; no successful
access, final permission or cache-validity premise is needed. -/
theorem event_noop_cache (tree : BorrowTree) (location : LocationTree) (anchor : UniIndex) (kind : AccessKind)
    (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (profile : ∀ event ∈ ((source_normal_projection tree location protections).performAccess
        anchor.toNat kind mode).visited, ∀ index node oldState,
      UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → node.isExposed = true →
      tree.locationStateAt location index = some oldState →
      performAccessTransition kind event.relatedness oldState.permission (protections.contains node.tag) =
        .Transition ⟨oldState.permission,oldState.permission⟩) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.exposedCache = location.exposedCache := by
  unfold BorrowTree.performNormalAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_normal_cache_scan
  let property := fun state : LocationTree × Except ExposedCacheError Unit => state.1.exposedCache = location.exposedCache
  have step : ∀ event member state, property state → property (scan event member state).value := by
    intro event member state good
    rcases state with ⟨current,outcome⟩
    dsimp only [property] at good ⊢
    cases outcome with
    | error error => simpa only [scan,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
    | ok value =>
      cases value
      cases converted : UniIndex.ofNat? event.node with
      | none => simpa only [scan,converted,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
      | some index =>
        cases present : tree.nodeAt index with
        | none => simpa only [scan,converted,present,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
        | some node =>
          simp only [scan,converted,present,↓reduceIte]
          split
          · rename_i active
            have exposed : node.isExposed = true := by
              cases flag : node.isExposed with
              | false => simp only [flag,Bool.false_and,Bool.false_eq_true] at active
              | true => rfl
            cases old : tree.locationStateAt location index with
            | none => simpa only [active,↓reduceIte,old,ForInStep.value] using good
            | some oldState =>
              cases next : ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.stateAt event.node with
              | none => simpa only [active,↓reduceIte,old,next,ForInStep.value] using good
              | some newState =>
                have noop := profile event member index node oldState converted present exposed old
                simpa only [active,↓reduceIte,old,next,noop,PermTransition.isNoop,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
          · rename_i inactive
            simpa only [ite_eq_right inactive,ForInStep.value] using good
  have initial : property (source_write_states location
      ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates,.ok ()) :=
    checked_materialized_cache location _
  exact GeneralBorrowLoop.list_invariant' _ scan property step _ initial


/-- Root-only exposure reduces the general Read cache frame to ordinary
Unique ownership; the foreign exposed-node obligations are impossible. -/
theorem root_read (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (protections : ProtectedTags) (mode : ChildrenVisitMode) (rootState : LocationState)
    (only : RootOnly tree root)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) root.toNat .Read)
    (stored : location.perms.get root = some rootState) (unique : rootState.permission = .Unique) :
    (tree.performNormalAccessAt location root .Read protections mode).location.exposedCache = location.exposedCache := by
  apply GeneralBorrowReadNoopCache.selected_unique tree location root protections mode rootState forest owned stored unique
  intro event member index node converted present different exposed
  exact False.elim (different (only index node present exposed))

/-- Read and Write local visits of a Unique root are true source no-ops,
regardless of whether a protector is registered. -/
theorem unique_local_noop (kind : AccessKind) (held : Bool) :
    performAccessTransition kind .LocalAccess .Unique held = .Transition ⟨.Unique,.Unique⟩ := by
  cases kind <;> cases held <;> rfl

/-- A root-only location has a neutral actual Read/Write cache loop whenever
the original root appears as a local visitor. Only initial effective root
permission and event relatedness are premises, never final cache or success. -/
theorem root_local (tree : BorrowTree) (location : LocationTree) (root anchor : UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (only : RootOnly tree root)
    (unique : ∀ node state, tree.nodeAt root = some node →
      tree.locationStateAt location root = some state → state.permission = .Unique)
    (localRoot : ∀ event ∈ ((source_normal_projection tree location protections).performAccess
      anchor.toNat kind mode).visited, event.node = root.toNat → event.relatedness = .LocalAccess) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.exposedCache = location.exposedCache := by
  apply event_noop_cache
  intro event member index node state converted present exposed old
  have same := only index node present exposed
  subst index
  have position : event.node = root.toNat := by
    unfold UniIndex.ofNat? at converted
    split at converted
    · cases converted
      simp only [UniIndex.toNat,UInt32.toNat_ofNat']
      omega
    · cases converted
  rw [unique node state present old,localRoot event member position]
  exact unique_local_noop kind _

/-- Real ownership and forest traversal make every visit to the selected root
local. The event property is derived from the actual visitor, not assumed. -/
theorem selected_event_local (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) root.toNat kind) :
    ∀ event ∈ ((source_normal_projection tree location protections).performAccess root.toNat kind mode).visited,
      event.node = root.toNat → event.relatedness = .LocalAccess := by
  have completed := GeneralBorrowTraversal.normal_access (source_normal_projection tree location protections) forest root.toNat kind mode owned
  have visited := GeneralBorrowStorage.events_visited
    ((source_normal_projection tree location protections).topology.traverse root.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse root.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections) completed
  change ((source_normal_projection tree location protections).performAccess root.toNat kind mode).visited =
    ((source_normal_projection tree location protections).topology.traverse root.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2 at visited
  have rootIn : root.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath root.toNat := by
    have head := sourceAncestorHead (source_normal_projection tree location protections).topology
      (source_normal_projection tree location protections).topology.nodes.size root.toNat
    change ((source_normal_projection tree location protections).topology.ancestorPath root.toNat).head? = some root.toNat at head
    cases path : (source_normal_projection tree location protections).topology.ancestorPath root.toNat with
    | nil => simp only [path,List.head?_nil,reduceCtorEq] at head
    | cons first rest =>
      have same : first = root.toNat := by simpa only [path,List.head?_cons,Option.some.injEq] using head
      simp only [List.mem_cons,same,true_or]
  intro event member same
  have scheduleMember : event ∈ ((source_normal_projection tree location protections).topology.traverse root.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2 := by
    rw [←visited];exact member
  have relation := (GeneralBorrowTraversal.traversal_data (source_normal_projection tree location protections).topology
    forest root.toNat owned.anchorValid mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2 event scheduleMember
  simpa only [same,ite_eq_left rootIn] using relation.2

/-- Both actual normal root Read and Write preserve every cache exactly for
root-only exposed forests with Unique effective root permission. -/
theorem root_access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (only : RootOnly tree root)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) root.toNat kind)
    (unique : ∀ node state, tree.nodeAt root = some node →
      tree.locationStateAt location root = some state → state.permission = .Unique) :
    (tree.performNormalAccessAt location root kind protections mode).location.exposedCache = location.exposedCache := by
  exact root_local tree location root root kind protections mode only unique
    (selected_event_local tree location root kind protections mode forest owned)

end DuplicatePrefix.GeneralBorrowRootOnlyNormalCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyNormalCache." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only normal-cache dependency {dependency}"
