import duplicate_prefix.GeneralBorrowNormalEventCacheFrame
import duplicate_prefix.GeneralBorrowNormalLocation
namespace DuplicatePrefix.GeneralBorrowReadNoopCache
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Equal exposure levels use the source early return, even for malformed graphs. -/
theorem same_level (cache : ExposedCache) (nodes : UniValMap TreeNode) (index : UniIndex)
    (level : WildcardAccessLevel) : cache.updateExposure nodes index level level = ⟨cache,.ok ()⟩ := by
  simp [ExposedCache.updateExposure,Id.run,bind,pure]

private theorem frozen_noop (related : AccessRelatedness) (held : Bool) :
    performAccessTransition .Read related .Frozen held = .Transition ⟨.Frozen,.Frozen⟩ := by
  cases related <;> cases held <;> rfl
private theorem unique_noop (held : Bool) :
    performAccessTransition .Read .LocalAccess .Unique held = .Transition ⟨.Unique,.Unique⟩ := by
  cases held <;> rfl

/-- Initial exposed Frozen visitors and initial exposed Unique local visitors
make no permission-strength transition during Read. The actual cache loop
therefore retains its cache on every outcome, without a poststate premise. -/
theorem normal_cache (tree : BorrowTree) (location : LocationTree) (anchor : UniIndex)
    (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (profile : ∀ event ∈ ((source_normal_projection tree location protections).performAccess
        anchor.toNat .Read mode).visited, ∀ index node oldState,
      UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → node.isExposed = true →
      tree.locationStateAt location index = some oldState →
      oldState.permission = .Frozen ∨ (oldState.permission = .Unique ∧ event.relatedness = .LocalAccess)) :
    (tree.performNormalAccessAt location anchor .Read protections mode).location.exposedCache = location.exposedCache := by
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
    | ok unit =>
      cases unit
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
              cases next : ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).tree.stateAt event.node with
              | none => simpa only [active,↓reduceIte,old,next,ForInStep.value] using good
              | some newState =>
                rcases profile event member index node oldState converted present exposed old with frozen | ⟨unique,related⟩
                · simpa only [active,↓reduceIte,old,next,frozen,frozen_noop,PermTransition.isNoop,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
                · simpa only [active,↓reduceIte,old,next,unique,related,unique_noop,PermTransition.isNoop,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte,ForInStep.value] using good
          · rename_i inactive
            simpa only [ite_eq_right inactive,ForInStep.value] using good
  have initial : property (source_write_states location
      ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).tree.locationStates,.ok ()) :=
    checked_materialized_cache location _
  exact GeneralBorrowLoop.list_invariant' _ scan property step _ initial

/-- In a completed-by-ownership normal Read, the selected Unique node is a
local visitor. All other exposed visitors need only have initial stored Frozen
permissions; exposed nodes in other components impose no condition. -/
theorem selected_unique (tree : BorrowTree) (location : LocationTree) (anchor : UniIndex)
    (protections : ProtectedTags) (mode : ChildrenVisitMode) (rootState : LocationState)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat .Read)
    (rootStored : location.perms.get anchor = some rootState) (rootUnique : rootState.permission = .Unique)
    (frozenOthers : ∀ event ∈ ((source_normal_projection tree location protections).performAccess
        anchor.toNat .Read mode).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → index ≠ anchor → node.isExposed = true →
      ∃ state, location.perms.get index = some state ∧ state.permission = .Frozen) :
    (tree.performNormalAccessAt location anchor .Read protections mode).location.exposedCache = location.exposedCache := by
  have completed := GeneralBorrowTraversal.normal_access (source_normal_projection tree location protections) forest anchor.toNat .Read mode owned
  have visited := GeneralBorrowStorage.events_visited
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    .Read (source_normal_projection tree location protections) completed
  change ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited =
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2 at visited
  have anchorIn : anchor.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat := by
    have head := sourceAncestorHead (source_normal_projection tree location protections).topology
      (source_normal_projection tree location protections).topology.nodes.size anchor.toNat
    change ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).head? = some anchor.toNat at head
    cases path : (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat with
    | nil => simp only [path,List.head?_nil,reduceCtorEq] at head
    | cons first rest =>
      have same : first = anchor.toNat := by simpa only [path,List.head?_cons,Option.some.injEq] using head
      simp only [path,List.mem_cons,same,true_or]
  apply normal_cache
  intro event member index node oldState converted present exposed old
  by_cases same : index = anchor
  · subst index
    have oldEq : oldState = rootState := by
      simpa only [BorrowTree.locationStateAt,present,rootStored,Option.getD_some,bind,pure,Option.bind,Option.some.injEq] using old.symm
    have scheduleMember : event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
        (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2 := by
      rw [←visited];exact member
    have relation := (GeneralBorrowTraversal.traversal_data (source_normal_projection tree location protections).topology
      forest anchor.toNat owned.anchorValid mode (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2 event scheduleMember
    have nodeEq : event.node = anchor.toNat := by
      unfold UniIndex.ofNat? at converted
      split at converted
      · cases converted
        simp only [UniIndex.toNat,UInt32.toNat_ofNat']
        omega
      · cases converted
    exact Or.inr ⟨(congrArg LocationState.permission oldEq).trans rootUnique,by simpa only [nodeEq,ite_eq_left anchorIn] using relation.2⟩
  · obtain ⟨state,stored,frozen⟩ := frozenOthers event member index node converted present same exposed
    have oldEq : oldState = state := by
      simpa only [BorrowTree.locationStateAt,present,stored,Option.getD_some,bind,pure,Option.bind,Option.some.injEq] using old.symm
    exact Or.inl ((congrArg LocationState.permission oldEq).trans frozen)

end DuplicatePrefix.GeneralBorrowReadNoopCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowReadNoopCache." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved initial Read cache dependency {dependency}"
