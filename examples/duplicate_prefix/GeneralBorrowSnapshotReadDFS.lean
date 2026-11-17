import duplicate_prefix.GeneralBorrowSnapshotReadDFSInvariant
import duplicate_prefix.GeneralBorrowSnapshotReadDFSTransferInvariant
namespace DuplicatePrefix.GeneralBorrowSnapshotReadDFS
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardSubtreeState (or_insert_snd write)
open GeneralBorrowExposedNonleafState (ReadFrame updated updated_other)
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
open GeneralBorrowSnapshotReadDFSPlan GeneralBorrowSnapshotReadDFSTransferInvariant
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The private Bool selects which proof facts are carried, and never changes
the interpreter or visitor arguments. The false projection preserves the raw
legacy API; the true projection additionally transports runtime invariants.
Actual general Read DFS. The plan is internal witness bookkeeping; virtual
roots instantiate it with True and physical roots use a real supporting path.
Raw Snapshot replaces the older zero/nonzero permission profile. -/
private theorem access_plan_optional_transfer (enabled effectsEnabled : Bool) (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (runtime : enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree initial protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (budget : effectsEnabled = true → tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    (enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location) ∧
    (effectsEnabled = true → GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum) ∧
    GeneralBorrowSnapshotReadTransfer.Global tree initial result.location protections root rootPosition maximum support.contains := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step : ∀ state, Invariant enabled effectsEnabled weights support plan state →
      (∃ final, scan () state = .done final ∧ Invariant enabled effectsEnabled weights support plan final ∧
        ((rootPosition != 0) = true ∨ final.2.1 = true)) ∨
      ∃ next, scan () state = .yield next ∧ Invariant enabled effectsEnabled weights support plan next ∧
        potential weights.weight next.2.2.2.1 < potential weights.weight state.2.2.2.1 := by
    intro state valid
    rcases state with ⟨location,witness,status,stack,steps⟩
    have statusEq := valid.status
    dsimp only at statusEq
    subst status
    by_cases empty : stack = #[]
    · subst stack
      exact .inl ⟨_,by simp [scan],valid,plan.finish witness valid.witness⟩
    · obtain ⟨baseStack,⟨index,afterChildren⟩,rfl⟩ := Array.exists_push_of_ne_empty empty
      have supported := valid.control.known (index,afterChildren) (by simp)
      obtain ⟨node,present⟩ := support.present index supported
      have notPast := GeneralBorrowWildcardControlStack.not_past weights support _ steps valid.control rootBound
      have sourceRelated (related : WildcardAccessRelatedness)
          (classified : relation location root index node maximum .Read rootPosition = some related) :
          location.exposedCache.accessRelatedness root index .Read (rootPosition != 0)
            (aboveMaximum node maximum) = some related := by
        exact (relation_source location root index node maximum .Read rootPosition).symm.trans classified
      cases afterChildren with
      | false =>
        have authorized := valid.snapshot.scalar index node supported present
        cases classified : relation location root index node maximum .Read rootPosition with
        | none => simp [classified,Scalar] at authorized
        | some related =>
          have exactRel := sourceRelated related classified
          unfold aboveMaximum at exactRel
          cases related with
          | LocalAccess =>
            have notSkipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
                (relation location root index node maximum .Read rootPosition) = false := by
              rw [classified]
              rfl
            have pushing := children_loop node.children (baseStack.push (index,true))
            simp only [forIn'_eq_forIn,pure] at pushing
            refine .inr ⟨(location,witness,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
            · simp only [scan]
              unfold_leaf_helpers
              simp [notPast,present,exactRel,effective,Id.run,bind,pure,LocationState.skipIfKnownNoop,AccessRelatedness.isForeign]
              try unfold_leaf_helpers
              simp [exactRel,effective,pushing,expanded]
              all_goals try rw [exactRel]
              all_goals try unfold_leaf_helpers
              all_goals cases maximum <;> simp_all [pushing,expanded,Id.run,bind,pure]
              all_goals try unfold_leaf_helpers
              all_goals try simp_all [pushing,expanded,Id.run,bind,pure]
            · exact GeneralBorrowSnapshotReadDFSTransferInvariant.expand weights support plan location witness baseStack index node steps valid present notSkipped
            · rw [expanded_potential,potential_push]
              simp only [cost,Bool.false_eq_true,↓reduceIte]
              have bounded := weights.children index node present
              omega
          | EitherAccess =>
            have notSkipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
                (relation location root index node maximum .Read rootPosition) = false := by
              rw [classified]
              rfl
            have pushing := children_loop node.children (baseStack.push (index,true))
            simp only [forIn'_eq_forIn,pure] at pushing
            refine .inr ⟨(location,witness,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
            · simp only [scan]
              unfold_leaf_helpers
              simp [notPast,present,exactRel,effective,Id.run,bind,pure]
              try unfold_leaf_helpers
              simp [exactRel,effective,pushing,expanded]
              all_goals try rw [exactRel]
              all_goals try unfold_leaf_helpers
              all_goals cases maximum <;> simp_all [pushing,expanded,Id.run,bind,pure]
              all_goals try unfold_leaf_helpers
              all_goals try simp_all [pushing,expanded,Id.run,bind,pure]
            · exact GeneralBorrowSnapshotReadDFSTransferInvariant.expand weights support plan location witness baseStack index node steps valid present notSkipped
            · rw [expanded_potential,potential_push]
              simp only [cost,Bool.false_eq_true,↓reduceIte]
              have bounded := weights.children index node present
              omega
          | ForeignAccess =>
            cases skipped : (effective location index node).skipIfKnownNoop .Read .ForeignAccess with
            | SkipSelfAndChildren =>
              have skipRaw : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
                  (relation location root index node maximum .Read rootPosition) = true := by
                rw [classified]
                exact (skip_source _ _ _).mpr skipped
              refine .inr ⟨(location,witness,.Completed,baseStack,steps+1),?_,?_,?_⟩
              · simp only [scan]
                unfold_leaf_helpers
                simp [notPast,present,exactRel,skipped,effective,Id.run,bind,pure]
                try unfold_leaf_helpers
                try simp [exactRel,skipped,effective]
                all_goals try rw [exactRel]
                all_goals try unfold_leaf_helpers
                all_goals cases maximum <;> simp_all [skipped,effective,Id.run,bind,pure]
                all_goals try unfold_leaf_helpers
                all_goals try simp_all [skipped,effective,Id.run,bind,pure]
              · exact GeneralBorrowSnapshotReadDFSTransferInvariant.pop weights support plan location witness baseStack index node steps valid present skipRaw
              · rw [potential_push]
                simp only [cost,Bool.false_eq_true,↓reduceIte]
                have bounded := weights.children index node present
                omega
            | Recurse =>
              have notSkipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
                  (relation location root index node maximum .Read rootPosition) = false := by
                rw [classified]
                change skip (effective location index node) .Read .ForeignAccess = false
                cases h : skip (effective location index node) .Read .ForeignAccess
                · rfl
                · have impossible := (skip_source _ _ _).mp h
                  rw [skipped] at impossible
                  cases impossible
              dsimp only [effective] at skipped
              have pushing := children_loop node.children (baseStack.push (index,true))
              simp only [forIn'_eq_forIn,pure] at pushing
              refine .inr ⟨(location,witness,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
              · simp only [scan]
                unfold_leaf_helpers
                simp [notPast,present,exactRel,effective,Id.run,bind,pure,skipped]
                try unfold_leaf_helpers
                simp [exactRel,effective,pushing,expanded,skipped]
                all_goals try rw [exactRel]
                all_goals try unfold_leaf_helpers
                all_goals cases maximum <;> simp_all [pushing,expanded,Id.run,bind,pure,skipped]
                all_goals try unfold_leaf_helpers
                all_goals try simp_all [pushing,expanded,Id.run,bind,pure,skipped]
              · exact GeneralBorrowSnapshotReadDFSTransferInvariant.expand weights support plan location witness baseStack index node steps valid present notSkipped
              · rw [expanded_potential,potential_push]
                simp only [cost,Bool.false_eq_true,↓reduceIte]
                have bounded := weights.children index node present
                omega
      | true =>
        have recurse := valid.pending index node (by simp) present
        obtain ⟨after,operations,afterSnapshot,frame,afterCoherent,other,pointwise,afterRuntime⟩ :=
          GeneralBorrowSnapshotReadDFSRuntimeData.post_optional enabled tree location protections root rootPosition maximum support.contains
            valid.snapshot depth valid.coherent valid.runtime index node supported present recurse
        have afterEffects : effectsEnabled = true → GeneralBorrowSnapshotReadWriteEffects.Effects tree initial after protections maximum := by
          intro active
          exact GeneralBorrowSnapshotReadWriteEffects.post tree initial location after protections root rootPosition maximum support.contains
            (valid.effects active) valid.snapshot depth valid.coherent (budget active) index node supported present recurse operations
        have afterTransfer : GeneralBorrowSnapshotReadTransfer.Global tree initial after protections root rootPosition maximum support.contains := by
          rcases operations with ⟨classified,same⟩ | ⟨exact,recorded,next,delta,classified,record,access,same⟩
          · subst after
            exact GeneralBorrowSnapshotReadTransfer.materialized_global tree initial location protections root rootPosition maximum support.contains valid.transfer index node present
          · subst after
            exact GeneralBorrowSnapshotReadTransfer.updated_global tree initial location protections root rootPosition maximum support.contains
              valid.snapshot valid.frame valid.transfer index node present exact recorded next delta classified recurse record access
        have maintained := GeneralBorrowSnapshotReadDFSTransferInvariant.post weights support plan location after witness baseStack index node steps
          valid present afterSnapshot frame pointwise afterCoherent other afterRuntime afterEffects afterTransfer
        rcases operations with ⟨classified,materializedEq⟩ | ⟨exact,recorded,next,delta,classified,record,access,updatedEq⟩
        · subst after
          have exactRel := sourceRelated .EitherAccess classified
          unfold aboveMaximum at exactRel
          refine .inr ⟨(materialized location index node,seen location index node maximum protections witness,.Completed,baseStack,steps+1),?_,maintained,?_⟩
          · simp only [scan]
            unfold_leaf_helpers
            simp [notPast,present,exactRel,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp [exactRel,materialized,seen,effective]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals cases maximum <;> simp_all [materialized,seen,effective,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [materialized,seen,effective,Id.run,bind,pure]
            all_goals split <;> simp_all [Bool.and_eq_false_iff]
            all_goals cases exposed : node.isExposed <;> simp_all [effective]
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Read <;> simp_all [effective]
            all_goals try
              have no : ¬ node.tag.value ≤ _ := UInt64.not_le.mpr (by assumption)
              simp_all only [no,decide_false,Bool.false_or]
          · rw [potential_push]
            simp [cost]
        · subst after
          have postRecurse : (effective location index node).skipIfKnownNoop .Read exact = .Recurse := by
            cases skipped : (effective location index node).skipIfKnownNoop .Read exact with
            | Recurse => rfl
            | SkipSelfAndChildren =>
                simp [LocationState.recordNewAccess,skipped] at record
          have exactRel := sourceRelated (GeneralBorrowSnapshotReadState.wildcard exact) classified
          unfold aboveMaximum at exactRel
          have cacheOK : ∀ oldLevel newLevel, (location.exposedCache.updateExposure tree.nodes index oldLevel newLevel).outcome = .ok () :=
            fun oldLevel newLevel => GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes depth index node present oldLevel newLevel
          refine .inr ⟨(updated tree location index node protections recorded next delta,
            seen location index node maximum protections witness,.Completed,baseStack,steps+1),?_,maintained,?_⟩
          · cases exact
            all_goals simp only [GeneralBorrowSnapshotReadState.wildcard] at exactRel
            all_goals simp only [scan]
            all_goals unfold_leaf_helpers
            all_goals simp [notPast,present,exactRel,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals simp only [exactRel,or_insert_snd,record,access,LocationState.AccessResult.resultingState,
              postRecurse,reduceCtorEq,and_false,ite_false]
            all_goals simp [updated,write,materialized,seen,effective,cacheOK]
            all_goals try rw [exactRel]
            all_goals try unfold_leaf_helpers
            all_goals cases maximum <;> simp_all [record,access,updated,write,materialized,seen,effective,cacheOK,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [record,access,updated,write,materialized,seen,effective,cacheOK,Id.run,bind,pure]
            all_goals split <;> simp_all [Bool.and_eq_false_iff]
            all_goals cases exposed : node.isExposed <;> simp_all [effective]
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Read <;> simp_all [effective]
            all_goals try
              have no : ¬ node.tag.value ≤ _ := UInt64.not_le.mpr (by assumption)
              simp_all only [no,decide_false,Bool.false_or]
            all_goals try split <;> simp_all [Bool.and_eq_false_iff]
          · rw [potential_push]
            simp [cost]
  have run : ∀ bound (state : LoopState), potential weights.weight state.2.2.2.1 = bound →
      Invariant enabled effectsEnabled weights support plan state →
      Invariant enabled effectsEnabled weights support plan (Lean.Loop.forIn (m := Id) {} state scan) ∧
      ((rootPosition != 0) = true ∨ (Lean.Loop.forIn (m := Id) {} state scan : Id LoopState).2.1 = true) := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro state measured valid
      rw [Lean.Loop.forIn_eq_of_monadTail]
      rcases step state valid with done | more
      · obtain ⟨final,actual,preserved,finished⟩ := done
        simpa only [actual,bind,pure] using And.intro preserved finished
      · obtain ⟨next,actual,preserved,smaller⟩ := more
        simp only [actual,bind]
        exact ih _ (by omega) next rfl preserved
  have retained := run _ (initial,false,.Completed,#[(root,false)],0) rfl
    (GeneralBorrowSnapshotReadDFSTransferInvariant.initial weights support plan snapshot coherent runtime)
  rcases retained.2 with virtual | found
  · simp only [retained.1.status,virtual,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨True.intro,retained.1.frame,retained.1.snapshot,retained.1.pointwise,retained.1.coherent,retained.1.outside,retained.1.runtime,retained.1.effects,retained.1.transfer⟩
  · simp only [retained.1.status,found,Bool.not_true,Bool.false_and,Bool.and_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨True.intro,retained.1.frame,retained.1.snapshot,retained.1.pointwise,retained.1.coherent,retained.1.outside,retained.1.runtime,retained.1.effects,retained.1.transfer⟩

private theorem access_plan_optional_effects (enabled effectsEnabled : Bool) (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (runtime : enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree initial protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (budget : effectsEnabled = true → tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    (enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location) ∧
    (effectsEnabled = true → GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum) := by
  have actual := access_plan_optional_transfer enabled effectsEnabled tree initial protections root rootPosition maximum weights rootBound support snapshot depth coherent plan runtime budget
  exact ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2.1⟩

private theorem access_plan_optional_runtime (enabled : Bool) (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (runtime : enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree initial protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    (enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location) := by
  have actual := access_plan_optional_effects enabled false tree initial protections root rootPosition maximum weights rootBound support snapshot depth coherent plan runtime (by simp)
  exact ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.1,actual.2.2.2.2.2.2.1⟩

theorem access_plan_frame (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) := by
  have actual := access_plan_optional_runtime false tree initial protections root rootPosition maximum weights rootBound support snapshot depth coherent plan (by simp)
  exact ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.1⟩

theorem access_plan_runtime (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) := by
  have actual := access_plan_optional_runtime true tree initial protections root rootPosition maximum weights rootBound support snapshot depth coherent plan (fun _ => ⟨profile,possible⟩)
  have afterRuntime := actual.2.2.2.2.2.2 rfl
  refine ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.1,afterRuntime.1,afterRuntime.2,?_⟩
  intro query missing
  apply actual.2.2.2.2.2.1 query
  intro included
  obtain ⟨node,present⟩ := support.present query included
  rw [present] at missing
  cases missing

theorem access_plan_effects (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum := by
  have actual := access_plan_optional_effects true true tree initial protections root rootPosition maximum weights rootBound support snapshot depth coherent plan (fun _ => ⟨profile,possible⟩) (fun _ => short)
  have afterRuntime := actual.2.2.2.2.2.2.1 rfl
  refine ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.1,afterRuntime.1,afterRuntime.2,?_,actual.2.2.2.2.2.2.2 rfl⟩
  intro query missing
  apply actual.2.2.2.2.2.1 query
  intro included
  obtain ⟨node,present⟩ := support.present query included
  rw [present] at missing
  cases missing

theorem access_plan_transfer (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum ∧
    GeneralBorrowSnapshotReadTransfer.Global tree initial result.location protections root rootPosition maximum support.contains := by
  have actual := access_plan_optional_transfer true true tree initial protections root rootPosition maximum weights rootBound support snapshot depth coherent plan (fun _ => ⟨profile,possible⟩) (fun _ => short)
  have afterRuntime := actual.2.2.2.2.2.2.1 rfl
  refine ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.1,afterRuntime.1,afterRuntime.2,?_,actual.2.2.2.2.2.2.2.1 rfl,actual.2.2.2.2.2.2.2.2⟩
  intro query missing
  apply actual.2.2.2.2.2.1 query
  intro included
  obtain ⟨node,present⟩ := support.present query included
  rw [present] at missing
  cases missing

/-- Legacy completion/Read/coherence API is preserved as a projection of the
stronger actual visitor result with outside-support storage framing. -/
theorem access_plan (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections := by
  have actual := access_plan_frame tree initial protections root rootPosition maximum weights rootBound support snapshot depth coherent plan
  exact ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1⟩

end DuplicatePrefix.GeneralBorrowSnapshotReadDFS
