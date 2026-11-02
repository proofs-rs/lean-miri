import duplicate_prefix.S05SemanticReadStage
import duplicate_prefix.S05CutoffOwnershipAuthorization
import duplicate_prefix.GeneralBorrowSnapshotOrderedPrimaryReadPlan
import duplicate_prefix.GeneralBorrowSnapshotVirtualReadAccess
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
import duplicate_prefix.GeneralBorrowSnapshotReadDFSInvariant
import duplicate_prefix.GeneralBorrowSnapshotReadDFSTransferInvariant
namespace DuplicatePrefix.S05SemanticReadSoundness
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
def TrackedInvariant (enabled effectsEnabled : Bool) {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum) (state : LoopState) : Prop :=
  GeneralBorrowSnapshotReadDFSTransferInvariant.Invariant enabled effectsEnabled weights support plan state ∧
  S05LiveSubtreeCacheSoundness.Soundness tree state.1 protections support.contains ∧
  S05SemanticReadStage.Stage tree initial state.1 protections root rootPosition maximum support.contains state.2.2.2.1 ∧
  S05ReadPostorderGraph.Separated tree state.2.2.2.1 ∧
  GeneralBorrowWildcardTaskRegions.Disjoint (source_normal_projection tree initial protections).topology state.2.2.2.1

private theorem expand_disjoint (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (stack : Array Task) (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (disjoint : GeneralBorrowWildcardTaskRegions.Disjoint (source_normal_projection tree initial protections).topology (stack.push (index,false))) :
    GeneralBorrowWildcardTaskRegions.Disjoint (source_normal_projection tree initial protections).topology (expanded stack index node.children) := by
  have valid : index.toNat < (source_normal_projection tree initial protections).topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  have projected := GeneralBorrowProjection.projection_topology_node tree initial protections index.toNat index node rfl present
  simp only [Array.getElem?_eq_getElem valid,Option.getD_some] at projected
  have shape : ((source_normal_projection tree initial protections).topology.nodes[index.toNat]'valid).children = node.children.toList.map UniIndex.toNat := by
    rw [projected]
  exact GeneralBorrowWildcardTaskRegions.expand _ forest stack index node.children valid shape disjoint

private theorem access_plan (enabled effectsEnabled : Bool) (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (runtime : enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree initial protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (budget : effectsEnabled = true → tree.nodes.size < 65536)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (graph : GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree)
    (tagOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (covers : ∀ query,support.contains query → GeneralBorrowExposureCardinality.Covers tree.nodes root query)
    (initialSound : S05LiveSubtreeCacheSoundness.Soundness tree initial protections support.contains)
    (short : tree.nodes.size < 65536) (enabledIsTrue : enabled = true) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (rootPosition != 0)
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    (enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location) ∧
    (effectsEnabled = true → GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum) ∧
    GeneralBorrowSnapshotReadTransfer.Global tree initial result.location protections root rootPosition maximum support.contains ∧
    S05LiveSubtreeCacheSoundness.Soundness tree result.location protections support.contains := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step : ∀ state, TrackedInvariant enabled effectsEnabled weights support plan state →
      (∃ final, scan () state = .done final ∧ TrackedInvariant enabled effectsEnabled weights support plan final ∧
        ((rootPosition != 0) = true ∨ final.2.1 = true)) ∨
      ∃ next, scan () state = .yield next ∧ TrackedInvariant enabled effectsEnabled weights support plan next ∧
        potential weights.weight next.2.2.2.1 < potential weights.weight state.2.2.2.1 := by
    intro state allValid
    obtain ⟨valid,sound,stage,separated,disjoint⟩ := allValid
    rcases state with ⟨location,witness,status,stack,steps⟩
    have statusEq := valid.status
    dsimp only at statusEq
    subst status
    by_cases empty : stack = #[]
    · subst stack
      exact .inl ⟨_,by simp [scan],⟨valid,sound,stage,separated,disjoint⟩,plan.finish witness valid.witness⟩
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
        | none => simp [classified,DuplicatePrefixCallbackAuthorization.Scalar] at authorized
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
            · exact ⟨GeneralBorrowSnapshotReadDFSTransferInvariant.expand weights support plan location witness baseStack index node steps valid present notSkipped,
                sound,S05SemanticReadStage.expand tree initial location protections root rootPosition maximum support.contains graph baseStack index node present stage,
                S05ReadPostorderGraph.expand tree initial protections baseStack index node separated disjoint,
                expand_disjoint tree initial protections forest baseStack index node present disjoint⟩
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
            · exact ⟨GeneralBorrowSnapshotReadDFSTransferInvariant.expand weights support plan location witness baseStack index node steps valid present notSkipped,
                sound,S05SemanticReadStage.expand tree initial location protections root rootPosition maximum support.contains graph baseStack index node present stage,
                S05ReadPostorderGraph.expand tree initial protections baseStack index node separated disjoint,
                expand_disjoint tree initial protections forest baseStack index node present disjoint⟩
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
              · exact ⟨GeneralBorrowSnapshotReadDFSTransferInvariant.pop weights support plan location witness baseStack index node steps valid present skipRaw,
                  sound,S05SemanticReadStage.pop tree initial location protections root rootPosition maximum support.contains depth baseStack index node supported present disjoint sound
                    (by simpa only [classified,DuplicatePrefixCallbackVisitAuthorization.entrySkip] using skipRaw) stage,
                  S05ReadPostorderGraph.pop tree baseStack (index,false) separated,
                  GeneralBorrowWildcardTaskRegions.pop _ baseStack (index,false) disjoint⟩
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
              · exact ⟨GeneralBorrowSnapshotReadDFSTransferInvariant.expand weights support plan location witness baseStack index node steps valid present notSkipped,
                sound,S05SemanticReadStage.expand tree initial location protections root rootPosition maximum support.contains graph baseStack index node present stage,
                S05ReadPostorderGraph.expand tree initial protections baseStack index node separated disjoint,
                expand_disjoint tree initial protections forest baseStack index node present disjoint⟩
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
        have afterSound : S05LiveSubtreeCacheSoundness.Soundness tree after protections support.contains := by
          rcases operations with ⟨classified,same⟩ | ⟨exact,recorded,next,delta,classified,record,access,same⟩
          · subst after
            exact S05SemanticReadSoundnessStep.either_post tree location protections support.contains sound index node present
          · subst after
            cases exact with
            | LocalAccess => exact S05SemanticReadSoundnessStep.local_post tree location protections support.contains sound index node present recorded next delta record access
            | ForeignAccess =>
              have foreign : relation location root index node maximum .Read rootPosition = some .ForeignAccess := classified
              exact S05SemanticReadStage.foreign_sound tree initial location protections root rootPosition maximum support.contains depth valid.frame
                baseStack index node supported present foreign separated disjoint stage sound recorded next delta record access
        have afterStage := S05SemanticReadStage.post tree initial location after protections root rootPosition maximum support.contains depth tagOrder coherent short covers
          valid.frame (afterRuntime enabledIsTrue).1 baseStack index node present operations stage
        have maintained := And.intro
          (GeneralBorrowSnapshotReadDFSTransferInvariant.post weights support plan location after witness baseStack index node steps
            valid present afterSnapshot frame pointwise afterCoherent other afterRuntime afterEffects afterTransfer)
          (And.intro afterSound (And.intro afterStage (And.intro (S05ReadPostorderGraph.pop tree baseStack (index,true) separated)
            (GeneralBorrowWildcardTaskRegions.pop _ baseStack (index,true) disjoint))))
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
      TrackedInvariant enabled effectsEnabled weights support plan state →
      TrackedInvariant enabled effectsEnabled weights support plan (Lean.Loop.forIn (m := Id) {} state scan) ∧
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
    ⟨GeneralBorrowSnapshotReadDFSTransferInvariant.initial weights support plan snapshot coherent runtime,
      initialSound,S05SemanticReadStage.initial tree initial protections root rootPosition maximum support.contains,
      S05ReadPostorderGraph.initial tree root,GeneralBorrowWildcardTaskRegions.initial _ root⟩
  rcases retained.2 with virtual | found
  · simp only [retained.1.1.status,virtual,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨True.intro,retained.1.1.frame,retained.1.1.snapshot,retained.1.1.pointwise,retained.1.1.coherent,retained.1.1.outside,retained.1.1.runtime,retained.1.1.effects,retained.1.1.transfer,retained.1.2.1⟩
  · simp only [retained.1.1.status,found,Bool.not_true,Bool.false_and,Bool.and_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨True.intro,retained.1.1.frame,retained.1.1.snapshot,retained.1.1.pointwise,retained.1.1.coherent,retained.1.1.outside,retained.1.1.runtime,retained.1.1.effects,retained.1.1.transfer,retained.1.2.1⟩


/-- Actual Read preserves the barrier-aware numeric soundness relation. Initial
Read authorization and its witness plan are derived from raw ownership,
cutoff geometry and graph facts; no operation result or target authorization
is supplied. Ordinary-WF coverage of these initial conditions remains open. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree initial protections root position)
    (sound : S05LiveSubtreeCacheSoundness.Soundness tree initial protections rights.area.contains)
    (tagOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (witness : S05CutoffOwnershipGeometry.CutoffWitness tree initial protections root position maximum rights.area.contains)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections (position != 0)
    result.status = .Completed ∧
      S05LiveSubtreeCacheSoundness.Soundness tree result.location protections rights.area.contains ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  have authorization := S05CutoffOwnershipAuthorization.read_authorization tree initial protections root position maximum rights depth tagOrder witness
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root position maximum .Read rights.area.contains authorization coherent short
  have planExists : Nonempty (WitnessPlan tree initial protections root position maximum) := by
    by_cases primary : position = 0
    · subst position
      exact GeneralBorrowSnapshotOrderedPrimaryReadPlan.of_authorization tree initial protections root maximum rights.area.contains tagOrder depth graph coherent short authorization
    · exact ⟨GeneralBorrowSnapshotVirtualReadAccess.plan tree initial protections root position maximum primary⟩
  obtain ⟨plan⟩ := planExists
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have bound := GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root
  obtain ⟨completed,frame,afterSnapshot,pointwise,afterCoherent,outside,runtime,effects,transfer,afterSound⟩ :=
    access_plan true false tree initial protections root position maximum weights bound rights.area snapshot depth coherent plan
      (fun _ => ⟨profile,possible⟩) (fun _ => short) forest graph tagOrder rights.covers sound short rfl
  exact ⟨completed,afterSound,(runtime rfl).1,(runtime rfl).2,afterCoherent⟩

end DuplicatePrefix.S05SemanticReadSoundness
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S05SemanticReadSoundness.access) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
