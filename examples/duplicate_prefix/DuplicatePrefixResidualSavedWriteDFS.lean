import duplicate_prefix.DuplicatePrefixResidualSavedWriteDFSInvariant
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
namespace DuplicatePrefix.DuplicatePrefixResidualSavedWriteDFS
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardSubtreeState (or_insert_snd write)
open GeneralBorrowExposedNonleafState (ReadFrame updated updated_other)
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open DuplicatePrefixResidualSavedWriteDFSInvariant GeneralBorrowProjection
open DuplicatePrefixResidualWriteWitnessPlan
open DuplicatePrefixResidualWriteDFSInvariant (seen)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The actual general Write DFS completes from the raw query-pair contract
and graph witness bookkeeping. Saved entry masks and exact untouched-frontier
storage handle arbitrary nested legal removals without a skip-persistence law.
No source operation-success certificate is a caller premise. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (rootPosition != 0)
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections maximum .Write removed ∧
      Matches tree initial result.location protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step : ∀ state, Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan state →
      (∃ final, scan () state = .done final ∧ Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan final ∧
        ((rootPosition != 0) = true ∨ final.2.1 = true)) ∨
      ∃ next, scan () state = .yield next ∧ Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan next ∧
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
          (classified : relation location root index node maximum .Write rootPosition = some related) :
          location.exposedCache.accessRelatedness root index .Write (rootPosition != 0)
            (aboveMaximum node maximum) = some related := by
        exact (relation_source location root index node maximum .Write rootPosition).symm.trans classified
      cases afterChildren with
      | false =>
        obtain ⟨removed,legal,matching,pending⟩ := valid.model
        have querySome : ∃ related, relation location root index node maximum .Write rootPosition = some related := by
          have unvisited := DuplicatePrefixResidualSavedWriteDFSInvariant.top_unvisited weights support plan location witness baseStack index node false steps valid present
          have retained := DuplicatePrefixResidualWriteQueries.unvisited_not_removed tree initial location protections maximum removed legal matching index node present unvisited
          have pair := authorization.queries removed removed legal legal (by intro query member;exact member) index node supported present retained
          have scalar := (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ _ _ _).mp pair
          rw [DuplicatePrefixResidualCountModel.relation_matches tree initial location protections .Write removed matching valid.coherent short root index node maximum rootPosition]
          cases queryEq : residualRelation tree initial protections root index node maximum .Write rootPosition removed with
          | none => simp [queryEq,DuplicatePrefixCallbackAuthorization.Scalar] at scalar
          | some related => exact ⟨related,rfl⟩
        cases classified : relation location root index node maximum .Write rootPosition with
        | none =>
          obtain ⟨related,impossible⟩ := querySome
          rw [classified] at impossible
          cases impossible
        | some related =>
          have exactRel := sourceRelated related classified
          unfold aboveMaximum at exactRel
          cases related with
          | LocalAccess =>
            have notSkipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
                (relation location root index node maximum .Write rootPosition) = false := by
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
            · exact DuplicatePrefixResidualSavedWriteDFSInvariant.expand weights support plan authorization coherent short forest location witness baseStack index node steps valid present notSkipped
            · rw [expanded_potential,potential_push]
              simp only [cost,Bool.false_eq_true,↓reduceIte]
              have bounded := weights.children index node present
              omega
          | EitherAccess =>
            have notSkipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
                (relation location root index node maximum .Write rootPosition) = false := by
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
            · exact DuplicatePrefixResidualSavedWriteDFSInvariant.expand weights support plan authorization coherent short forest location witness baseStack index node steps valid present notSkipped
            · rw [expanded_potential,potential_push]
              simp only [cost,Bool.false_eq_true,↓reduceIte]
              have bounded := weights.children index node present
              omega
          | ForeignAccess =>
            cases skipped : (effective location index node).skipIfKnownNoop .Write .ForeignAccess with
            | SkipSelfAndChildren =>
              have skipRaw : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
                  (relation location root index node maximum .Write rootPosition) = true := by
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
              · exact DuplicatePrefixResidualSavedWriteDFSInvariant.pop weights support plan location witness baseStack index node steps valid present skipRaw
              · rw [potential_push]
                simp only [cost,Bool.false_eq_true,↓reduceIte]
                have bounded := weights.children index node present
                omega
            | Recurse =>
              have notSkipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Write
                  (relation location root index node maximum .Write rootPosition) = false := by
                rw [classified]
                change skip (effective location index node) .Write .ForeignAccess = false
                cases h : skip (effective location index node) .Write .ForeignAccess
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
              · exact DuplicatePrefixResidualSavedWriteDFSInvariant.expand weights support plan authorization coherent short forest location witness baseStack index node steps valid present notSkipped
              · rw [expanded_potential,potential_push]
                simp only [cost,Bool.false_eq_true,↓reduceIte]
                have bounded := weights.children index node present
                omega
      | true =>
        have unvisited := DuplicatePrefixResidualSavedWriteDFSInvariant.top_unvisited weights support plan location witness baseStack index node true steps valid present
        obtain ⟨removed,legal,matching,pending⟩ := valid.model
        obtain ⟨before,legalBefore,subset,active⟩ := pending index node (by simp) present
        obtain ⟨after,afterRemoved,operations,afterLegal,afterMatches,afterCoherent,other⟩ :=
          DuplicatePrefixResidualSavedWritePost.post tree initial location protections root index node maximum rootPosition support.contains
            authorization before removed legalBefore subset legal matching coherent valid.coherent short depth supported present unvisited active
        have monotone := DuplicatePrefixResidualSavedWritePost.action_mono tree location protections root index node maximum rootPosition removed after afterRemoved operations
        have maintained := DuplicatePrefixResidualSavedWriteDFSInvariant.post weights support plan location after witness baseStack index node steps
          valid present removed afterRemoved pending monotone afterLegal afterMatches afterCoherent other
        rcases operations with ⟨classified,materializedEq,_⟩ | ⟨exact,recorded,next,delta,classified,record,access,updatedEq,_⟩
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
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write <;> simp_all [effective]
            all_goals try
              have no : ¬ node.tag.value ≤ _ := UInt64.not_le.mpr (by assumption)
              simp_all only [no,decide_false,Bool.false_or]
          · rw [potential_push]
            simp [cost]
        · subst after
          have postRecurse : (effective location index node).skipIfKnownNoop .Write exact = .Recurse := by
            cases skipped : (effective location index node).skipIfKnownNoop .Write exact with
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
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write <;> simp_all [effective]
            all_goals try
              have no : ¬ node.tag.value ≤ _ := UInt64.not_le.mpr (by assumption)
              simp_all only [no,decide_false,Bool.false_or]
            all_goals try split <;> simp_all [Bool.and_eq_false_iff]
          · rw [potential_push]
            simp [cost]
  have run : ∀ bound (state : LoopState), potential weights.weight state.2.2.2.1 = bound →
      Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan state →
      Invariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan
        (Lean.Loop.forIn (m := Id) {} state scan) ∧
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
    (DuplicatePrefixResidualSavedWriteDFSInvariant.initial weights support plan coherent)
  have finalModel : ∃ removed, Removal tree initial protections maximum .Write removed ∧
      Matches tree initial (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1 protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1 protections ∧
      (∀ query, ¬support.contains query → (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1.perms.get query = initial.perms.get query) := by
    obtain ⟨removed,legal,matching,_⟩ := retained.1.model
    exact ⟨removed,legal,matching,retained.1.coherent,retained.1.outside⟩
  rcases retained.2 with virtual | found
  · simp only [retained.1.status,virtual,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨True.intro,finalModel⟩
  · simp only [retained.1.status,found,Bool.not_true,Bool.false_and,Bool.and_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨True.intro,finalModel⟩
end DuplicatePrefix.DuplicatePrefixResidualSavedWriteDFS
