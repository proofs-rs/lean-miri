import duplicate_prefix.S05CompletedWriteAuthorityRetention
import duplicate_prefix.S05CompletedAncestryWriteAccess
import duplicate_prefix.S05WildcardCompletedWriteQueries

namespace DuplicatePrefix.S05CompletedWriteAuthorityDFS
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualCountModel
open DuplicatePrefixResidualSupportAuthorization (Removal residualRelation)
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other ReadFrame)
open GeneralBorrowSnapshotReadState (wildcard)
open GeneralBorrowExposureCardinality (Covers)
open GeneralBorrowExposedConditionalWritePermissions
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack GeneralBorrowProjection
open GeneralBorrowWildcardSubtreeState (or_insert_snd write)
open DuplicatePrefixResidualSavedWriteDFSInvariant DuplicatePrefixResidualWriteWitnessPlan
open DuplicatePrefixResidualWriteDFSInvariant (seen)
open GeneralBorrowResidualSavedWriteRuntime (RuntimeInvariant)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
-- Inherited elaboration limit; this is not interpreter fuel or a runtime resource guarantee.
set_option maxHeartbeats 8000000

open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open DuplicatePrefixResidualWriteRepaired (Authorization)
private abbrev Action (tree : BorrowTree) (current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (removed : List UniIndex) (after : LocationTree) (afterRemoved : List UniIndex) : Prop :=
  DuplicatePrefixResidualWritePost.Action tree current protections root index node maximum position removed after afterRemoved ∨
  (DuplicatePrefixCallbackVisitAuthorizationRepaired.PostchildrenNoop (effective current index node) .Write
    (protections.contains node.tag) (relation current root index node maximum .Write position) ∧
    after = materialized current index node ∧ afterRemoved = removed)

private theorem action_mono (tree : BorrowTree) (current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (removed : List UniIndex) (after : LocationTree) (afterRemoved : List UniIndex)
    (action : Action tree current protections root index node maximum position removed after afterRemoved) :
    ∀ query ∈ removed, query ∈ afterRemoved := by
  rcases action with old | ⟨_,_,rfl⟩
  · exact DuplicatePrefixResidualSavedWritePost.action_mono tree current protections root index node maximum position removed after afterRemoved old
  · intro query member;exact member

private theorem post_model (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (before removed : List UniIndex)
    (legalBefore : Removal tree initial protections maximum .Write before)
    (subset : ∀ query ∈ before, query ∈ removed)
    (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (currentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (inside : support index) (present : tree.nodes.get index = some node)
    (unvisited : current.perms.get index = initial.perms.get index)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree current protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current)
    (initialActive : DuplicatePrefixCallbackVisitAuthorization.entrySkip
      (effective initial index node) .Write (residualRelation tree initial protections root index node maximum .Write rootPosition before) = false) :
    ∃ after afterRemoved,
      Action tree current protections root index node maximum rootPosition removed after afterRemoved ∧
      Removal tree initial protections maximum .Write afterRemoved ∧
      Matches tree initial after protections .Write afterRemoved ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, query ≠ index → after.perms.get query = current.perms.get query) := by
  have retained := DuplicatePrefixResidualWriteQueries.unvisited_not_removed tree initial current protections maximum removed legal matching index node present unvisited
  have authorized := authorization.queries before removed legalBefore legal subset index node inside present retained
  rw [←unvisited,←relation_matches tree initial current protections .Write removed matching currentCoherent short root index node maximum rootPosition] at authorized
  have noSkip : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective current index node) .Write
      (residualRelation tree initial protections root index node maximum .Write rootPosition before) = false := by
    simpa only [effective,unvisited] using initialActive
  rcases authorized with legacy | repaired
  · have old : ∃ after afterRemoved,
        DuplicatePrefixResidualWritePost.Action tree current protections root index node maximum rootPosition removed after afterRemoved ∧
        Removal tree initial protections maximum .Write afterRemoved ∧
        Matches tree initial after protections .Write afterRemoved ∧
        GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
        (∀ query, query ≠ index → after.perms.get query = current.perms.get query) := by
      have branch := legacy.2.resolve_left (by
        intro yes
        have impossible : (false : Bool) = true := noSkip.symm.trans yes
        cases impossible)
      cases classified : relation current root index node maximum .Write rootPosition with
      | none => simp [classified] at branch
      | some related =>
        cases related with
        | EitherAccess =>
          refine ⟨materialized current index node,removed,.inl ⟨classified,rfl,rfl⟩,legal,?_,
            GeneralBorrowExposedNonleafCoherence.materialized_coherent tree current index node protections present currentCoherent,?_⟩
          · intro query queryNode found exposed
            change GeneralBorrowExposureCardinality.supports
              ((effective (materialized current index node) query queryNode).permission.strongestAllowedLocalAccess (protections.contains queryNode.tag)) .Write = _
            rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
            exact matching query queryNode found exposed
          · intro query different
            unfold materialized UniValMap.orInsert
            split
            · rfl
            · exact GeneralBorrowFreshLocation.get_other _ index query _ different
        | LocalAccess =>
          have raw := branch
          rw [classified] at raw
          have compatible : Compatible (effective current index node) .LocalAccess (protections.contains node.tag) := raw.2
          have scheduled : GeneralBorrowEvents.Scheduled (effective current index node) .Write .LocalAccess := by
            apply GeneralBorrowEvents.recurse_scheduled
            cases skipped : (effective current index node).skipIfKnownNoop .Write .LocalAccess with
            | Recurse => rfl
            | SkipSelfAndChildren =>
              have yes := (skip_source _ _ _).mpr skipped
              have impossible : (false : Bool) = true := raw.1.symm.trans yes
              cases impossible
          obtain ⟨recorded,next,delta,record,access,_,afterLegal,afterMatches,afterCoherent⟩ :=
            DuplicatePrefixResidualWriteStep.step tree initial current protections root index node maximum rootPosition removed
              legal matching currentCoherent short depth present unvisited .LocalAccess .LocalAccess classified rfl compatible scheduled
          refine ⟨updated tree current index node protections recorded next delta,
            DuplicatePrefixResidualWriteStep.removedAfter current protections removed index node next,
            .inr ⟨.LocalAccess,recorded,next,delta,classified,record,access,rfl,rfl⟩,
            afterLegal,afterMatches,afterCoherent,?_⟩
          exact fun query different => updated_other tree current index query node protections recorded next delta different
        | ForeignAccess =>
          have raw := branch
          rw [classified] at raw
          have compatible : Compatible (effective current index node) .ForeignAccess (protections.contains node.tag) := raw.2
          have scheduled : GeneralBorrowEvents.Scheduled (effective current index node) .Write .ForeignAccess := by
            apply GeneralBorrowEvents.recurse_scheduled
            cases skipped : (effective current index node).skipIfKnownNoop .Write .ForeignAccess with
            | Recurse => rfl
            | SkipSelfAndChildren =>
              have yes := (skip_source _ _ _).mpr skipped
              have impossible : (false : Bool) = true := raw.1.symm.trans yes
              cases impossible
          obtain ⟨recorded,next,delta,record,access,_,afterLegal,afterMatches,afterCoherent⟩ :=
            DuplicatePrefixResidualWriteStep.step tree initial current protections root index node maximum rootPosition removed
              legal matching currentCoherent short depth present unvisited .ForeignAccess .ForeignAccess classified rfl compatible scheduled
          refine ⟨updated tree current index node protections recorded next delta,
            DuplicatePrefixResidualWriteStep.removedAfter current protections removed index node next,
            .inr ⟨.ForeignAccess,recorded,next,delta,classified,record,access,rfl,rfl⟩,
            afterLegal,afterMatches,afterCoherent,?_⟩
          exact fun query different => updated_other tree current index query node protections recorded next delta different
    obtain ⟨after,afterRemoved,action,legal,matching,coherent,other⟩ := old
    exact ⟨after,afterRemoved,.inl action,legal,matching,coherent,other⟩
  · obtain ⟨legal,matching,_,coherent,_,_,other,_⟩ :=
      DuplicatePrefixResidualPostchildrenNoop.materialized_preserves tree initial current protections maximum removed
        index node present legal matching currentCoherent profile possible
    exact ⟨materialized current index node,removed,.inr ⟨repaired.2,rfl,rfl⟩,legal,matching,coherent,other⟩

private theorem access_with_geometry (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (initialProfile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (initialPossible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (completion : Completion) (source : UniIndex)
    (classification : ∀ removed, Removal tree initial protections maximum .Write removed →
      ∀ index node, support.contains index → tree.nodes.get index = some node →
      let query := residualRelation tree initial protections root index node maximum .Write rootPosition removed
      (CandidateStableCallOwnership.Below completion index source → query = some .LocalAccess ∨ query = some .EitherAccess) ∧
      (¬CandidateStableCallOwnership.Below completion index source → query = some .ForeignAccess ∨ query = some .EitherAccess))
    (initialAuthority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (rootPosition != 0)
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections maximum .Write removed ∧
      Matches tree initial result.location protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  let Tracked (state : LoopState) : Prop :=
    RuntimeInvariant (initial := initial) (protections := protections) (rootPosition := rootPosition) (maximum := maximum) weights support plan state ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source state.1
  have step : ∀ state, Tracked state →
      (∃ final, scan () state = .done final ∧ Tracked final ∧
        ((rootPosition != 0) = true ∨ final.2.1 = true)) ∨
      ∃ next, scan () state = .yield next ∧ Tracked next ∧
        potential weights.weight next.2.2.2.1 < potential weights.weight state.2.2.2.1 := by
    intro state tracked
    rcases tracked with ⟨allValid,rights⟩
    rcases allValid with ⟨valid,profile,possible,vacant⟩
    rcases state with ⟨location,witness,status,stack,steps⟩
    have statusEq := valid.status
    dsimp only at statusEq
    subst status
    by_cases empty : stack = #[]
    · subst stack
      exact .inl ⟨_,by simp [scan],⟨⟨valid,profile,possible,vacant⟩,rights⟩,plan.finish witness valid.witness⟩
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
          rw [DuplicatePrefixResidualCountModel.relation_matches tree initial location protections .Write removed matching valid.coherent short root index node maximum rootPosition]
          cases queryEq : residualRelation tree initial protections root index node maximum .Write rootPosition removed with
          | none =>
            rcases pair with legacy | repaired
            · simp [queryEq,DuplicatePrefixCallbackVisitAuthorization.Authorized,
                DuplicatePrefixCallbackVisitAuthorization.entrySkip] at legacy
            · have classified := repaired.2.1
              simp [queryEq] at classified
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
            · exact ⟨DuplicatePrefixResidualEntryExpand.expand weights support plan short forest witness baseStack index node steps ⟨valid,profile,possible,vacant⟩ present notSkipped,rights⟩
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
            · exact ⟨DuplicatePrefixResidualEntryExpand.expand weights support plan short forest witness baseStack index node steps ⟨valid,profile,possible,vacant⟩ present notSkipped,rights⟩
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
              · exact ⟨⟨DuplicatePrefixResidualSavedWriteDFSInvariant.pop weights support plan location witness baseStack index node steps valid present skipRaw,profile,possible,vacant⟩,rights⟩
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
              · exact ⟨DuplicatePrefixResidualEntryExpand.expand weights support plan short forest witness baseStack index node steps ⟨valid,profile,possible,vacant⟩ present notSkipped,rights⟩
              · rw [expanded_potential,potential_push]
                simp only [cost,Bool.false_eq_true,↓reduceIte]
                have bounded := weights.children index node present
                omega
      | true =>
        have unvisited := DuplicatePrefixResidualSavedWriteDFSInvariant.top_unvisited weights support plan location witness baseStack index node true steps valid present
        obtain ⟨removed,legal,matching,pending⟩ := valid.model
        obtain ⟨before,legalBefore,subset,active⟩ := pending index node (by simp) present
        obtain ⟨after,afterRemoved,operations,afterLegal,afterMatches,afterCoherent,other⟩ :=
          post_model tree initial location protections root index node maximum rootPosition support.contains
            authorization before removed legalBefore subset legal matching valid.coherent short depth supported present unvisited profile possible active
        have monotone := action_mono tree location protections root index node maximum rootPosition removed after afterRemoved operations
        have oldMaintained := DuplicatePrefixResidualSavedWriteDFSInvariant.post weights support plan location after witness baseStack index node steps
          valid present removed afterRemoved pending monotone afterLegal afterMatches afterCoherent other
        have maintained : RuntimeInvariant (initial := initial) (protections := protections)
            (rootPosition := rootPosition) (maximum := maximum) weights support plan
            (after,seen location index node maximum protections witness,.Completed,baseStack,steps+1) := by
          rcases operations with old | ⟨_,same,_⟩
          · obtain ⟨afterProfile,afterPossible,afterVacant⟩ :=
              GeneralBorrowResidualWriteRuntime.action_runtime tree location protections root index node maximum rootPosition
                removed after afterRemoved present profile possible old
            exact ⟨oldMaintained,afterProfile,afterPossible,fun query missing => (afterVacant query missing).trans (vacant query missing)⟩
          · subst after
            exact DuplicatePrefixResidualPostchildrenNoop.preserve_runtime weights support plan witness baseStack index node steps
              ⟨valid,profile,possible,vacant⟩ present
        have afterRights : S05CompletedAncestryReadMutable.Authority tree completion protections source after := by
          rcases operations with old | ⟨_,same,_⟩
          · rcases old with ⟨_,same,_⟩ | ⟨exact,recorded,next,delta,classified,record,access,same,_⟩
            · subst after
              exact S05CompletedWriteAuthorityRetention.materialized_authority tree completion location protections source index node present rights
            · subst after
              have shape := classification removed legal index node supported present
              have matchingRelation := DuplicatePrefixResidualCountModel.relation_matches tree initial location protections .Write removed matching valid.coherent short root index node maximum rootPosition
              dsimp only at shape
              rw [←matchingRelation,classified] at shape
              exact S05CompletedWriteAuthorityRetention.updated_authority tree completion location protections source index node present rights
                exact recorded next delta
                (by intro below; rcases shape.1 below with localCase | eitherCase <;> cases exact <;> simp_all only [GeneralBorrowSnapshotReadState.wildcard, Option.some.injEq, reduceCtorEq])
                (by intro outside; rcases shape.2 outside with foreignCase | eitherCase <;> cases exact <;> simp_all only [GeneralBorrowSnapshotReadState.wildcard, Option.some.injEq, reduceCtorEq])
                record access
          · subst after
            exact S05CompletedWriteAuthorityRetention.materialized_authority tree completion location protections source index node present rights
        rcases operations with legacy | ⟨guard,materializedEq,_⟩
        · rcases legacy with ⟨classified,materializedEq,_⟩ | ⟨exact,recorded,next,delta,classified,record,access,updatedEq,_⟩
          · subst after
            have exactRel := sourceRelated .EitherAccess classified
            unfold aboveMaximum at exactRel
            refine .inr ⟨(materialized location index node,seen location index node maximum protections witness,.Completed,baseStack,steps+1),?_,⟨maintained,afterRights⟩,?_⟩
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
              seen location index node maximum protections witness,.Completed,baseStack,steps+1),?_,⟨maintained,afterRights⟩,?_⟩
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
        · subst after
          have exactRel := sourceRelated .ForeignAccess guard.1
          unfold aboveMaximum at exactRel
          have scalar : DuplicatePrefixCallbackVisitAuthorizationRepaired.PostchildrenNoop
              (effective location index node) .Write (protections.contains node.tag) (some .ForeignAccess) := by
            simpa only [guard.1] using guard
          have sourceGuard := DuplicatePrefixCallbackVisitAuthorizationRepaired.guard_source _ _ _ scalar
          refine .inr ⟨(materialized location index node,seen location index node maximum protections witness,.Completed,baseStack,steps+1),?_,⟨maintained,afterRights⟩,?_⟩
          · simp only [scan]
            unfold_leaf_helpers
            simp [notPast,present,exactRel,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals simp only [exactRel,or_insert_snd,sourceGuard,ite_true]
            all_goals cases maximum <;> simp_all [materialized,seen,effective,Id.run,bind,pure]
            all_goals try unfold_leaf_helpers
            all_goals try simp_all [materialized,seen,effective,Id.run,bind,pure]
            all_goals split <;> simp_all [Bool.and_eq_false_iff]
            all_goals cases exposed : node.isExposed <;> simp_all [effective]
            all_goals cases permits : ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write <;> simp_all [effective]
            all_goals try
              have no : ¬ node.tag.value ≤ _ := UInt64.not_le.mpr (by assumption)
              simp_all only [no,decide_false,Bool.false_or]
          · rw [potential_push];simp [cost]
  have run : ∀ bound (state : LoopState), potential weights.weight state.2.2.2.1 = bound →
      Tracked state →
      Tracked (Lean.Loop.forIn (m := Id) {} state scan) ∧
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
    ⟨⟨DuplicatePrefixResidualSavedWriteDFSInvariant.initial weights support plan coherent,initialProfile,initialPossible,(by intros; rfl)⟩,initialAuthority⟩
  have finalModel : ∃ removed, Removal tree initial protections maximum .Write removed ∧
      Matches tree initial (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1 protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1 protections ∧
      (∀ query, ¬support.contains query → (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1.perms.get query = initial.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1 protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1 ∧
      (∀ query, tree.nodes.get query = none → (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1.perms.get query = initial.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source (Lean.Loop.forIn (m := Id) {} (initial,false,.Completed,#[(root,false)],0) scan : Id LoopState).1 := by
    obtain ⟨removed,legal,matching,_⟩ := retained.1.1.1.model
    exact ⟨removed,legal,matching,retained.1.1.1.coherent,retained.1.1.1.outside,retained.1.1.2.1,retained.1.1.2.2.1,retained.1.1.2.2.2,retained.1.2⟩
  rcases retained.2 with virtual | found
  · simp only [retained.1.1.1.status,virtual,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨True.intro,finalModel⟩
  · simp only [retained.1.1.1.status,found,Bool.not_true,Bool.false_and,Bool.and_false,Bool.false_eq_true,↓reduceIte]
    exact ⟨True.intro,finalModel⟩

theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (initialProfile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (initialPossible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (completion : Completion) (source selectedRoot : UniIndex) (selectedPosition : Nat) (selectedNode : TreeNode)
    (complete : Completes tree completion) (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot) (selectedPath : Path tree selectedRoot source)
    (areaPath : ∀ index, support.contains index → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index)
    (cutoffEq : maximum = some selectedNode.tag)
    (initialAuthority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (rootPosition != 0)
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections maximum .Write removed ∧
      Matches tree initial result.location protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location := by
  apply access_with_geometry tree initial protections root rootPosition maximum weights rootBound support plan authorization
    depth forest coherent short initialProfile initialPossible completion source _ initialAuthority
  intro removed legal index node supported present
  have selectedLegal : Removal tree initial protections (some selectedNode.tag) .Write removed := by
    simpa only [cutoffEq] using legal
  simpa only [cutoffEq] using S05CompletedWriteAuthorityRetention.query_shape tree completion initial protections complete depth order
    rootPosition selectedPosition root selectedRoot source index node selectedNode rootSlot selectedSlot selectedPresent different
    selectedPath (areaPath index supported) present
    (fun query found lookup _ below => (initialAuthority query found lookup).1 below) removed selectedLegal

theorem access_none (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (initialProfile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (initialPossible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (completion : Completion) (source selectedRoot : UniIndex) (selectedPosition : Nat) (selectedNode sourceNode : TreeNode)
    (complete : Completes tree completion) (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (exposed : sourceNode.isExposed = true) (selectedPath : Path tree selectedRoot source)
    (areaPath : ∀ index, support.contains index → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index)
    (cutoffEq : maximum = none)
    (initialAuthority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (rootPosition != 0)
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections maximum .Write removed ∧
      Matches tree initial result.location protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location := by
  apply access_with_geometry tree initial protections root rootPosition maximum weights rootBound support plan authorization
    depth forest coherent short initialProfile initialPossible completion source _ initialAuthority
  intro removed legal index node supported present
  have noneLegal : Removal tree initial protections none .Write removed := by
    simpa only [cutoffEq] using legal
  have empty := DuplicatePrefixResidualSupportAuthorization.no_maximum_removal_empty tree initial protections .Write removed noneLegal
  subst removed
  simpa only [cutoffEq] using S05WildcardCompletedWriteQueries.query_shape tree completion initial protections complete depth order
    rootPosition selectedPosition root selectedRoot source index node selectedNode sourceNode rootSlot selectedSlot selectedPresent sourcePresent exposed
    selectedPath (areaPath index supported) present
    (fun query found lookup below => (initialAuthority query found lookup).1 below)

end DuplicatePrefix.S05CompletedWriteAuthorityDFS
