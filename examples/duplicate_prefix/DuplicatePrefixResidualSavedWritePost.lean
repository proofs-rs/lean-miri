import duplicate_prefix.DuplicatePrefixResidualWritePost
import duplicate_prefix.DuplicatePrefixResidualWriteStep
import duplicate_prefix.DuplicatePrefixResidualWriteQueries
import duplicate_prefix.GeneralBorrowExposedNonleafCoherence
import duplicate_prefix.GeneralBorrowSnapshotReadState
namespace DuplicatePrefix.DuplicatePrefixResidualSavedWritePost
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowExposedConditionalWritePermissions
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other)
open GeneralBorrowSnapshotReadState (wildcard)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev Action := DuplicatePrefixResidualWritePost.Action

theorem action_mono (tree : BorrowTree) (current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (removed : List UniIndex) (after : LocationTree) (afterRemoved : List UniIndex)
    (action : Action tree current protections root index node maximum position removed after afterRemoved) :
    ∀ query ∈ removed, query ∈ afterRemoved := by
  rcases action with ⟨_,_,same⟩ | ⟨exact,recorded,next,delta,_,_,_,_,same⟩
  · subst afterRemoved;intro query member;exact member
  · subst afterRemoved
    intro query member
    unfold DuplicatePrefixResidualWriteStep.removedAfter
    split <;> simp [member]

/-- A saved entry-mask skip=false and the raw query-pair contract derive the real Write
postorder action, including compatibility and scheduling of exact branches.
Only internal finite-model invariants and literal unvisited storage equality
are supplied; no operation-success, compatible, or scheduled premise is used. -/
theorem post (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (before removed : List UniIndex)
    (legalBefore : Removal tree initial protections maximum .Write before)
    (subset : ∀ query ∈ before, query ∈ removed)
    (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (currentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (inside : support index) (present : tree.nodes.get index = some node)
    (unvisited : current.perms.get index = initial.perms.get index)
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
  have branch := authorized.2.resolve_left (by
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
end DuplicatePrefix.DuplicatePrefixResidualSavedWritePost
