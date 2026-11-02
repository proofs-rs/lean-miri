import duplicate_prefix.GeneralBorrowExposedConditionalAccessSupport
namespace DuplicatePrefix.GeneralBorrowExposedConditionalReadExactScalar
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowExposedNonleafState (updated)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem local_noop (state next : LocationState) (delta : PermTransition) (held : Bool)
    (compatible : GeneralBorrowProtectedReadCompatible.Compatible state .LocalAccess held)
    (access : state.performAccess .Read .LocalAccess held = .Success next delta) : delta.isNoop = true := by
  obtain ⟨expected,expectedDelta,performed,permission⟩ := GeneralBorrowExposedConditionalAccessSupport.local_read_levels state held compatible
  have equal := LocationState.AccessResult.Success.inj (performed.symm.trans access)
  have same : next.permission = state.permission := by rw [←equal.1];exact permission
  have endpoints := GeneralBorrowEventTransitionMetadata.success_endpoint state next delta .Read .LocalAccess held access
  simp only [PermTransition.isNoop,endpoints.2.1,endpoints.2.2,same,beq_self_eq_true]

theorem disabled_foreign_noop (state next : LocationState) (delta : PermTransition) (held : Bool)
    (disabled : state.permission = .Disabled)
    (access : state.performAccess .Read .ForeignAccess held = .Success next delta) : delta.isNoop = true := by
  have endpoints := (GeneralBorrowEventTransitionMetadata.success_endpoint state next delta .Read .ForeignAccess held access).1
  rw [disabled] at endpoints
  have primitive : performAccessTransition .Read .ForeignAccess .Disabled held = .Transition ⟨.Disabled,.Disabled⟩ := by cases held <;> rfl
  have equal := PermTransitionOutcome.Transition.inj (primitive.symm.trans endpoints)
  rw [←equal]
  rfl

/-- Every exact Read update with zero-count foreign rows retains the actual
cache object, not just selected counters. Exposed foreign rows are Disabled;
local Read preserves its permission, and unexposed rows never update exposure. -/
theorem updated_cache (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition) (related : AccessRelatedness)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (present : tree.nodes.get index = some node)
    (compatible : GeneralBorrowProtectedReadCompatible.Compatible (effective location index node) related (protections.contains node.tag))
    (record : (effective location index node).recordNewAccess .Read related = .Recorded recorded)
    (access : recorded.performAccess .Read related (protections.contains node.tag) = .Success next delta)
    (foreignZero : related = .ForeignAccess → GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Read = 0) :
    (updated tree location index node protections recorded next delta).exposedCache = location.exposedCache := by
  have permission := GeneralBorrowEventTransitionMetadata.record_permission _ _ .Read related record
  cases exposed : node.isExposed with
  | false => simp only [updated,exposed,Bool.false_and,Bool.false_eq_true,ite_false]
  | true =>
    have noop : delta.isNoop = true := by
      cases related with
      | LocalAccess =>
        have good : GeneralBorrowProtectedReadCompatible.Compatible recorded .LocalAccess (protections.contains node.tag) := by
          unfold GeneralBorrowProtectedReadCompatible.Compatible at compatible ⊢
          have possible : recorded.possible = (effective location index node).possible := by
            unfold LocationState.recordNewAccess at record
            split at record
            · cases record;rfl
            · cases record
          simpa only [possible,permission] using compatible
        exact local_noop recorded next delta _ good access
      | ForeignAccess =>
        have noSupport := GeneralBorrowExposedConditionalAccessSupport.exposed_zero tree location protections coherent short index node present exposed .Read (foreignZero rfl)
        have disabled := GeneralBorrowExposedConditionalAccessSupport.read_zero_permission (effective location index node) (protections.contains node.tag) noSupport
        exact disabled_foreign_noop recorded next delta _ (permission.trans disabled) access
    simp only [updated,exposed,noop,Bool.not_true,Bool.and_false,Bool.false_eq_true,ite_false]
end DuplicatePrefix.GeneralBorrowExposedConditionalReadExactScalar
