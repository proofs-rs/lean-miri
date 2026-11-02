import duplicate_prefix.GeneralBorrowExposedNonleafState

namespace DuplicatePrefix.GeneralBorrowExposedNonleafCoherence
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState
open GeneralBorrowExposureCardinality (LocationCoherent)
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

theorem effective_congr (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (coherent : LocationCoherent tree before protections)
    (cache : after.exposedCache = before.exposedCache)
    (same : ∀ query node, tree.nodes.get query = some node → effective after query node = effective before query node) :
    LocationCoherent tree after protections := by
  intro query kind
  rw [cache,coherent query kind]
  apply congrArg UInt16.ofNat
  apply GeneralBorrowExposurePermissionUpdate.cardinality_congr
  intro index node present
  change (effective before index node).permission.strongestAllowedLocalAccess (protections.contains node.tag) =
    (effective after index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)
  rw [same index node present]

theorem materialized_coherent (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (present : tree.nodes.get root = some node)
    (coherent : LocationCoherent tree location protections) :
    LocationCoherent tree (materialized location root node) protections :=
  effective_congr tree location _ protections coherent rfl
    (fun query queryNode found => GeneralBorrowExposedVirtualSchedule.materialized_effective tree location root node present query queryNode found)

theorem updated_coherent (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition) (related : AccessRelatedness)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (present : tree.nodes.get index = some node)
    (coherent : LocationCoherent tree location protections)
    (record : (effective location index node).recordNewAccess .Read related = .Recorded recorded)
    (access : recorded.performAccess .Read related (protections.contains node.tag) = .Success next delta) :
    LocationCoherent tree (updated tree location index node protections recorded next delta) protections := by
  let replacement := GeneralBorrowExposurePermissionUpdate.nextLocation tree location protections index node next
  have preserved := GeneralBorrowExposurePermissionUpdate.preserves tree location protections depth coherent index node present next
  have endpoints := GeneralBorrowEventTransitionMetadata.success_endpoint recorded next delta .Read related (protections.contains node.tag) access
  have old := GeneralBorrowEventTransitionMetadata.record_permission _ _ .Read related record
  have noop : delta.isNoop = true → next.permission = (effective location index node).permission := by
    intro same
    have eq : delta.fromPermission = delta.toPermission := by simpa only [PermTransition.isNoop,beq_iff_eq] using same
    exact endpoints.2.2.symm.trans (eq.symm.trans (endpoints.2.1.trans old))
  have cache : (updated tree location index node protections recorded next delta).exposedCache = replacement.exposedCache := by
    dsimp only [updated,replacement,GeneralBorrowExposurePermissionUpdate.nextLocation,
      GeneralBorrowExposurePermissionUpdate.cacheUpdate,GeneralBorrowExposurePermissionUpdate.newLevel,
      GeneralBorrowExposureLevelTransition.operation,GeneralBorrowExposureCardinality.effective]
    cases exposed : node.isExposed <;> cases noOp : delta.isNoop
    all_goals simp only [exposed,noOp,Bool.not_true,Bool.not_false,Bool.true_and,Bool.false_and,
      Bool.false_eq_true,ite_false,ite_true]
    all_goals try rfl
    have permission := noop noOp
    rw [permission]
    simp only [effective,ExposedCache.updateExposure,beq_self_eq_true,ite_true,Id.run,pure]
  apply effective_congr tree replacement _ protections preserved.2 cache
  intro query queryNode found
  by_cases same : query = index
  · subst query
    have sameNode := Option.some.inj (present.symm.trans found)
    subst queryNode
    simp only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,replacement,
      GeneralBorrowExposurePermissionUpdate.nextLocation,GeneralBorrowFreshLocation.get_same,Option.getD_some]
  · simp only [effective,updated_other tree location index query node protections recorded next delta same,replacement,
      GeneralBorrowExposurePermissionUpdate.nextLocation,GeneralBorrowFreshLocation.get_other _ index query next same]

end DuplicatePrefix.GeneralBorrowExposedNonleafCoherence
