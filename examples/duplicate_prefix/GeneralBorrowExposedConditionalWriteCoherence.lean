import duplicate_prefix.GeneralBorrowExposedConditionalWriteState
namespace DuplicatePrefix.GeneralBorrowExposedConditionalWriteCoherence
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowExposedNonleafState (updated updated_other)
open GeneralBorrowExposedNonleafCoherence (effective_congr)
open GeneralBorrowExposureCardinality (LocationCoherent)
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
theorem updated_coherent (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition) (related : AccessRelatedness)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (present : tree.nodes.get index = some node)
    (coherent : LocationCoherent tree location protections)
    (record : (effective location index node).recordNewAccess .Write related = .Recorded recorded)
    (access : recorded.performAccess .Write related (protections.contains node.tag) = .Success next delta) :
    LocationCoherent tree (updated tree location index node protections recorded next delta) protections := by
  let replacement := GeneralBorrowExposurePermissionUpdate.nextLocation tree location protections index node next
  have preserved := GeneralBorrowExposurePermissionUpdate.preserves tree location protections depth coherent index node present next
  have endpoints := GeneralBorrowEventTransitionMetadata.success_endpoint recorded next delta .Write related (protections.contains node.tag) access
  have old := GeneralBorrowEventTransitionMetadata.record_permission _ _ .Write related record
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

end DuplicatePrefix.GeneralBorrowExposedConditionalWriteCoherence
