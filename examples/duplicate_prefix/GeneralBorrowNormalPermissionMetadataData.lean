import duplicate_prefix.GeneralBorrowExposureCardinality
import duplicate_prefix.GeneralBorrowProjection
namespace DuplicatePrefix.GeneralBorrowNormalPermissionMetadataData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposureCardinality
set_option autoImplicit false in
/-- Initial and final permission metadata for one actual normal-access visitor.
Constructing this record requires the real source transition and materialized
endpoint; the cache coherence proof consumes it without assuming access success. -/
structure EventMetadata (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) (event : TraversalEvent) where
  index : UniIndex
  node : TreeNode
  oldState : LocationState
  newState : LocationState
  transition : PermTransition
  converted : UniIndex.ofNat? event.node = some index
  present : tree.nodeAt index = some node
  oldPresent : tree.locationStateAt location index = some oldState
  newPresent : ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.stateAt event.node = some newState
  performed : performAccessTransition kind event.relatedness oldState.permission (protections.contains node.tag) = .Transition transition
  fromPermission : transition.fromPermission = oldState.permission
  finalEndpoint : transition.toPermission = newState.permission
  finalStored : ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates[index.toNat]? = some (some newState)
  noopLevel : transition.isNoop = true →
    oldState.permission.strongestAllowedLocalAccess (protections.contains node.tag) =
      newState.permission.strongestAllowedLocalAccess (protections.contains node.tag)
  newEffective : effective (tree.performNormalAccessAt location anchor kind protections mode).location protections index node =
    newState.permission.strongestAllowedLocalAccess (protections.contains node.tag)
end DuplicatePrefix.GeneralBorrowNormalPermissionMetadataData
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowNormalPermissionMetadataData.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generic normal permission data dependency {dependency}"
