import duplicate_prefix.GeneralBorrowObserverReadNormal
import duplicate_prefix.DuplicatePrefixNormalAuthorizationPreservation

namespace DuplicatePrefix.GeneralBorrowObserverReadWriteback
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem stateAt_flags (tree : BorrowTree) (location : LocationTree) (first second : ProtectedTags) (index : Nat) :
    (source_normal_projection tree location first).stateAt index = (source_normal_projection tree location second).stateAt index := by
  unfold_general_projection
  rfl

theorem relation_flags (tree : BorrowTree) (before after : LocationTree) (first second : ProtectedTags) (anchor index : Nat) :
    GeneralBorrowAnchor.relation (source_normal_projection tree after second) anchor index =
      GeneralBorrowAnchor.relation (source_normal_projection tree before first) anchor index := by
  unfold GeneralBorrowAnchor.relation
  unfold_general_projection
  rfl

theorem protected_flags (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree after protections).protectedNodes = (source_normal_projection tree before protections).protectedNodes := by
  unfold_general_projection
  rfl

/-- Actual normal Read and physical writeback preserve a separately supplied
observer Both Normal under virtual protectors. The source needs Read only.
The relation/protector guards are finite graph data to derive inside callers. -/
theorem access (tree : BorrowTree) (location : LocationTree) (actual virtual : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (source observer : UniIndex) (sourceNode : TreeNode) (present : tree.nodeAt source = some sourceNode)
    (sourceRead : DuplicatePrefixNormalKind.Capability tree location actual source .Read)
    (observerBoth : DuplicatePrefixBorrowAuthorization.Normal tree location virtual observer)
    (fits : tree.nodes.data.size ≤ 4294967296) (mode : ChildrenVisitMode)
    (localSource : ∀ index,observerBoth.component.support index →
      GeneralBorrowAnchor.relation (source_normal_projection tree location virtual) observer.toNat index = .LocalAccess →
      GeneralBorrowAnchor.relation (source_normal_projection tree location actual) source.toNat index = .LocalAccess)
    (foreignLocal : ∀ index,observerBoth.component.support index →
      GeneralBorrowAnchor.relation (source_normal_projection tree location virtual) observer.toNat index = .ForeignAccess →
      GeneralBorrowAnchor.relation (source_normal_projection tree location actual) source.toNat index = .LocalAccess →
      (source_normal_projection tree location virtual).protectedNodes.contains index = false)
    (foreignHeld : ∀ index,observerBoth.component.support index →
      GeneralBorrowAnchor.relation (source_normal_projection tree location actual) source.toNat index = .ForeignAccess →
      (source_normal_projection tree location actual).protectedNodes.contains index =
        (source_normal_projection tree location virtual).protectedNodes.contains index) :
    (tree.performNormalAccessAt location source .Read actual mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location source .Read actual mode).outcome = .ok () ∧
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location source .Read actual mode).location virtual observer,
      next.component = observerBoth.component := by
  let projection := source_normal_projection tree location actual
  let related := GeneralBorrowAnchor.relation (source_normal_projection tree location virtual) observer.toNat
  let held := fun index => (source_normal_projection tree location virtual).protectedNodes.contains index
  have sizes := projection_sizes tree location actual
  have topologySize : projection.topology.nodes.size = tree.nodes.data.size := by
    dsimp only [projection]
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have aligned : projection.locationStates.size = projection.topology.nodes.size := sizes.1.trans topologySize.symm
  have valid : source.toNat < projection.topology.nodes.size := by
    rw [topologySize]
    exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes source sourceNode present
  have sourceOwned : GeneralBorrowReadCapabilityNormal.Pointwise sourceRead.component.support projection
      (GeneralBorrowAnchor.relation projection source.toNat) := by
    intro index included bounded
    have bound : index < tree.nodes.data.size := by rw [←sizes.1];exact bounded
    exact sourceRead.permissions index included bound
  have observerOwned : GeneralBorrowObserverReadNormal.Pointwise observerBoth.component.support projection related held := by
    intro index included bounded
    have bound : index < tree.nodes.data.size := by rw [←sizes.1];exact bounded
    obtain ⟨readState,readPresent,read⟩ := observerBoth.permissions .Read index included bound
    obtain ⟨writeState,writePresent,write⟩ := observerBoth.permissions .Write index included bound
    have equal := Option.some.inj (writePresent.symm.trans readPresent)
    subst writeState
    exact ⟨readState,(stateAt_flags tree location actual virtual index).trans readPresent,read,write⟩
  obtain ⟨forest⟩ := formed.forest location actual
  have pureResult := GeneralBorrowObserverReadNormal.normal projection forest source.toNat valid mode aligned sourceRead.component
    sourceOwned observerBoth.component.support related held observerOwned localSource foreignLocal foreignHeld
  have observerAfter : GeneralBorrowObserverReadNormal.Pointwise observerBoth.component.support
      (source_normal_projection tree (tree.performNormalAccessAt location source .Read actual mode).location actual) related held := by
    rw [GeneralBorrowRangePreserves.normal_projection tree location actual source .Read mode fits]
    exact pureResult.2
  obtain ⟨depth⟩ := formed.depth
  have complete := GeneralBorrowCompatibleScopedNormal.access tree location actual source .Read mode forest sourceRead.component
    (by intro index included bounded;apply sourceRead.permissions index included;rw [←topologySize];exact bounded)
    depth formed.children sourceNode present
  refine ⟨complete.1,complete.2,⟨observerBoth.component,?_⟩,rfl⟩
  intro kind index included bounded
  have finalBound : index < (source_normal_projection tree
      (tree.performNormalAccessAt location source .Read actual mode).location actual).locationStates.size := by
    rw [(projection_sizes tree _ actual).1];exact bounded
  obtain ⟨state,statePresent,both⟩ := observerAfter index included finalBound
  refine ⟨state,?_,?_⟩
  · rw [←stateAt_flags tree _ actual virtual index]
    exact statePresent
  · have relation : GeneralBorrowAnchor.relation (source_normal_projection tree
        (tree.performNormalAccessAt location source .Read actual mode).location virtual) observer.toNat index = related index :=
      relation_flags tree location _ virtual virtual observer.toNat index
    have flag : (source_normal_projection tree (tree.performNormalAccessAt location source .Read actual mode).location virtual).protectedNodes.contains index = held index :=
      congrArg (fun flags => flags.contains index) (protected_flags tree location _ virtual)
    rw [relation,flag]
    cases kind with
    | Read => exact both.1
    | Write => exact both.2

end DuplicatePrefix.GeneralBorrowObserverReadWriteback
