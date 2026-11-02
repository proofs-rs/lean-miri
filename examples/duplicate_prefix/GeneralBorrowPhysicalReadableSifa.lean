import duplicate_prefix.GeneralBorrowSparseReadSifa
import duplicate_prefix.GeneralBorrowPhysicalReadable
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableSifa
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowStorage
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (readable : GeneralBorrowPhysicalReadable.Profile tree location protections)
    (initial : GeneralBorrowLocationSifaConsistency.Profile tree location protections) :
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections := by
  have complete := GeneralBorrowPhysicalReadable.normal tree location protections anchor mode forest fits depth children anchorNode anchorPresent readable
  have masked := GeneralBorrowSparseReadSifa.events (GeneralBorrowGraph.Present tree)
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    (source_normal_projection tree location protections)
    (by
      intro event member
      obtain ⟨index,node,_,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location protections depth children anchor anchorNode anchorPresent .Read mode event member
      exact ⟨index,node,indexEq,present⟩)
    (GeneralBorrowPhysicalReadable.projection tree location protections fits readable)
    (GeneralBorrowLocationSifaConsistency.projection tree location protections fits initial)
  change GeneralBorrowNormalSifaConsistency.Profile
    ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).tree at masked
  rw [←GeneralBorrowRangePreserves.normal_projection tree location protections anchor .Read mode fits] at masked
  refine ⟨complete.1,complete.2.1,?_,?_⟩
  · intro query node present
    have bound : query.toNat < (source_normal_projection tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections).locationStates.size := by
      rw [(projection_sizes _ _ _).1]
      exact (array_of_node tree query node present).1
    let state := ((tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get query).getD node.defaultLocationState
    have physical := projection_location_state tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections query node present
    have stored : (source_normal_projection tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections).stateAt query.toNat = some state := by
      simpa [state,BorrowTree.locationStateAt,present] using physical
    have consistent := masked query.toNat state stored
    rw [GeneralBorrowNormalPermissionMetadata.held tree _ protections query node present] at consistent
    exact consistent
  · intro query missing
    exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections anchor query .Read mode depth children anchorNode anchorPresent missing
      (initial.vacant query missing)

end DuplicatePrefix.GeneralBorrowPhysicalReadableSifa
