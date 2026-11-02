import duplicate_prefix.GeneralBorrowIsolatedLeafNormal
import duplicate_prefix.GeneralBorrowFreshChild
namespace DuplicatePrefix.GeneralBorrowIsolatedLeafActivation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- The real isolated reservation's local Write stores exact Unique, including
when the new root is Strong-protected. Other physical components are untouched. -/
theorem unique (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (node : TreeNode) (mode : ChildrenVisitMode)
    (present : tree.nodeAt anchor=some node) (parentless : node.parent=none) (leaf : node.children=#[])
    (stored : location.perms.get anchor=some GeneralBorrowFreshChild.inside)
    (fits : tree.nodes.data.size≤4294967296) :
    (tree.performNormalAccessAt location anchor .Write protections mode).location.perms.get anchor=some GeneralBorrowWildcardLeaf.unique := by
  let projection := source_normal_projection tree location protections
  have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor node present
  have valid : anchor.toNat<projection.topology.nodes.size := by
    dsimp only [projection]
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using bound
  have projected := projection_topology_node tree location protections anchor.toNat anchor node rfl present
  have shape : projection.topology.nodes[anchor.toNat]=⟨none,[]⟩ := by
    rw [Array.getElem?_eq_getElem valid,Option.getD_some,parentless,leaf] at projected
    exact projected
  have events := GeneralBorrowIsolatedLeafNormal.schedule projection.topology anchor.toNat mode (sourceNormalSkipped projection .Write)
    valid (by rw [shape]) (by rw [shape])
  have statePresent : projection.stateAt anchor.toNat=some GeneralBorrowFreshChild.inside := by
    rw [projection_state tree location protections anchor.toNat anchor node (index_self anchor) rfl present]
    simp [stored]
  have stateValid : anchor.toNat<projection.locationStates.size := by
    rw [(projection_sizes tree location protections).1]
    exact bound
  have record : GeneralBorrowFreshChild.inside.recordNewAccess .Write .LocalAccess=.Recorded GeneralBorrowFreshChild.inside := rfl
  have transition : GeneralBorrowFreshChild.inside.performAccess .Write .LocalAccess (projection.protectedNodes.contains anchor.toNat)=
      .Success GeneralBorrowWildcardLeaf.unique ⟨.ReservedFrz false,.Unique⟩ := by
    cases projection.protectedNodes.contains anchor.toNat <;> rfl
  have activated : ((projection.performAccess anchor.toNat .Write mode).tree.locationStates[anchor.toNat]?)=some (some GeneralBorrowWildcardLeaf.unique) := by
    unfold NormalTreeState.performAccess
    dsimp only
    rw [events]
    unfold_normal_events
    simp only [statePresent,record,transition,stateValid,↓reduceDIte,LocationState.AccessResult.resultingState]
    simp [Array.getElem?_set_self]
  have projectionAfter := congrArg (fun state : NormalTreeState=>state.locationStates[anchor.toNat]?)
    (GeneralBorrowRangePreserves.normal_projection tree location protections anchor .Write mode fits)
  rw [activated] at projectionAfter
  have optional (next : LocationTree) : (source_normal_projection tree next protections).locationStates[anchor.toNat]? = some (next.perms.get anchor) := by
    unfold_general_projection
    rw [Array.getElem?_mapIdx,Array.getElem?_eq_getElem bound]
    obtain ⟨_,cell⟩ := array_of_node tree anchor node present
    simp only [cell,Option.map_some,index_self]
  rw [optional] at projectionAfter
  exact Option.some.inj projectionAfter
end DuplicatePrefix.GeneralBorrowIsolatedLeafActivation
