import duplicate_prefix.GeneralBorrowExposedScopedAncestorMixedRangeData
import duplicate_prefix.GeneralBorrowExposedScopedMixedRebase
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorMixedRebase
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedScopedAncestorMixedRangeData (Data Mixed)
open GeneralBorrowExposedNonleafState (ReadFrame)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Re-form the complete initial raw Read contract after the actual operation.
Mixed labels supply selected ownership; frame/profile/coherence supply all
other-component records, including the physical first root's witness. -/
def rebase {tree initial protections anchor selected head tail support writable}
    (data : Data tree initial protections anchor selected head tail support writable)
    (current : LocationTree) (frame : ReadFrame initial current)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (profile : Readable tree current protections)
    (unique : GeneralBorrowExposedConstructorUnique.Unique tree current support)
    (mixed : Mixed tree current protections anchor support writable) :
    Data tree current protections anchor selected head tail support writable where
  base := {
    forest := data.base.forest
    component := data.base.component
    owned := by
      intro index supported valid
      have statesValid : index < (source_normal_projection tree current protections).locationStates.size := by
        rw [(projection_sizes tree current protections).1]
        have topologySize : (source_normal_projection tree current protections).topology.nodes.size = tree.nodes.data.size := by
          unfold_general_projection
          unfold_general_topology
          simp only [Array.size_map]
        rw [topologySize] at valid
        exact valid
      obtain ⟨state,present,permission⟩ := mixed index (by rw [←data.support_eq];exact supported) statesValid
      exact ⟨state,present,GeneralBorrowExposedScopedMixedRebase.required_read state (writable index) _ _ permission⟩
    rootPath := data.base.rootPath
    supportEq := data.base.supportEq
    ancestors := by
      intro index node state inside present exposed stored
      have initialState : tree.locationStateAt initial index=some ((initial.perms.get index).getD node.defaultLocationState) := by
        simp only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some]
      have ancestor := (data.base.ancestors index node _ inside present exposed initialState).1
      have stateEq : ((current.perms.get index).getD node.defaultLocationState)=state := by
        simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,Option.some.injEq] using stored
      refine ⟨ancestor,?_⟩
      rw [←stateEq]
      exact unique index node (by rw [←data.base.supportEq];exact inside) present exposed
    separate := data.base.separate
    coherent := coherent
    readable := profile
    primary := fun different => GeneralBorrowExposedScopedMixedRebase.primary (data.base.primary different) current frame coherent profile
    virtual := fun root member different => GeneralBorrowExposedKnownRootTransport.rebase
      (data.base.virtual root member different) current coherent profile }
  support_eq := data.support_eq
  mixed := mixed
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorMixedRebase
