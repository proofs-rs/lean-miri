import duplicate_prefix.GeneralBorrowExposedScopedMixedRangeData
namespace DuplicatePrefix.GeneralBorrowExposedScopedMixedRebase
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedScopedMixedRangeData (Data Mixed)
open GeneralBorrowExposedNonleafState (ReadFrame)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Both mutable and read-only labels imply the raw permission for a Read. -/
theorem required_read (state : LocationState) (writable : Bool) (related : AccessRelatedness) (held : Bool)
    (owned : GeneralBorrowPermissions.Required state writable related held) :
    GeneralBorrowPermissions.AccessOwned state .Read related held := by
  cases writable with
  | false => exact owned
  | true =>
    cases related with
    | ForeignAccess => exact owned
    | LocalAccess =>
      rcases state with ⟨permission,accessed,sifa⟩
      cases permission with
      | ReservedFrz conflicted => cases conflicted <;> simp_all [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.Owned,GeneralBorrowPermissions.LocalOwned,GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.LocalReadable]
      | Cell | ReservedIM | Unique | Frozen | Disabled => simp_all [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.Owned,GeneralBorrowPermissions.LocalOwned,GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.LocalReadable]

/-- The original supporting descendant remains a real supporting witness.
Exact Read counters turn its scoped conditional postprofile into local Read
compatibility; this uses no poststate support assumption. -/
def primary {tree initial root protections}
    (data : GeneralBorrowExposedKnownRootPrimaryWitness.Data tree initial root protections)
    (current : LocationTree) (frame : ReadFrame initial current)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (profile : Readable tree current protections) :
    GeneralBorrowExposedKnownRootPrimaryWitness.Data tree current root protections where
  base := GeneralBorrowExposedKnownRootTransport.rebase data.base current coherent profile
  graph := data.graph
  witness := data.witness
  node := data.node
  present := data.present
  exposed := data.exposed
  path := data.path
  support := by
    have positive := GeneralBorrowExposedKnownRootPrimaryPath.positive data.base data.witness data.node data.present data.exposed
      data.support data.witness (.refl data.witness data.node data.present)
    have compatible := local_compatible tree initial current protections frame profile data.witness data.node data.present
      (data.base.included data.witness (GeneralBorrowExposedKnownRootPrimaryWitness.path_supported data data.path)) (by omega)
    have allows := GeneralBorrowExposedConditionalReadPermissions.local_allows _ _ compatible
    change GeneralBorrowExposureCardinality.supports
      ((GeneralBorrowWildcardVirtualLeaf.effective current data.witness data.node).permission.strongestAllowedLocalAccess
        (protections.contains data.node.tag)) .Read = true
    cases level : ((GeneralBorrowWildcardVirtualLeaf.effective current data.witness data.node).permission.strongestAllowedLocalAccess
        (protections.contains data.node.tag)) <;>
      simp_all [GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead,WildcardAccessLevel.allows]


/-- Re-form the complete initial raw Read contract after the actual operation.
Mixed labels supply selected ownership; frame/profile/coherence supply all
other-component records, including the physical first root's witness. -/
def rebase {tree initial protections anchor selected head tail support writable}
    (data : Data tree initial protections anchor selected head tail support writable)
    (current : LocationTree) (frame : ReadFrame initial current)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (profile : Readable tree current protections)
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
      exact ⟨state,present,required_read state (writable index) _ _ permission⟩
    rootPath := data.base.rootPath
    hidden := data.base.hidden
    separate := data.base.separate
    coherent := coherent
    profile := profile
    primary := fun different => primary (data.base.primary different) current frame coherent profile
    virtual := fun root member different => GeneralBorrowExposedKnownRootTransport.rebase
      (data.base.virtual root member different) current coherent profile }
  support_eq := data.support_eq
  mixed := mixed
end DuplicatePrefix.GeneralBorrowExposedScopedMixedRebase
