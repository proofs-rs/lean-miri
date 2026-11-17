import duplicate_prefix.GeneralBorrowExposedScopedWriteFrameAccess
import duplicate_prefix.GeneralBorrowExposedKnownRootRangeData
import duplicate_prefix.GeneralBorrowExposedScopedOwnership
namespace DuplicatePrefix.GeneralBorrowExposedScopedWriteClosedData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootWriteState
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
def primary {tree initial root protections}
    (data : GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree initial root protections)
    (current : LocationTree) (frame : WriteFrame initial current)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (profile : Profile tree current protections) :
    GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree current root protections where
  base := GeneralBorrowExposedKnownRootWriteTransport.rebase data.base current coherent profile
  graph := data.graph
  witness := data.witness
  node := data.node
  present := data.present
  exposed := data.exposed
  path := data.path
  support := by
    have positive := GeneralBorrowExposedKnownRootWritePrimaryPath.positive data.base data.witness data.node data.present data.exposed
      data.support data.witness (.refl data.witness data.node data.present)
    have compatible := local_compatible tree initial current protections frame profile data.witness data.node data.present
      (data.base.included data.witness (GeneralBorrowExposedKnownRootWritePrimaryWitness.path_supported data data.path)) (by omega)
    have allows := GeneralBorrowExposedConditionalWritePermissions.local_allows _ _ compatible
    change GeneralBorrowExposureCardinality.supports
      ((GeneralBorrowWildcardVirtualLeaf.effective current data.witness data.node).permission.strongestAllowedLocalAccess
        (protections.contains data.node.tag)) .Write = true
    cases level : ((GeneralBorrowWildcardVirtualLeaf.effective current data.witness data.node).permission.strongestAllowedLocalAccess
        (protections.contains data.node.tag)) <;>
      simp_all [GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsWrite,WildcardAccessLevel.allows]


/-- The actual scoped Write retains its complete raw next-Write contract.
Exact Write counters retain supporting witnesses, and the physical foreign
passes preserve every permission inside the hidden selected component. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (data : GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write) :
    source_access_status (source_tree_access_at tree location (some anchor) .Write protections mode range) = none ∧
      Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree
        (source_access_location (source_tree_access_at tree location (some anchor) .Write protections mode range))
        protections anchor selected head tail .Write) := by
  obtain ⟨after,actual,status,frame,profile,coherent,outside⟩ := GeneralBorrowExposedScopedWriteFrameAccess.access tree location protections
    anchor selected head context.anchorNode context.selectedNode tail mode range context.roots data.forest data.component data.owned
    context.depth context.children context.anchorPresent context.selectedPresent data.rootPath data.hidden data.separate
    data.coherent data.profile context.tags data.primary data.virtual
  have sizes := GeneralBorrowProjection.projection_sizes tree location protections
  have topologySize : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    rw [topologySize]
    exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor context.anchorNode context.anchorPresent
  have mixed : GeneralBorrowExposedScopedOwnership.Pointwise data.component.support
      (source_normal_projection tree location protections) (fun _=>true)
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
    intro index supported bound
    obtain ⟨state,present,permission⟩ := data.owned index supported (by rw [sizes.1,←topologySize] at bound;exact bound)
    exact ⟨state,present,permission⟩
  have normalMixed := GeneralBorrowExposedScopedOwnership.access_mixed tree location protections anchor .Write mode (fun _=>true)
    fits data.forest valid (sizes.1.trans topologySize.symm) data.component mixed
    (by intro index supported bound impossible;cases impossible)
  have afterMixed := GeneralBorrowExposedScopedOwnership.row_frame tree _ after protections data.component.support (fun _=>true) _ fits normalMixed
    (fun index member => outside index (fun included => data.separate index included member))
  refine ⟨status,?_⟩
  rw [actual]
  refine ⟨⟨data.forest,data.component,?_,data.rootPath,data.hidden,data.separate,coherent,profile,
    (fun different => primary (data.primary different) after frame coherent profile),
    (fun root member different => GeneralBorrowExposedKnownRootWriteTransport.rebase (data.virtual root member different) after coherent profile)⟩⟩
  intro index supported bound
  have statesValid : index < (source_normal_projection tree after protections).locationStates.size := by
    rw [(projection_sizes tree after protections).1,←topologySize]
    exact bound
  obtain ⟨state,present,permission⟩ := afterMixed index supported statesValid
  exact ⟨state,present,permission⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWriteClosedData
