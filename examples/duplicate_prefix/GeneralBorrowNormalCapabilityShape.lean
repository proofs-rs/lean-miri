import duplicate_prefix.GeneralBorrowSharedMaterializedCapability
namespace DuplicatePrefix.GeneralBorrowNormalCapabilityShape
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowView GeneralBorrowFreshOwnership
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def transport_component {before after : TraversalTree} (same : after = before) (anchor : Nat)
    (component : GeneralBorrowExposedScopedNormal.Component before anchor) :
    GeneralBorrowExposedScopedNormal.Component after anchor := same.symm ▸ component

private theorem transport_support {before after : TraversalTree} (same : after = before) (anchor : Nat)
    (component : GeneralBorrowExposedScopedNormal.Component before anchor) :
    (transport_component same anchor component).support = component.support := by cases same;rfl

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- SIFA-only shape changes preserve an internal one-kind source capability. -/
theorem capability (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (source : UniIndex) (kind : AccessKind)
    (same : normalShape (source_normal_projection after newLocation protections) = normalShape (source_normal_projection before oldLocation protections))
    (old : DuplicatePrefixNormalKind.Capability before oldLocation protections source kind) :
    Nonempty (DuplicatePrefixNormalKind.Capability after newLocation protections source kind) := by
  have topology := congrArg (fun row => row.1) same
  let component := transport_component topology source.toNat old.component
  have supportEq : component.support = old.component.support := transport_support topology source.toNat old.component
  have permissions := DuplicatePrefixConstructorNormalShape.permissions
    (source_normal_projection before oldLocation protections) (source_normal_projection after newLocation protections)
    same source.toNat kind old.component.support (by
      intro index included valid
      exact old.permissions index included (by rw [←topology_size before oldLocation protections];exact valid))
  refine ⟨⟨component,?_⟩⟩
  intro index included valid
  exact permissions index (by rw [←supportEq];exact included) (by rw [topology_size after newLocation protections];exact valid)

/-- SIFA-only shape changes preserve the existing S01 Both Normal unchanged
in meaning; only its component is transported across equal topology. -/
theorem normal (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (source : UniIndex)
    (same : normalShape (source_normal_projection after newLocation protections) = normalShape (source_normal_projection before oldLocation protections))
    (old : DuplicatePrefixBorrowAuthorization.Normal before oldLocation protections source) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal after newLocation protections source) := by
  have topology := congrArg (fun row => row.1) same
  let component := transport_component topology source.toNat old.component
  have supportEq : component.support = old.component.support := transport_support topology source.toNat old.component
  refine ⟨⟨component,?_⟩⟩
  intro kind index included valid
  apply DuplicatePrefixConstructorNormalShape.permissions
    (source_normal_projection before oldLocation protections) (source_normal_projection after newLocation protections)
    same source.toNat kind old.component.support _ index (by rw [←supportEq];exact included)
      (by rw [topology_size after newLocation protections];exact valid)
  intro query supported bounded
  exact old.permissions kind query supported (by rw [←topology_size before oldLocation protections];exact bounded)

end DuplicatePrefix.GeneralBorrowNormalCapabilityShape
