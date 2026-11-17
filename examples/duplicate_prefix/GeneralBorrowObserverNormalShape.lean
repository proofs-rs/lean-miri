import duplicate_prefix.GeneralBorrowObserverSharedRange
import duplicate_prefix.GeneralBorrowNormalCapabilityShape
namespace DuplicatePrefix.GeneralBorrowObserverNormalShape
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowView GeneralBorrowFreshOwnership GeneralBorrowObserverSharedRange GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def transport {before after : TraversalTree} (same : after = before) (anchor : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before anchor) :
    GeneralBorrowExposedScopedNormal.Component after anchor := same.symm ▸ old
private theorem support {before after : TraversalTree} (same : after = before) (anchor : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before anchor) :
    (transport same anchor old).support = old.support := by cases same;rfl
private theorem size (tree : BorrowTree) (location : LocationTree) (virtual : ProtectedTags) :
    (source_normal_projection tree location virtual).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection;unfold_general_topology;simp only [Array.size_map]

/-- SIFA-only metadata changes preserve an observer's exact component support. -/
theorem normal (before after : BorrowTree) (oldLocation newLocation : LocationTree) (virtual : ProtectedTags)
    (observer : UniIndex)
    (same : normalShape (source_normal_projection after newLocation virtual) = normalShape (source_normal_projection before oldLocation virtual))
    (old : DuplicatePrefixBorrowAuthorization.Normal before oldLocation virtual observer) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal after newLocation virtual observer,
      next.component.support = old.component.support := by
  have topology := congrArg (fun row => row.1) same
  let component := transport topology observer.toNat old.component
  have supportEq : component.support = old.component.support := support topology observer.toNat old.component
  refine ⟨⟨component,?_⟩,supportEq⟩
  intro kind index included valid
  apply DuplicatePrefixConstructorNormalShape.permissions
    (source_normal_projection before oldLocation virtual) (source_normal_projection after newLocation virtual)
    same observer.toNat kind old.component.support _ index (by rw [←supportEq];exact included)
      (by rw [size after newLocation virtual];exact valid)
  intro query supported bounded
  exact old.permissions kind query supported (by rw [←size before oldLocation virtual];exact bounded)

/-- Actual ancestor SIFA update preserves every installed observer row, along
with parent/new-child graph membership for the next constructor. -/
theorem owned (before after : BorrowTree) (same : treeShape after = treeShape before)
    (virtual : ProtectedTags) (parent observer child : UniIndex) (lower upper : UInt64)
    (initial : OwnedOn (Both before virtual parent observer child) lower upper before.locations) :
    OwnedOn (Both after virtual parent observer child) lower upper after.locations := by
  have nodes : after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) :=
    congrArg (fun row => row.2.1) same
  have ranges : after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) :=
    congrArg (fun row => row.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro position valid positive beforeUpper afterLower
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have entriesSame : (after.locations.entries[position]'valid).range = (before.locations.entries[position]'oldValid).range ∧
      locationShape (after.locations.entries[position]'valid).data = locationShape (before.locations.entries[position]'oldValid).data := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at known
    exact Prod.mk.inj (Option.some.inj known)
  rw [entriesSame.1] at beforeUpper afterLower
  obtain ⟨previous,parentSupported,childSupported⟩ := initial position oldValid positive beforeUpper afterLower
  have profiles := GeneralBorrowFreshOwnership.projection_shape before after
    (before.locations.entries[position]'oldValid).data (after.locations.entries[position]'valid).data virtual nodes entriesSame.2
  obtain ⟨next,supportEq⟩ := normal before after _ _ virtual observer profiles previous
  exact ⟨next,supportEq.symm ▸ parentSupported,supportEq.symm ▸ childSupported⟩
end DuplicatePrefix.GeneralBorrowObserverNormalShape
