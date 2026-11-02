import duplicate_prefix.GeneralBorrowStructuralHistorySifaState
import duplicate_prefix.GeneralBorrowForestTagHighWater
import duplicate_prefix.GeneralBorrowExposedScopedNormal
import duplicate_prefix.GeneralRangeMapOrigins
namespace DuplicatePrefix.DuplicatePrefixBorrowContract
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Static call-time machine facts, not an execution history or a definition of
complete Rust/Lean reference validity. Scalar permission/SIFA, vacant-slot,
exposure cache and global tag consistency remain independent of slice ownership.
Numeric headroom and physical caller/ABI conditions are deliberately separate. -/
structure RuntimeFacts (tree : BorrowTree) (global : GlobalState) : Prop where
  formed : GeneralBorrowStructuralHistorySifaState.Formed tree global.protectedTags
  coherent : GeneralRangeMapState.Every
    (fun location=>GeneralBorrowExposureCardinality.LocationCoherent tree location global.protectedTags) tree.locations
  possible : GeneralRangeMapState.Every (fun location=>∀ index node,tree.nodeAt index=some node→
    ((location.perms.get index).getD node.defaultLocationState).possible=true) tree.locations
  below : GeneralBorrowForestTagHighWater.Below tree global.protectedTags global.nextPointerTag

theorem vacant_clean {tree : BorrowTree} {global : GlobalState} (facts : RuntimeFacts tree global) :
    GeneralBorrowGcVacantClean.VacantClean tree :=
  GeneralBorrowStructuralHistorySifaState.vacant_clean tree global.protectedTags facts.formed

/-- Permission kernel for the NORMAL phase of a positive concrete slice access.
No single-root, hidden/exposed, leaf, tag-order, append-only, or global outside-
window permission restriction is imposed. General exposed-root callbacks are a
SEPARATE outstanding obligation: this record alone is not complete ValidCaller. -/
structure ConcreteNormalWrite (tree : BorrowTree) (protections : ProtectedTags)
    (tag : BorTag) (offset len : UInt64) where
  anchor : UniIndex
  node : TreeNode
  tagPresent : tree.indexOfTag tag=some anchor
  present : tree.nodeAt anchor=some node
  positive : 0<len.toNat
  bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat
  component : GeneralBorrowExposedScopedNormal.Component
    (source_normal_projection tree default protections).topology anchor.toNat
  owned : GeneralRangeMapOrigins.OwnedOn (fun location=>
    GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections)
      anchor.toNat .Write component) offset (offset+len) tree.locations

/-- The data-only permission kernel derives the real normal phase, for either
child visit mode, on every actual partition intersecting the supplied slice.
This does not certify the later exposed-root callbacks or the whole function. -/
theorem normal_write_at (tree : BorrowTree) (global : GlobalState) (tag : BorTag) (offset len : UInt64)
    (runtime : RuntimeFacts tree global) (permission : ConcreteNormalWrite tree global.protectedTags tag offset len)
    (position : Nat) (valid : position<tree.locations.entries.size)
    (beforeUpper : tree.locations.entries[position].range.start.toNat<(offset+len).toNat)
    (afterLower : offset.toNat<tree.locations.entries[position].range.stop.toNat) (mode : ChildrenVisitMode) :
    (tree.performNormalAccessAt tree.locations.entries[position].data permission.anchor .Write global.protectedTags mode).access.status=.Completed ∧
    (tree.performNormalAccessAt tree.locations.entries[position].data permission.anchor .Write global.protectedTags mode).outcome=.ok () := by
  have lengthFits : offset.toNat+len.toNat<2^64 := by
    have capacity:=tree.locations.size.bytes.toNat_lt
    have bounds:=permission.bounds
    omega
  have positive : offset.toNat<(offset+len).toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt lengthFits]
    have nonzero:=permission.positive
    omega
  obtain ⟨forest⟩ := runtime.formed.forest tree.locations.entries[position].data global.protectedTags
  obtain ⟨depth⟩ := runtime.formed.depth
  exact GeneralBorrowExposedScopedNormal.access tree tree.locations.entries[position].data global.protectedTags permission.anchor .Write mode
    forest permission.component (permission.owned position valid positive beforeUpper afterLower)
    depth runtime.formed.children permission.node permission.present
end DuplicatePrefix.DuplicatePrefixBorrowContract
