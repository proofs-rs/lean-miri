import duplicate_prefix.GeneralBorrowExposedScopedAncestorSharedConstructor
import duplicate_prefix.GeneralBorrowProtectorCacheMap
import duplicate_prefix.GeneralBorrowProtector
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorSharedProtect
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedAncestorSharedConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A real fresh Strong registration preserves the whole scoped exposed-leaf
constructor contract, not merely its normal projection. Freshness concerns
initial node/tag data and does not assume registration or borrow success. -/
theorem protect (input : Input) (protections : ProtectedTags) (tag : BorTag) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (fresh : ∀ index node,input.tree.nodeAt index = some node → node.tag ≠ tag) :
    ∃ next : Resources input (protections.insert tag .StrongProtector) selected head tail writable,
      next.component.support = raw.component.support := by
  have protectorFresh : GeneralBorrowProtector.Fresh input.tree tag := by
    intro row member
    have present := (GeneralBorrowFreshReuseProtection.entries_get input.tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
    exact fresh row.1 row.2 present
  have projection (location : LocationTree) := GeneralBorrowProtector.normal_projection input.tree location protections tag .StrongProtector protectorFresh
  let component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection input.tree default (protections.insert tag .StrongProtector)).topology input.parent.toNat := {
    support := raw.component.support
    anchor := raw.component.anchor
    parents := by rw [projection default];exact raw.component.parents
    children := by rw [projection default];exact raw.component.children }
  let next : Resources input (protections.insert tag .StrongProtector) selected head tail writable := {
    forest := by rw [projection default];exact raw.forest
    component := component
    selectedNode := raw.selectedNode
    selectedPresent := raw.selectedPresent
    roots := raw.roots
    rootPath := by rw [projection default];exact raw.rootPath
    ancestry := raw.ancestry
    exposedUnique := raw.exposedUnique
    separate := raw.separate
    tags := raw.tags
    leaves := raw.leaves
    unique := raw.unique
    first := raw.first
    rest := raw.rest
    coherent := by
      intro position valid
      apply GeneralBorrowProtectorCacheMap.register input.tree _ protections tag .StrongProtector (raw.coherent position valid)
      intro index node present same
      exact False.elim (fresh index node present same)
    owned := by
      intro position valid positive lower upper
      change GeneralBorrowExposedScopedOwnership.Pointwise raw.component.support
        (source_normal_projection input.tree _ (protections.insert tag .StrongProtector)) writable
        (GeneralBorrowAnchor.relation (source_normal_projection input.tree _ (protections.insert tag .StrongProtector)) input.parent.toNat)
      rw [projection]
      exact raw.owned position valid positive lower upper
    room := raw.room }
  exact ⟨next,rfl⟩
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorSharedProtect
