import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedConstructor
import duplicate_prefix.GeneralBorrowProtectorCacheMap
import duplicate_prefix.GeneralBorrowProtector
import duplicate_prefix.ProtectorInsertion
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedProtect
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableSharedConstructor (Resources ResourcesFor)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A real fresh Strong registration preserves the whole scoped exposed-leaf
constructor contract, not merely its normal projection. Freshness concerns
initial node/tag data and does not assume registration or borrow success. -/
theorem protect {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (tag : BorTag) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : ResourcesFor input protections selected head tail writable profileMode)
    (fresh : ∀ index node,input.tree.nodeAt index = some node → node.tag ≠ tag) :
    ∃ next : ResourcesFor input (protections.insert tag .StrongProtector) selected head tail writable profileMode,
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
  let next : ResourcesFor input (protections.insert tag .StrongProtector) selected head tail writable profileMode := {
    forest := by rw [projection default];exact raw.forest
    component := component
    selectedNode := raw.selectedNode
    selectedPresent := raw.selectedPresent
    roots := raw.roots
    rootPath := by rw [projection default];exact raw.rootPath
    exposures := raw.exposures
    separate := raw.separate
    tags := raw.tags
    leaves := raw.leaves
    writableLeaves := by
      intro position valid query node included present
      change GeneralBorrowExposedConditionalWritePermissions.Compatible _ .LocalAccess _
      rw [ProtectorInsertion.contains_other protections tag node.tag .StrongProtector (fresh query node present)]
      exact raw.writableLeaves position valid query node included present
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
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedProtect
