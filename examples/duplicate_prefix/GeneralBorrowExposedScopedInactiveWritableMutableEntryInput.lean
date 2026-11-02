import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableProtect
import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryInput
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual tag freshness and source node/tag lookup derive fresh Strong
registration for the whole mixed writable-leaf constructor resources. -/
theorem register {profileMode : ProfileMode} (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.ResourcesFor input protections selected head tail profileMode)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    ∃ held : GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.ResourcesFor input
      (protections.insert input.newTag .StrongProtector) selected head tail profileMode,
      held.component.support=raw.component.support := by
  apply GeneralBorrowExposedScopedInactiveWritableProtectedMutableProtect.protect input protections input.newTag selected head tail raw
  intro index node present same
  have mapped:=nodeTags index node present
  have absent : input.tree.tagMapping.get input.newTag=none := by
    simp only [UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
  rw [same,absent] at mapped
  cases mapped
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryInput
