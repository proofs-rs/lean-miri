import duplicate_prefix.GeneralBorrowExposedScopedAncestorSharedProtect
import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorSharedProtectFresh
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedScopedAncestorSharedConstructor (Resources)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The allocator's actual tag-map freshness and NodeTags derive the Strong
registration adapter's node freshness. No final protection/resource guard. -/
theorem protect (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    ∃ next : Resources input (protections.insert input.newTag .StrongProtector) selected head tail writable,
      next.component.support=raw.component.support := by
  apply GeneralBorrowExposedScopedAncestorSharedProtect.protect input protections input.newTag selected head tail writable raw
  intro index node present same
  have mapped := nodeTags index node present
  have absent : input.tree.tagMapping.get input.newTag=none := by
    simp only [UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
  rw [same,absent] at mapped
  cases mapped
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorSharedProtectFresh
