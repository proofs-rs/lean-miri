import duplicate_prefix.GeneralBorrowExposedScopedAncestorDefaultProtect
import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorDefaultProtectFresh
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedScopedAncestorDefaultConstructor (Resources)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The allocator's actual tag-map freshness and NodeTags derive the Strong
registration adapter's node freshness. No final protection/resource guard. -/
theorem protect (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    ∃ next : Resources input (protections.insert input.newTag .StrongProtector) selected head tail,
      next.component.support=raw.component.support := by
  apply GeneralBorrowExposedScopedAncestorDefaultProtect.protect input protections input.newTag selected head tail raw
  intro index node present same
  have mapped := nodeTags index node present
  have absent : input.tree.tagMapping.get input.newTag=none := by
    simp only [UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
  rw [same,absent] at mapped
  cases mapped
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorDefaultProtectFresh
