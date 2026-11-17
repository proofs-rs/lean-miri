import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableTagHidden
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildMutable
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Initial graph/tag lookup and real mutable attachment identify every node
carrying the new helper tag with the freshly created hidden child. -/
theorem hidden (input : Input)
    (nodeTags : ∀ index node,input.tree.nodeAt index=some node → input.tree.indexOfTag node.tag=some index)
    (query : UniIndex) (node : TreeNode) (present : (result input).nodeAt query=some node)
    (tag : node.tag=input.newTag) : node.isExposed=false := by
  have staged := GeneralBorrowSharedAllocatorInvariant.staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned
    (locations input) input.parentPresent input.fresh nodeTags
  have coherent : GeneralBorrowGcAllocator.NodeTags (stage input) := by
    simpa only [stage,mapping] using staged
  have tags := GeneralBorrowSharedAllocatorInvariant.shape_tags (stage input) (result input) (shape input) coherent
  let metadata := GeneralBorrowFreshMetadataChildMutable.append input
  have lookup := tags query node present
  change (result input).indexOfTag node.tag=some query at lookup
  rw [tag,metadata.freshLookup] at lookup
  have same : query=index input := (Option.some.inj lookup).symm
  subst query
  obtain ⟨fresh,presentFresh,_,_,_,_,hidden⟩ := metadata.newNode
  have equal : node=fresh := Option.some.inj (present.symm.trans presentFresh)
  rw [equal]
  exact hidden
end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableTagHidden
