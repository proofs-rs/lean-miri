import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafProtect
import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafExpressionData
namespace DuplicatePrefix.GeneralBorrowExposedScopedMutableEntryData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Tag allocator freshness and the actual graph-tag lookup invariant discharge
Strong registration and form the complete initial protected parent Read data. -/
theorem registered (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources input protections selected head tail)
    (nodeTags : ∀ index node,input.tree.nodeAt index = some node → input.tree.indexOfTag node.tag = some index) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowExposedScopedMixedRangeData.Data input.tree location
          (protections.insert input.newTag .StrongProtector) input.parent selected head tail raw.component.support (fun _=>true)))
        input.offset (input.offset+input.len) input.tree.locations := by
  have absent : input.tree.indexOfTag input.newTag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
  obtain ⟨held,support⟩ := GeneralBorrowExposedScopedDefaultLeafProtect.protect input protections input.newTag selected head tail raw (by
    intro index node present equal
    have mapped := nodeTags index node present
    rw [equal,absent] at mapped
    cases mapped)
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedDefaultLeafExpressionData.build input
    (protections.insert input.newTag .StrongProtector) selected head tail held
  exact ⟨context,by simpa only [support] using owned⟩
end DuplicatePrefix.GeneralBorrowExposedScopedMutableEntryData
