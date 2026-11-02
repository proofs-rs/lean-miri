import duplicate_prefix.GeneralBorrowExposedScopedWritableMutableEntryInput
import duplicate_prefix.GeneralBorrowExposedScopedWritableProtectedMutableData
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem registered (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources input protections selected head tail)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedWritableReadData.Data
        input.tree location (protections.insert input.newTag .StrongProtector) input.parent selected head tail
        raw.component.support (fun _=>true))) input.offset (input.offset+input.len) input.tree.locations := by
  obtain ⟨held,support⟩:=GeneralBorrowExposedScopedWritableMutableEntryInput.register input protections selected head tail raw nodeTags
  obtain ⟨context,owned⟩:=GeneralBorrowExposedScopedWritableProtectedMutableData.build input
    (protections.insert input.newTag .StrongProtector) selected head tail held
  exact ⟨context,by simpa only [support] using owned⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryData
