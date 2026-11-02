import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafExpressionData
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafUniqueData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared GeneralBorrowExposedScopedSharedLeafConstructor
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Initial raw resources yield the exact Unique-leaf strengthening used to
preserve untouched future permission slots during actual ranged Reads. -/
theorem build (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowExposedScopedUniqueReadData.Data input.tree location protections
          input.parent selected head tail raw.component.support writable))
        input.offset (input.offset+input.len) input.tree.locations := by
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedSharedLeafExpressionData.build input protections selected head tail writable raw
  refine ⟨context,?_⟩
  intro position valid positive lower upper
  obtain ⟨data⟩ := owned position valid positive lower upper
  have short : input.tree.nodes.size < 65536 := by have room := raw.room;omega
  exact ⟨⟨data,short,raw.leaves,fun query included => raw.unique query included position valid⟩⟩
end DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafUniqueData
