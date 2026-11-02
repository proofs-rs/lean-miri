import duplicate_prefix.GeneralBorrowExposedScopedWritableCopyReadWriteBorrow
namespace DuplicatePrefix.GeneralBorrowScopedWritableCopyInput
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option autoImplicit false in
/-- Raw source graph/effective writable-leaf ownership for the real scoped copy helper.
No memory, callback or interpreter operation-success certificate is a field. -/
structure Input (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset sliceLen count : UInt64) where
  anchor : UniIndex
  selected : UniIndex
  head : UniIndex
  tail : List UniIndex
  context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail
  fits : tree.nodes.data.size≤4294967296
  covered : GeneralBorrowGraph.RootsCover tree
  tagPresent : tree.indexOfTag tag=some anchor
  well : tree.locations.WellFormed
  bounds : offset.toNat+sliceLen.toNat≤tree.locations.size.bytes.toNat
  twice : count.toNat+count.toNat≤sliceLen.toNat
  support : Nat→Prop
  owned : GeneralRangeMapOrigins.OwnedOn
    (fun location=>Nonempty (GeneralBorrowExposedScopedWritableReadData.Data tree location protections anchor selected head tail support (fun _=>true)))
    offset (offset+sliceLen) tree.locations

theorem accesses (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset sliceLen count : UInt64) (input : Input tree protections tag offset sliceLen count) :
    let read:=tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
    let write:=read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed
    read.status=.Completed ∧ write.status=.Completed ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data write.tree location protections input.anchor input.selected input.head input.tail))
      offset (offset+sliceLen) write.tree.locations ∧
    write.tree.locations.WellFormed ∧ write.tree.locations.size=tree.locations.size := by
  have good:=GeneralBorrowExposedScopedWritableCopyReadWriteBorrow.accesses tree protections tag input.anchor input.selected input.head input.tail
    offset sliceLen count input.context input.tagPresent input.well input.fits input.bounds input.twice input.support input.owned
    .VisitChildrenOfAccessed .VisitChildrenOfAccessed
  exact ⟨good.1,good.2.1,good.2.2.1,good.2.2.2.1,good.2.2.2.2.1⟩
end DuplicatePrefix.GeneralBorrowScopedWritableCopyInput
