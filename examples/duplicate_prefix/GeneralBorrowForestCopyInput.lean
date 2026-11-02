import duplicate_prefix.GeneralBorrowForestCopyBorrow
namespace DuplicatePrefix.GeneralBorrowForestCopyInput
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false in
structure Input (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset sliceLen count : UInt64) where
  anchor : UniIndex
  primary : UniIndex
  extras : List UniIndex
  context : GeneralBorrowForestAccessData.Context tree anchor primary extras
  fits : tree.nodes.data.size ≤ 4294967296
  covered : GeneralBorrowGraph.RootsCover tree
  tagPresent : tree.indexOfTag tag = some anchor
  well : tree.locations.WellFormed
  bounds : offset.toNat+sliceLen.toNat ≤ tree.locations.size.bytes.toNat
  twice : count.toNat+count.toNat ≤ sliceLen.toNat
  owned : GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location protections anchor primary extras))
    offset (offset+sliceLen) tree.locations

/-- Compatibility projection of the full forest next-input theorem for MIR
copy clients; the source Input still requires both cache-kind forest records. -/
theorem accesses (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset sliceLen count : UInt64) (input : Input tree protections tag offset sliceLen count) :
    let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
      .Read protections .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned write.tree protections input.anchor .Write)
        offset (offset+sliceLen) write.tree.locations ∧
      write.tree.locations.WellFormed ∧ write.tree.locations.size = tree.locations.size := by
  have good := GeneralBorrowForestCopyBorrow.accesses tree protections tag input.anchor input.primary input.extras
    offset sliceLen count input.context input.tagPresent input.well input.fits input.bounds input.twice input.owned
    .VisitChildrenOfAccessed .VisitChildrenOfAccessed
  refine ⟨good.1,good.2.1,?_,good.2.2.2.1,good.2.2.2.2.1⟩
  intro position valid positive lower upper
  obtain ⟨data⟩ := good.2.2.1 position valid positive lower upper
  exact ⟨⟨data.base.forest⟩,data.base.owned⟩
end DuplicatePrefix.GeneralBorrowForestCopyInput
