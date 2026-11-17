import duplicate_prefix.GeneralBorrowForestMutableSlice
import duplicate_prefix.GeneralBorrowForestForeignSliceRepeated

namespace DuplicatePrefix.GeneralBorrowForestCopyBorrow
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestMutableAccess (Data)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem arithmetic (offset len count capacity : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (twice : count.toNat+count.toNat ≤ len.toNat) :
    offset.toNat+count.toNat ≤ capacity.toNat ∧
    (offset+count).toNat+count.toNat ≤ capacity.toNat ∧
    offset.toNat ≤ (offset+count).toNat ∧
    (offset+count).toNat ≤ (offset+len).toNat ∧
    ((offset+count)+count).toNat ≤ (offset+len).toNat := by
  have capacityFits : capacity.toNat < 2^64 := UInt64.toNat_lt_size capacity
  have fullFits : offset.toNat+len.toNat < 2^64 := by omega
  have firstFits : offset.toNat+count.toNat < 2^64 := by omega
  have secondFits : offset.toNat+count.toNat+count.toNat < 2^64 := by omega
  simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits,Nat.mod_eq_of_lt firstFits,Nat.mod_eq_of_lt secondFits]
  omega

/-- Adjacent nonoverlapping source Read and destination Write on an arbitrary
multiple-root forest, retaining full mutable and both cache-kind records over
the original slice. The two actual visitors may choose independent modes. -/
theorem accesses (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor primary : UniIndex) (extras : List UniIndex) (offset sliceLen count : UInt64)
    (context : Context tree anchor primary extras)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed) (fits : tree.nodes.data.size ≤ 4294967296)
    (bounds : offset.toNat+sliceLen.toNat ≤ tree.locations.size.bytes.toNat)
    (twice : count.toNat+count.toNat ≤ sliceLen.toNat)
    (owned : OwnedOn (fun location => Nonempty (Data tree location protections anchor primary extras))
      offset (offset+sliceLen) tree.locations)
    (readMode writeMode : ChildrenVisitMode) :
    let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
      .Read protections readMode
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write protections writeMode
    read.status = .Completed ∧ write.status = .Completed ∧
      OwnedOn (fun location => Nonempty (Data write.tree location protections anchor primary extras))
        offset (offset+sliceLen) write.tree.locations ∧
      write.tree.locations.WellFormed ∧ write.tree.locations.size = tree.locations.size ∧
      Nonempty (Context write.tree anchor primary extras) := by
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read protections readMode
  let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
    .Write protections writeMode
  have ranges := arithmetic offset sliceLen count tree.locations.size.bytes bounds twice
  have first := GeneralBorrowForestMutableSlice.access tree protections tag anchor primary extras
    (Size.ofBytes offset) (Size.ofBytes count) .Read readMode context tagPresent well fits
    offset (offset+sliceLen) owned ranges.1 (Nat.le_refl _) ranges.2.2.2.1
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read protections readMode
  change read.tree = {tree with locations := read.tree.locations} at frame
  have nextContext : Context read.tree anchor primary extras := by
    rw [frame]
    exact GeneralBorrowForestForeignSliceRepeated.context_on_map tree _ anchor primary extras context
  have nextTag : read.tree.indexOfTag tag = some anchor := by rw [frame];exact tagPresent
  have nextFits : read.tree.nodes.data.size ≤ 4294967296 := by rw [frame];exact fits
  have second := GeneralBorrowForestMutableSlice.access read.tree protections tag anchor primary extras
    (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write writeMode nextContext nextTag first.2.2.1 nextFits
    offset (offset+sliceLen) first.2.1 (by rw [first.2.2.2];exact ranges.2.1)
    ranges.2.2.1 ranges.2.2.2.2
  have writeFrame := GeneralBorrowFreshReadFrame.frame read.tree (.concrete tag) (Size.ofBytes (offset+count))
    (Size.ofBytes count) .Write protections writeMode
  change write.tree = {read.tree with locations := write.tree.locations} at writeFrame
  refine ⟨first.1,second.1,second.2.1,second.2.2.1,second.2.2.2.trans first.2.2.2,?_⟩
  rw [writeFrame]
  exact ⟨GeneralBorrowForestForeignSliceRepeated.context_on_map read.tree _ anchor primary extras nextContext⟩

end DuplicatePrefix.GeneralBorrowForestCopyBorrow
