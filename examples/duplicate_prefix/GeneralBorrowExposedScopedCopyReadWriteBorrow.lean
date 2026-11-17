import duplicate_prefix.GeneralBorrowExposedScopedUniqueReadWrite
import duplicate_prefix.GeneralBorrowExposedScopedUniqueReadRange
import duplicate_prefix.GeneralBorrowExposedScopedLeafWriteReadRange
import duplicate_prefix.GeneralBorrowForestCopyBorrow

namespace DuplicatePrefix.GeneralBorrowExposedScopedCopyReadWriteBorrow
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowExposedKnownRootRangeData (Context)
open GeneralBorrowExposedScopedUniqueReadData (Data)
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Adjacent nonoverlapping source Read and destination Write on an arbitrary
multiple-root forest with a hidden all-writable component and exposed Unique
leaves. Both completions, final Write profile and geometry are derived from
initial strengthened Read data; the two visitors may use independent modes.
The full raw next-Write data, including selected ownership, is retained. -/
theorem accesses (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor selected head : UniIndex) (tail : List UniIndex) (offset sliceLen count : UInt64)
    (context : Context tree anchor selected head tail)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed) (fits : tree.nodes.data.size ≤ 4294967296)
    (bounds : offset.toNat+sliceLen.toNat ≤ tree.locations.size.bytes.toNat)
    (twice : count.toNat+count.toNat ≤ sliceLen.toNat)
    (support : Nat → Prop)
    (owned : OwnedOn (fun location => Nonempty (Data tree location protections anchor selected head tail support (fun _=>true)))
      offset (offset+sliceLen) tree.locations)
    (readMode writeMode : ChildrenVisitMode) :
    let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
      .Read protections readMode
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write protections writeMode
    read.status = .Completed ∧ write.status = .Completed ∧
      OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data write.tree location protections anchor selected head tail))
        offset (offset+sliceLen) write.tree.locations ∧
      write.tree.locations.WellFormed ∧ write.tree.locations.size = tree.locations.size ∧
      Nonempty (Context write.tree anchor selected head tail) := by
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read protections readMode
  let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
    .Write protections writeMode
  have ranges := GeneralBorrowForestCopyBorrow.arithmetic offset sliceLen count tree.locations.size.bytes bounds twice
  have first := GeneralBorrowExposedScopedUniqueReadRange.access tree protections tag anchor selected head tail
    (Size.ofBytes offset) (Size.ofBytes count) readMode context support (fun _=>true) fits tagPresent well
    offset (offset+sliceLen) owned ranges.1 (Nat.le_refl _) ranges.2.2.2.1
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read protections readMode
  change read.tree = {tree with locations := read.tree.locations} at frame
  have nextContext : Context read.tree anchor selected head tail := by
    rw [frame]
    exact ⟨context.anchorNode,context.selectedNode,context.anchorPresent,context.selectedPresent,context.roots,context.depth,context.children,context.tags⟩
  have nextTag : read.tree.indexOfTag tag = some anchor := by rw [frame];exact tagPresent
  have nextFits : read.tree.nodes.data.size ≤ 4294967296 := by rw [frame];exact fits
  have writeOwned : OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data read.tree location protections anchor selected head tail))
      offset (offset+sliceLen) read.tree.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩ := first.2.1 position valid positive lower upper
    exact ⟨GeneralBorrowExposedScopedLeafWriteReadClosed.initial read.tree _ protections anchor selected head tail support nextContext data⟩
  have second := GeneralBorrowExposedScopedLeafWriteReadRange.access read.tree protections tag anchor selected head tail
    (Size.ofBytes (offset+count)) (Size.ofBytes count) writeMode nextContext nextFits nextTag first.2.2.1
    offset (offset+sliceLen) writeOwned (by rw [first.2.2.2];exact ranges.2.1)
    ranges.2.2.1 ranges.2.2.2.2
  have writeFrame := GeneralBorrowFreshReadFrame.frame read.tree (.concrete tag) (Size.ofBytes (offset+count))
    (Size.ofBytes count) .Write protections writeMode
  change write.tree = {read.tree with locations := write.tree.locations} at writeFrame
  refine ⟨first.1,second.1,second.2.1,second.2.2.1,second.2.2.2.trans first.2.2.2,?_⟩
  rw [writeFrame]
  exact ⟨⟨nextContext.anchorNode,nextContext.selectedNode,nextContext.anchorPresent,nextContext.selectedPresent,nextContext.roots,nextContext.depth,nextContext.children,nextContext.tags⟩⟩

end DuplicatePrefix.GeneralBorrowExposedScopedCopyReadWriteBorrow
