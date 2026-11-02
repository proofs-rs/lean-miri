import duplicate_prefix.GeneralBorrowForestCopyBorrow
import duplicate_prefix.GeneralBorrowForestDefault

namespace DuplicatePrefix.GeneralBorrowForestAcceptedBorrow
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The accepted positive suffix's actual Default reborrow followed by adjacent
copy source Read and destination Write. Extra roots participate in all three
ranged accesses. Initial ownership, allocator and geometry suffice; no operation
success or intermediate ownership is supplied. Physical bytes/MIR return are
separate components. -/
theorem suffix (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len count : UInt64)
    (parentMode readMode writeMode : ChildrenVisitMode)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (twice : count.toNat+count.toNat ≤ len.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location protections parent primary extras))
      offset (offset+len) tree.locations) :
    let reborrow := GeneralBorrowForestDefault.child tree protections parentTag newTag offset len parentMode
    let read := reborrow.tree.performBorrowAccessRange (.concrete newTag) (Size.ofBytes offset) (Size.ofBytes count)
      .Read protections readMode
    let write := read.tree.performBorrowAccessRange (.concrete newTag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write protections writeMode
    (GeneralBorrowForestDefault.read tree protections parentTag offset len parentMode).status = .Completed ∧
    reborrow.outcome = .ok () ∧ read.status = .Completed ∧ write.status = .Completed ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data write.tree location protections
        (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) primary extras))
      offset (offset+len) write.tree.locations ∧
    write.tree.locations.WellFormed ∧ write.tree.locations.size = tree.locations.size ∧
    Nonempty (Context write.tree (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) primary extras) := by
  have constructed := GeneralBorrowForestDefault.run tree protections parentTag newTag parent primary extras offset len parentMode
    context covered parentTagPresent fresh slot fits nonzero well bounds before
  obtain ⟨nextContext⟩ := constructed.2.2.1
  have copied := GeneralBorrowForestCopyBorrow.accesses _ protections newTag
    (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) primary extras offset len count nextContext
    constructed.2.2.2.2.1 constructed.2.2.2.2.2.1 constructed.2.2.2.2.2.2.2.1
    (by rw [constructed.2.2.2.2.2.2.1];exact bounds) twice constructed.2.2.2.1 readMode writeMode
  exact ⟨constructed.1,constructed.2.1,copied.1,copied.2.1,copied.2.2.1,copied.2.2.2.1,
    copied.2.2.2.2.1.trans constructed.2.2.2.2.2.2.1,copied.2.2.2.2.2⟩

end DuplicatePrefix.GeneralBorrowForestAcceptedBorrow
