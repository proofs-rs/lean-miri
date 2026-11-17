import duplicate_prefix.GeneralBorrowFreshConstructor
import duplicate_prefix.GeneralBorrowFreshReuseConstructor
import duplicate_prefix.GeneralBorrowFreshReborrowStages
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableSlot

namespace DuplicatePrefix.GeneralBorrowFreshProtectedSlotOwned
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Either actual allocator branch installs the fresh Default child's Write
ownership. Parent ownership is initial data; both success and fresh ownership
are conclusions. Vacant slots may carry arbitrary old permissions because the
constructor overwrites its selected inside range. -/
theorem owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : Slot tree depth parent) (fits : tree.nodes.data.size ≤ 4294967296)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags)
    (before : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    result.outcome = .ok () ∧
      GeneralRangeMapOrigins.OwnedOn
        (GeneralBorrowRange.LocationOwned result.tree protections (GeneralBorrowFreshMetadataChildMutableSlot.index slot) .Write)
        offset (offset+len) result.tree.locations := by
  cases slot with
  | append noFree aligned indexFits =>
    exact GeneralBorrowFreshConstructor.mutable_owned tree depth parentTag newTag parent parentNode
      parentTagPresent parentPresent fresh noFree aligned indexFits offset len nonzero well bounds protections .Write before
  | reuse index available bounded vacant slack =>
    exact GeneralBorrowFreshReuseConstructor.mutable_owned tree depth parentTag newTag parent parentNode
      parentTagPresent parentPresent fresh index available bounded vacant slack fits offset len nonzero well bounds protections .Write before

end DuplicatePrefix.GeneralBorrowFreshProtectedSlotOwned
