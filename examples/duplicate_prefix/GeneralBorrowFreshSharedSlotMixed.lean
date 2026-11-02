import duplicate_prefix.GeneralBorrowFreshMixedConstructor
import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot

namespace DuplicatePrefix.GeneralBorrowFreshSharedSlotMixed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshReleaseMixed (Combined)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual append/reuse shared installation retains old writable labels while
marking only the fresh Frozen child read-only. This does not infer mutable
ownership from the child's Read contract. -/
theorem owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (writable : Nat → Bool)
    (before : GeneralRangeMapOrigins.OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations) :
    let after := GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len
    GeneralRangeMapOrigins.OwnedOn
      (Combined after protections (GeneralBorrowFreshMetadataChildSlot.index slot)
        (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildSlot.index slot).toNat))
      offset (offset+len) after.locations := by
  cases slot with
  | append noFree aligned indexFits =>
    exact (GeneralBorrowFreshMixedConstructor.append_owned tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
      fresh noFree aligned indexFits isProtected offset len nonzero well bounds protections writable before).2
  | reuse index available bounded vacant slack =>
    exact (GeneralBorrowFreshMixedConstructor.reuse_owned tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
      fresh index available bounded vacant slack fits isProtected offset len nonzero well bounds protections writable before).2

end DuplicatePrefix.GeneralBorrowFreshSharedSlotMixed
