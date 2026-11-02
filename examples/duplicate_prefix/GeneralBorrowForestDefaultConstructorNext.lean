import duplicate_prefix.GeneralBorrowForestForeignWriteNextLocation
import duplicate_prefix.GeneralBorrowFreshDefaultSlotOther
import duplicate_prefix.GeneralBorrowFreshDefaultSlotPaths
import duplicate_prefix.GeneralBorrowFreshDefaultSlotFlags

namespace DuplicatePrefix.GeneralBorrowForestDefaultConstructorNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowForestForeignAccess (LocationData)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Certificate transport for an ACTUAL shared constructor's next location.
The actual append/reuse rules derive all support-presence/child-closure,
ancestor-path, root-path and unexposed fields. The remaining range-stage
certificates are the fresh child's separately derived ownership and a
same-origin cache equality. This is a composition helper, not a final
whole-operation theorem assuming its result ownership. -/
theorem next (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent primary : UniIndex) (parentNode : TreeNode) (extras : List UniIndex)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (initial final : LocationTree) (protections : ProtectedTags)
    (data : LocationData tree initial protections parent primary extras .Write)
    (unexposed : GeneralBorrowFreshDefaultSlotFlags.Unexposed tree)
    (newOwner : GeneralBorrowRange.LocationOwned
      (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) protections
      (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) .Write final)
    (cache : final.exposedCache = initial.exposedCache) :
    ∃ next : LocationData (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len)
      final protections (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) primary extras .Write, next.region.support = data.region.support := by
  have attach := GeneralBorrowFreshDefaultSlotPaths.attach tree depth children covered parentTag newTag parent parentNode
    parentTagPresent parentPresent fresh slot offset len nonzero well bounds initial final protections data.forest
  have vacancy : ∀ query node, tree.nodeAt query = some node → query ≠ GeneralBorrowFreshMetadataChildDefaultSlot.index slot := by
    intro query node present
    cases slot with
    | append noFree aligned fits =>
      intro equal
      have bounded := (array_of_node tree query node present).1
      have indexValue : (GeneralBorrowFreshMetadataChildDefaultSlot.index (Slot.append noFree aligned fits : Slot tree depth parent)).toNat = tree.nodes.data.size := by
        dsimp only [GeneralBorrowFreshMetadataChildDefaultSlot.index,UniIndex.toNat]
        rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
        exact aligned
      rw [equal,indexValue] at bounded
      omega
    | reuse index available bounded vacant slack =>
      intro equal
      change tree.nodes.get query = some node at present
      change query = index at equal
      rw [equal,vacant] at present
      cases present
  have otherNodes : ∀ query oldNode, tree.nodeAt query = some oldNode → query ≠ parent →
      ∃ next, (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len).nodeAt query = some next ∧
        next.children = oldNode.children := by
    intro query oldNode present notParent
    obtain ⟨next,lookup,tag,parentEq,childrenEq,permission,flag⟩ := GeneralBorrowFreshDefaultSlotOther.of_slot
      tree depth children covered parentTag newTag parent parentNode parentTagPresent parentPresent fresh slot
      offset len nonzero well bounds query oldNode present notParent
    exact ⟨next,lookup,childrenEq⟩
  exact GeneralBorrowForestForeignWriteNextLocation.attach_location tree _ initial final protections parent _ primary extras data newOwner
    attach.childPath vacancy otherNodes
    (GeneralBorrowFreshDefaultSlotFlags.of_slot tree depth children covered parentTag newTag parent parentNode
      parentTagPresent parentPresent fresh slot offset len nonzero well bounds unexposed) cache

end DuplicatePrefix.GeneralBorrowForestDefaultConstructorNext
