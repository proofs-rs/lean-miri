import duplicate_prefix.GeneralBorrowPartitionDefaultStage
import duplicate_prefix.GeneralBorrowPartitionEntryData
import duplicate_prefix.GeneralBorrowFreshDefaultStages
import duplicate_prefix.GeneralBorrowFreshDefaultWithin
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultSlot

namespace DuplicatePrefix.GeneralBorrowDefaultActivation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The real reserved tree is the actual Default constructor result. -/
def reserved (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) : BorrowTree :=
  (GeneralBorrowPartitionDefault.operation tree parentTag tag offset len).tree

def write (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  (reserved tree parentTag tag offset len).performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len)
    .Write {} .VisitChildrenOfAccessed

/-- From an actual partial-range unprotected reservation, the real child-tag
Write completes and retains child Write ownership on that range. Structural,
lookup, selected slot, ownership and operation success are all derived from the
initial recurring State. No claim about subsequent parent accesses is a premise. -/
theorem activate (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) :
    (GeneralBorrowPartitionDefault.operation tree s.node.tag tag offset len).outcome = .ok () ∧
    (write tree s.node.tag tag offset len).status = .Completed ∧
    (∃ index, (reserved tree s.node.tag tag offset len).indexOfTag tag = some index ∧
      GeneralRangeMapOrigins.OwnedOn
        (GeneralBorrowRange.LocationOwned (write tree s.node.tag tag offset len).tree {} index .Write)
        offset (offset+len) (write tree s.node.tag tag offset len).tree.locations) ∧
    (write tree s.node.tag tag offset len).tree.locations.WellFormed ∧
    (write tree s.node.tag tag offset len).tree.locations.size = tree.locations.size := by
  let entry := GeneralBorrowPartitionEntryData.data tree root capacity s tag fresh
  let index := GeneralBorrowFreshMetadataChildDefaultSlot.index entry.slot
  have request : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact bounds
  have owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact s.owned position valid
  have clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none := by
    have vacant : tree.nodes.get index = none := by
      cases chosen : entry.slot with
      | append noFree aligned fits =>
        have empty := GeneralBorrowFreshDefaultStages.slot_vacant tree entry.depth root entry.slot
        simpa only [index,GeneralBorrowFreshMetadataChildDefaultSlot.index,GeneralBorrowFreshDefaultStages.slot_index,chosen] using empty
      | reuse candidate available bounded vacant slack =>
        simpa only [index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using vacant
    exact s.clean index vacant
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build tree entry.depth entry.children entry.covered
    s.node.tag tag root s.node (s.allocator.nodeTags root s.node s.star.present) s.star.present fresh entry.slot
    offset len nonzero s.well entry.nodeFits request
  have formed :
      (GeneralBorrowPartitionDefault.operation tree s.node.tag tag offset len).outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned (reserved tree s.node.tag tag offset len) {} index .Write)
        offset (offset+len) (reserved tree s.node.tag tag offset len).locations := by
    cases chosen : entry.slot with
    | append noFree aligned fits =>
      have child := GeneralBorrowFreshDefaultWithin.append tree entry.depth s.node.tag tag root s.node
        (s.allocator.nodeTags root s.node s.star.present) s.star.present fresh noFree aligned fits
        offset len nonzero s.well request {} owned (by simpa only [index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using clean)
      exact ⟨child.1,by simpa only [index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen,reserved,GeneralBorrowPartitionDefault.operation] using child.2.1⟩
    | reuse candidate available bounded vacant slack =>
      have child := GeneralBorrowFreshDefaultWithin.reuse tree entry.depth s.node.tag tag root s.node
        (s.allocator.nodeTags root s.node s.star.present) s.star.present fresh candidate available bounded vacant slack entry.nodeFits
        offset len nonzero s.well request {} owned (by simpa only [index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using clean)
      exact ⟨child.1,by simpa only [index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen,reserved,GeneralBorrowPartitionDefault.operation] using child.2.1⟩
  obtain ⟨node,present,tagged,exposed⟩ := metadata.node
  have nextRequest : offset.toNat+len.toNat ≤ (reserved tree s.node.tag tag offset len).locations.size.bytes.toNat := by
    rw [show (reserved tree s.node.tag tag offset len).locations.size = tree.locations.size from metadata.capacity]
    exact request
  have activated := GeneralBorrowRangeLocal.access (reserved tree s.node.tag tag offset len) {} tag index root
    (Size.ofBytes offset) (Size.ofBytes len) .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible)
    metadata.nodeFits metadata.certificates.depth metadata.certificates.children node present (metadata.roots.trans s.roots)
    metadata.certificates.covered metadata.lookup metadata.well offset (offset+len) formed.2 nextRequest (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨formed.1,activated.1,⟨index,metadata.lookup,activated.2.1⟩,activated.2.2.1,activated.2.2.2.trans metadata.capacity⟩
/-- The actual Read/reservation stage followed by the actual child-tag Write. -/
def stageWrite (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  (GeneralBorrowPartitionDefaultStage.operation tree parentTag tag offset len).tree.performNormalAccessRange tag
    (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed

/-- A full actual root Read, Default reservation, and child activation sequence.
The final ownership is at the child on its slice; the parent is not assumed to
retain a recurring root contract after activation. -/
theorem stage_activate (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) :
    (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).status = .Completed ∧
    (GeneralBorrowPartitionDefaultStage.operation tree s.node.tag tag offset len).outcome = .ok () ∧
    (stageWrite tree s.node.tag tag offset len).status = .Completed ∧
    (∃ index, (GeneralBorrowPartitionDefaultStage.operation tree s.node.tag tag offset len).tree.indexOfTag tag = some index ∧
      OwnedOn (GeneralBorrowRange.LocationOwned (stageWrite tree s.node.tag tag offset len).tree {} index .Write)
        offset (offset+len) (stageWrite tree s.node.tag tag offset len).tree.locations) ∧
    (stageWrite tree s.node.tag tag offset len).tree.locations.WellFormed ∧
    (stageWrite tree s.node.tag tag offset len).tree.locations.size = tree.locations.size := by
  have read := GeneralBorrowPartitionState.access tree root capacity s offset len .Read bounds
  obtain ⟨⟨prepared,tagged⟩⟩ := read.2.1
  have nextFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have activated := activate _ root capacity prepared offset len nonzero bounds tag nextFresh
  rw [tagged] at activated
  refine ⟨read.1,activated.1,activated.2.1,activated.2.2.1,activated.2.2.2.1,?_⟩
  have readCapacity : (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.locations.size = tree.locations.size :=
    prepared.capacity.trans s.capacity.symm
  exact activated.2.2.2.2.trans readCapacity

end
end DuplicatePrefix.GeneralBorrowDefaultActivation
