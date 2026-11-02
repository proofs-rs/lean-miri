import duplicate_prefix.GeneralBorrowForestForeignShared
import duplicate_prefix.GeneralBorrowFreshSharedSlotResources

namespace DuplicatePrefix.GeneralBorrowForestForeignSharedResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestForeignAccess (LocationData)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshReadFrame
open GeneralBorrowForestForeignShared (read child)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual Read/constructor postmetadata needed to repeat a shared operation.
It includes allocator consistency, geometry, root coverage, new concrete tag
lookup and node growth≤1. Initial allocator/borrow records derive everything;
there is no intermediate-state or successful-operation premise. -/
theorem preserves (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (allocator : GeneralBorrowGcAllocator.Invariant tree)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (LocationData tree location protections parent primary extras .Read))
      offset (offset+len) tree.locations) :
    let after := (child tree protections parentTag newTag isProtected offset len mode).tree
    GeneralBorrowGcAllocator.Invariant after ∧ after.locations.WellFormed ∧
      after.locations.size = tree.locations.size ∧ after.nodes.size ≤ tree.nodes.size+1 ∧
      GeneralBorrowGraph.RootsCover after ∧ after.indexOfTag newTag = some (GeneralBorrowFreshMetadataChildSlot.index slot) := by
  have good := GeneralBorrowForestForeignSlice.access tree protections parentTag parent primary extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read mode context parentTagPresent well fits offset (offset+len) before bounds
    (Nat.le_refl _) (Nat.le_refl _)
  let accessed := read tree protections parentTag offset len mode
  change accessed.status = .Completed ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (LocationData accessed.tree location protections parent primary extras .Read))
      offset (offset+len) accessed.tree.locations ∧
    accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes context.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [frame];exact context.children
  have coverage : GeneralBorrowGraph.RootsCover accessed.tree := by rw [frame];exact covered
  have present : accessed.tree.nodeAt parent = some context.anchorNode := by
    change accessed.tree.nodes.get parent = _
    rw [nodes]
    exact context.anchorPresent
  have tag : accessed.tree.indexOfTag parentTag = some parent := by rw [frame];exact parentTagPresent
  have nextFresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact fresh
  have nextAllocator : GeneralBorrowGcAllocator.Invariant accessed.tree := by
    rw [frame]
    exact ⟨allocator.pool,allocator.accounting,allocator.unique,allocator.nodeTags⟩
  let nextSlot := GeneralBorrowFreshMetadataChildSlot.transport tree accessed.tree context.depth depth nodes mapping rfl parent slot
  have slotEq : GeneralBorrowFreshMetadataChildSlot.index nextSlot = GeneralBorrowFreshMetadataChildSlot.index slot :=
    GeneralBorrowFreshMetadataChildSlot.transport_index tree accessed.tree context.depth depth nodes mapping rfl parent slot
  have nextBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  have facts := GeneralBorrowFreshSharedSlotResources.preserves accessed.tree depth children coverage parentTag newTag parent context.anchorNode
    tag present nextFresh nextSlot isProtected offset len nonzero good.2.2.1 nextBounds nextAllocator
  let metadata := GeneralBorrowFreshMetadataChildSlot.build accessed.tree depth children coverage parentTag newTag parent context.anchorNode
    tag present nextFresh nextSlot isProtected offset len nonzero good.2.2.1 nextBounds
  have lookup : (child tree protections parentTag newTag isProtected offset len mode).tree.indexOfTag newTag =
      some (GeneralBorrowFreshMetadataChildSlot.index slot) := by
    simpa only [slotEq,child,accessed,GeneralBorrowFreshMetadataChildSlot.result] using metadata.lookup
  have count : (child tree protections parentTag newTag isProtected offset len mode).tree.nodes.size ≤ tree.nodes.size+1 := by
    have bounded := facts.2.2.2
    rw [nodes] at bounded
    exact bounded
  exact ⟨facts.1,facts.2.1,facts.2.2.1.trans good.2.2.2,count,metadata.certificates.covered,lookup⟩

end DuplicatePrefix.GeneralBorrowForestForeignSharedResources
