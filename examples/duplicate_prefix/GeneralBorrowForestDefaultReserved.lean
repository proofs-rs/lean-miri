import duplicate_prefix.GeneralBorrowForestDefault
import duplicate_prefix.GeneralBorrowDefaultReservationSlice
import duplicate_prefix.GeneralBorrowForestMutableSlice
import duplicate_prefix.GeneralBorrowFreshReadFrame

namespace DuplicatePrefix.GeneralBorrowForestDefaultReserved
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

open GeneralBorrowForestDefault (read child)

/-- Actual Read/Default reservation installs stored ReservedFrz(false) on
its selected slice, without requiring initial vacant-slot permissions Clean. -/
theorem formed (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location protections parent primary extras))
      offset (offset+len) tree.locations) :
    GeneralRangeMapOrigins.OwnedOn (GeneralBorrowDefaultReservationSlice.Reserved (GeneralBorrowFreshMetadataChildDefaultSlot.index slot))
      offset (offset+len) (child tree protections parentTag newTag offset len mode).tree.locations := by
  have good := GeneralBorrowForestMutableSlice.access tree protections parentTag parent primary extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read mode context parentTagPresent well fits offset (offset+len) before bounds
    (Nat.le_refl _) (Nat.le_refl _)
  let accessed := read tree protections parentTag offset len mode
  change accessed.status = .Completed ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data accessed.tree location protections parent primary extras))
      offset (offset+len) accessed.tree.locations ∧
    accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes context.depth
  let nextContext : Context accessed.tree parent primary extras := {
    anchorNode := context.anchorNode
    primaryNode := context.primaryNode
    depth := depth
    children := by rw [frame];exact context.children
    anchorPresent := by change accessed.tree.nodes.get parent = _;rw [nodes];exact context.anchorPresent
    primaryPresent := by rw [nodes];exact context.primaryPresent
    roots := by rw [frame];exact context.roots
    different := context.different
    unexposed := by intro index node present;rw [nodes] at present;exact context.unexposed index node present }
  have nextCovered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [frame];exact covered
  have nextTag : accessed.tree.indexOfTag parentTag = some parent := by rw [frame];exact parentTagPresent
  have nextFresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact fresh
  let nextSlot := GeneralBorrowFreshMetadataChildDefaultSlot.transport tree accessed.tree context.depth depth nodes mapping rfl parent slot
  have slotEq : GeneralBorrowFreshMetadataChildDefaultSlot.index nextSlot = GeneralBorrowFreshMetadataChildDefaultSlot.index slot :=
    GeneralBorrowFreshMetadataChildDefaultSlot.transport_index tree accessed.tree context.depth depth nodes mapping rfl parent slot
  have nextFits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact fits
  have nextBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  have typed := GeneralBorrowDefaultReservationSlice.formed accessed.tree depth nextContext.children nextCovered parentTag newTag parent context.anchorNode
    nextTag nextContext.anchorPresent nextFresh nextSlot offset len nonzero good.2.2.1 nextBounds
  simpa only [slotEq,child,accessed,GeneralBorrowFreshMetadataChildDefaultSlot.result] using typed

end DuplicatePrefix.GeneralBorrowForestDefaultReserved
