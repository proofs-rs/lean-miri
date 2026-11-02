import duplicate_prefix.GeneralRootDefaultMetadata
import duplicate_prefix.GeneralBorrowForestAsMutDefaultResources
import duplicate_prefix.GeneralRootDefaultCleanSlot
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultOld
import duplicate_prefix.GeneralBorrowFreshDefaultPathData
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowSharedRootMutableReservation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages GeneralRangeMapOrigins GeneralRangeMapState
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowFreshDefaultSequence
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure Output (tree : BorrowTree) (tag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree tag parent offset len) where
  metadata : GeneralRootDefaultMetadata.Output tree tag parent {} offset len data
  allocator : GeneralBorrowGcAllocator.Invariant (child data {}).tree
  clean : GeneralBorrowGcVacantClean.VacantClean (child data {}).tree
  size : (child data {}).tree.nodes.size ≤ tree.nodes.size+1
  oldNode : ∀ query node, tree.nodeAt query = some node →
    ∃ next, (child data {}).tree.nodeAt query = some next ∧ next.tag=node.tag ∧ next.isExposed=node.isExposed
  oldLookup : ∀ future, tag≠future → (child data {}).tree.indexOfTag future = tree.indexOfTag future
  attach : ∀ location, GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree location {}).topology
    (source_normal_projection (child data {}).tree location {}).topology parent.toNat (index data).toNat

/-- Real leading Read and actual Default constructor preserve coherent pools,
all vacant-slot cleanliness and root/child topology without restricting exposed
flags. Permissions are required only on the requested positive window. -/
def build (tree : BorrowTree) (tag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree tag parent offset len)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} parent .Write) offset (offset+len) tree.locations)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    Output tree tag parent offset len data := by
  let accessed := read data {}
  have good := GeneralBorrowRangeLocal.access tree {} data.parentTag parent data.root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) data.nodeFits data.depth data.children data.parentNode data.parentPresent
    data.roots data.covered data.parentTagPresent data.well offset (offset+len) owned data.bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ OwnedOn (GeneralBorrowRange.LocationOwned accessed.tree {} parent .Write) offset (offset+len) accessed.tree.locations ∧
    accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read {} .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes=tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping=tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [frame];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [frame];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent=some data.parentNode := by change accessed.tree.nodes.get parent=_;rw[nodes];exact data.parentPresent
  have parentTag : accessed.tree.indexOfTag data.parentTag=some parent := by rw[frame];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tag := by rw[mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size≤4294967296 := by rw[nodes];exact data.nodeFits
  have bounds : offset.toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat := by rw[good.2.2.2];exact data.bounds
  let slot := GeneralBorrowFreshMetadataChildDefaultSlot.transport tree accessed.tree data.depth depth nodes mapping rfl parent data.slot
  have slotIndex : GeneralBorrowFreshMetadataChildDefaultSlot.index slot=index data := by
    rw [GeneralBorrowFreshMetadataChildDefaultSlot.transport_index]
    unfold index;cases data.slot <;> rfl
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build accessed.tree depth children covered data.parentTag tag parent data.parentNode
    parentTag parentPresent fresh slot offset len data.nonzero good.2.2.1 fits bounds
  have readAllocator : GeneralBorrowGcAllocator.Invariant accessed.tree := by rw[frame];exact ⟨allocator.pool,allocator.accounting,allocator.unique,allocator.nodeTags⟩
  have resources := GeneralBorrowForestAsMutDefaultResources.preserves accessed.tree depth children covered data.parentTag tag parent data.parentNode
    parentTag parentPresent fresh slot offset len data.nonzero good.2.2.1 bounds readAllocator
  have cleanAfter : GeneralBorrowGcVacantClean.VacantClean (child data {}).tree := by
    intro query vacant
    have different : query≠GeneralBorrowFreshMetadataChildDefaultSlot.index slot := by
      intro same
      obtain ⟨node,present,_,_⟩:=metadata.node
      rw[same] at vacant
      change (GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree data.parentTag tag offset len).nodeAt _=none at vacant
      rw[present] at vacant;cases vacant
    have oldVacant : accessed.tree.nodes.get query=none := by
      cases old : accessed.tree.nodes.get query with
      | none => rfl
      | some node =>
        obtain ⟨next,present,_,_⟩:=GeneralBorrowFreshMetadataChildDefaultOld.of_slot accessed.tree depth children covered data.parentTag tag parent data.parentNode
          parentTag parentPresent fresh slot offset len data.nonzero good.2.2.1 bounds query node old
        change (GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree data.parentTag tag offset len).nodeAt query=none at vacant
        rw[vacant] at present;cases present
    have initialVacant : tree.nodes.get query=none := by rw[nodes] at oldVacant;exact oldVacant
    have readClean := GeneralBorrowFreshActiveOnRange.ranged tree {} data.parentTag parent data.root query (Size.ofBytes offset) (Size.ofBytes len)
      .Read .Write .VisitChildrenOfAccessed (fun _=>rfl) data.depth data.children data.parentNode data.parentPresent data.roots data.covered data.parentTagPresent
      initialVacant (clean query initialVacant) data.well offset (offset+len) owned data.bounds (Nat.le_refl _) (Nat.le_refl _)
    exact GeneralRootDefaultCleanSlot.mutable_slot accessed.tree depth children covered data.parentTag tag parent data.parentNode
      parentTag parentPresent fresh slot offset len data.nonzero good.2.2.1 bounds query different readClean.2
  refine {
    metadata:=GeneralRootDefaultMetadata.build tree tag parent {} offset len data.nonzero data data.bounds owned,
    allocator:=resources.1,clean:=cleanAfter,size:=?_,oldNode:=?_,oldLookup:=?_,attach:=?_ }
  · have size:=resources.2.2.2
    rw[nodes] at size
    exact size
  · intro query node present
    have presentAfter : accessed.tree.nodeAt query=some node := by change accessed.tree.nodes.get query=_;rw[nodes];exact present
    exact GeneralBorrowFreshMetadataChildDefaultOld.of_slot accessed.tree depth children covered data.parentTag tag parent data.parentNode
      parentTag parentPresent fresh slot offset len data.nonzero good.2.2.1 bounds query node presentAfter
  · intro future different
    exact (metadata.oldLookup future different).trans (by rw[frame];rfl)
  · intro location
    have topology := GeneralBorrowFreshMetadataChildAllocator.topology_frame tree accessed.tree nodes location location ({} : ProtectedTags)
    have forest := GeneralBorrowFreshDefaultPathData.forest_of_owned tree {} parent offset len data.nonzero data.well data.bounds owned location {}
    have readForest : GeneralBorrowForest.Forest (source_normal_projection accessed.tree location {}).topology := by rw[topology];exact forest
    have attached := GeneralBorrowFreshDefaultPathData.attach accessed.tree depth children covered data.parentTag tag parent data.parentNode
      parentTag parentPresent fresh slot offset len data.nonzero good.2.2.1 bounds location location {} readForest
    rw[topology] at attached
    change GeneralBorrowFreshSharedPaths.Attach _ _ parent.toNat (GeneralBorrowFreshMetadataChildDefaultSlot.index slot).toNat at attached
    rw[slotIndex] at attached
    exact attached
end
end DuplicatePrefix.GeneralBorrowSharedRootMutableReservation
