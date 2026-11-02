import duplicate_prefix.GeneralBorrowForestForeignSharedResources
import duplicate_prefix.GeneralBorrowForestMixedShared
import duplicate_prefix.GeneralBorrowForestForeignCleanRange
import duplicate_prefix.GeneralBorrowGcVacantClean
import duplicate_prefix.GeneralBorrowFreshSharedFutureClean
import duplicate_prefix.GeneralBorrowFreshMetadataChildOld
namespace DuplicatePrefix.GeneralBorrowForestMixedSharedVacantClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshReadFrame
open GeneralBorrowForestForeignShared (read child)
open GeneralBorrowForestForeignAccess (LocationData)
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
theorem preserves (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (writable : Nat → Bool)
    (allocator : GeneralBorrowGcAllocator.Invariant tree)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location protections parent primary extras writable))
      offset (offset+len) tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowForestMixedShared.child tree protections parentTag newTag isProtected offset len mode).tree := by
  have foreign : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestForeignAccess.LocationData tree location protections parent primary extras .Read))
      offset (offset+len) tree.locations := by
    intro position valid positive start stop
    obtain ⟨data⟩ := before position valid positive start stop
    exact ⟨data.base⟩
  have good := GeneralBorrowForestForeignSlice.access tree protections parentTag parent primary extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read mode context parentTagPresent well fits offset (offset+len) foreign bounds
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
  let metadata := GeneralBorrowFreshMetadataChildSlot.build accessed.tree depth children coverage parentTag newTag parent context.anchorNode
    tag present nextFresh nextSlot isProtected offset len nonzero good.2.2.1 nextBounds
  intro query vacant
  have vacantResult : (GeneralBorrowFreshMetadataChildSlot.result accessed.tree parentTag newTag isProtected offset len).nodes.get query = none := vacant
  have different : query ≠ GeneralBorrowFreshMetadataChildSlot.index nextSlot := by
    intro same
    obtain ⟨node,present,_,_⟩ := metadata.node
    rw [same] at vacantResult
    change (GeneralBorrowFreshMetadataChildSlot.result accessed.tree parentTag newTag isProtected offset len).nodeAt _ = none at vacantResult
    rw [present] at vacantResult
    cases vacantResult
  have oldVacant : accessed.tree.nodes.get query = none := by
    cases previous : accessed.tree.nodes.get query with
    | none => rfl
    | some node =>
      obtain ⟨next,present,_,_⟩ := GeneralBorrowFreshMetadataChildOld.of_slot accessed.tree depth children coverage
        parentTag newTag parent context.anchorNode tag present nextFresh nextSlot isProtected offset len nonzero good.2.2.1 nextBounds query node previous
      change (GeneralBorrowFreshMetadataChildSlot.result accessed.tree parentTag newTag isProtected offset len).nodeAt query = none at vacantResult
      rw [vacantResult] at present
      cases present
  have initialVacant : tree.nodes.get query = none := by rw [nodes] at oldVacant;exact oldVacant
  have readClean := GeneralBorrowForestForeignCleanRange.ranged tree protections parentTag parent primary query extras
    (Size.ofBytes offset) (Size.ofBytes len) mode context fits parentTagPresent initialVacant (clean query initialVacant)
    well offset (offset+len) foreign bounds (Nat.le_refl _) (Nat.le_refl _)
  have cleanAfter : GeneralBorrowFreshFutureClean.Clean accessed.tree query := readClean.2
  change GeneralBorrowFreshFutureClean.Clean (GeneralBorrowFreshMetadataChildSlot.result accessed.tree parentTag newTag isProtected offset len) query
  cases slotEq : nextSlot with
  | append noFree aligned fits =>
    exact GeneralBorrowFreshSharedFutureClean.append
      ⟨accessed.tree,depth,children,coverage,parentTag,newTag,parent,context.anchorNode,tag,present,nextFresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,good.2.2.1,nextBounds⟩ query (by simpa only [slotEq,GeneralBorrowFreshMetadataChildSlot.index,GeneralBorrowFreshMetadataChildShared.index] using different) cleanAfter
  | reuse index available bounded vacant slack =>
    exact GeneralBorrowFreshSharedFutureClean.reuse
      ⟨accessed.tree,depth,children,coverage,parentTag,newTag,parent,context.anchorNode,tag,present,nextFresh,
        index,available,bounded,vacant,slack,isProtected,offset,len,nonzero,good.2.2.1,nextBounds⟩ query (by simpa only [slotEq,GeneralBorrowFreshMetadataChildSlot.index,GeneralBorrowFreshMetadataChildShared.index] using different) cleanAfter

end DuplicatePrefix.GeneralBorrowForestMixedSharedVacantClean
