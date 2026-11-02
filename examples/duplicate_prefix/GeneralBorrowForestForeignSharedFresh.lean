import duplicate_prefix.GeneralBorrowForestForeignShared

namespace DuplicatePrefix.GeneralBorrowForestForeignSharedFresh
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestForeignAccess (LocationData)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshReadFrame
open GeneralBorrowForestForeignShared (read child)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Absent source lookup means no physical map row has this key; no key-unique
or operation-success hypothesis is needed. -/
theorem fresh_of_absent (mapping : UniKeyMap BorTag) (tag : BorTag) (absent : mapping.get tag = none) :
    GeneralBorrowTagMap.Fresh mapping tag := by
  cases found : mapping.mapping.find? (fun row => row.1 == tag) with
  | some row => simp only [UniKeyMap.get,found] at absent;cases absent
  | none =>
    have missing := Array.find?_eq_none.mp found
    intro row member
    simpa only [beq_iff_eq] using missing row member

/-- An initially unused different tag remains physically unused after the REAL
leading Read and shared constructor. This supplies remaining finite-history
keys from initial disjointness, without per-step freshness assumptions. -/
theorem preserves (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (LocationData tree location protections parent primary extras .Read))
      offset (offset+len) tree.locations)
    (future : BorTag) (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping future) (different : newTag ≠ future) :
    GeneralBorrowTagMap.Fresh (child tree protections parentTag newTag isProtected offset len mode).tree.tagMapping future := by
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
  let nextSlot := GeneralBorrowFreshMetadataChildSlot.transport tree accessed.tree context.depth depth nodes mapping rfl parent slot
  have nextBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let metadata := GeneralBorrowFreshMetadataChildSlot.build accessed.tree depth children coverage parentTag newTag parent context.anchorNode
    tag present nextFresh nextSlot isProtected offset len nonzero good.2.2.1 nextBounds
  have absent : accessed.tree.indexOfTag future = none := by
    change accessed.tree.tagMapping.get future = none
    rw [mapping]
    unfold UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find tree.tagMapping future futureFresh]
    rfl
  apply fresh_of_absent
  exact (metadata.oldLookup future different).trans absent

end DuplicatePrefix.GeneralBorrowForestForeignSharedFresh
