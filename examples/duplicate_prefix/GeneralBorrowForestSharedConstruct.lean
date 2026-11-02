import duplicate_prefix.GeneralBorrowForestSharedData

namespace DuplicatePrefix.GeneralBorrowForestSharedConstruct
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestSharedData GeneralBorrowFreshReadFrame
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def read {tree : BorrowTree} {protections : ProtectedTags} {newTag : BorTag} {isProtected : Bool}
    {parent primary : UniIndex} {extras : List UniIndex} {offset len : UInt64}
    (data : Data tree protections newTag isProtected parent primary extras offset len) :=
  tree.performBorrowAccessRange (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) .VisitChildrenOfAccessed

def child {tree : BorrowTree} {protections : ProtectedTags} {newTag : BorTag} {isProtected : Bool}
    {parent primary : UniIndex} {extras : List UniIndex} {offset len : UInt64}
    (data : Data tree protections newTag isProtected parent primary extras offset len) :=
  (read data).tree.newChild (Size.ofBytes offset) (.concrete data.parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected

/-- Actual registered-protector Read followed by the actual Frozen newChild,
with arbitrary finite extra unexposed foreign-owned subtrees and either real
append or reusable allocator slot. Every success fact is derived from initial
Data; none is a premise. This is a reborrow component, not yet FnEntry/fullcall. -/
theorem run (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (data : Data tree protections newTag isProtected parent primary extras offset len) :
    (read data).status = .Completed ∧ (child data).outcome = .ok () := by
  have good := GeneralBorrowForestAccessRange.access tree (registered protections newTag isProtected) data.parentTag
    parent primary extras (Size.ofBytes offset) (Size.ofBytes len) .Read data.context data.tagPresent data.well data.locations data.bounds
  change (read data).status = .Completed ∧ (read data).tree.locations.WellFormed ∧
    (read data).tree.locations.size = tree.locations.size at good
  refine ⟨good.1,?_⟩
  let accessed := read data
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes data.context.depth
  have parentPresent : accessed.tree.nodeAt parent = some data.context.anchorNode := by
    change accessed.tree.nodes.get parent = _
    rw [nodes]
    exact data.context.anchorPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by
    rw [mapping]
    exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.fresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2];exact data.bounds
  change (accessed.tree.newChild (Size.ofBytes offset) (.concrete data.parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected).outcome = .ok ()
  cases data.slot with
  | append noFree aligned fits =>
    apply GeneralBorrowFreshSharedChild.append_success accessed.tree depth data.parentTag newTag parent data.context.anchorNode
      tagPresent parentPresent fresh
    · simpa only [mapping] using noFree
    · simpa only [mapping,nodes] using aligned
    · simpa only [mapping] using fits
    · exact data.nonzero
    · exact good.2.1
    · exact bounds
  | reuse index available bounded vacant slack =>
    apply GeneralBorrowFreshSharedChild.reuse_success accessed.tree depth data.parentTag newTag parent data.context.anchorNode
      tagPresent parentPresent fresh index
    · simpa only [mapping] using available
    · simpa only [nodes] using bounded
    · simpa only [nodes] using vacant
    · simpa only [depth,depth_on,nodes] using slack
    · exact data.nonzero
    · exact good.2.1
    · exact bounds

end DuplicatePrefix.GeneralBorrowForestSharedConstruct
