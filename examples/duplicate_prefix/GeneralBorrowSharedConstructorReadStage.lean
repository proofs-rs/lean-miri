import duplicate_prefix.GeneralBorrowSharedConstructorReadSlot
import duplicate_prefix.GeneralBorrowFreshStageMetadata

namespace DuplicatePrefix.GeneralBorrowSharedConstructorReadStage
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- After the actual leading Read, its data-derived allocator/graph frame lets
the actual unprotected shared constructor preserve any old Read bank member.
Source ownership derives the intermediate geometry; no operation success is an
input premise. The target's after-Read owner is the preceding Read-bank output. -/
theorem owned (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (writable : Nat → Bool)
    (sourceOwned : OwnedOn (Combined tree {} parent writable) offset (offset+len) tree.locations)
    (target : UniIndex) (targetPresent : ∃ node, tree.nodeAt target = some node)
    (afterReadOwned : OwnedOn (GeneralBorrowRange.LocationOwned (read data {} false).tree {} target .Read)
      offset (offset+len) (read data {} false).tree.locations) :
    OwnedOn (GeneralBorrowRange.LocationOwned (child data {} false).tree {} target .Read)
      offset (offset+len) (child data {} false).tree.locations := by
  let accessed := read data {} false
  have good := GeneralBorrowFreshMixedRead.access tree {} data.parentTag parent data.root
    (Size.ofBytes offset) (Size.ofBytes len) writable .VisitChildrenOfAccessed data.nodeFits data.depth data.children data.parentNode
    data.parentPresent data.roots data.covered data.parentTagPresent data.well offset (offset+len) sourceOwned data.bounds
    (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ OwnedOn (Combined accessed.tree {} parent writable)
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read {} .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [frame];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [frame];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.parentNode := by change accessed.tree.nodes.get parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact data.bounds
  let slot := GeneralBorrowFreshMetadataChildSlot.transport tree accessed.tree data.depth depth nodes mapping rfl parent data.slot
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have targetAfter : ∃ node, accessed.tree.nodeAt target = some node := by
    obtain ⟨node,present⟩ := targetPresent
    refine ⟨node,?_⟩
    change accessed.tree.nodes.get target = some node
    rw [nodes];exact present
  exact GeneralBorrowSharedConstructorReadSlot.owned accessed.tree depth children covered data.parentTag newTag parent data.parentNode
    tagPresent parentPresent fresh slot offset len data.nonzero good.2.2.1 bounds fits target targetAfter afterReadOwned

end DuplicatePrefix.GeneralBorrowSharedConstructorReadStage
