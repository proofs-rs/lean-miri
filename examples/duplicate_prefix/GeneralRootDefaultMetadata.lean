import duplicate_prefix.GeneralBorrowFreshDefaultSequence
import duplicate_prefix.GeneralBorrowRangeLocal
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultSlot

namespace DuplicatePrefix.GeneralRootDefaultMetadata
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
structure Output (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (protections : ProtectedTags)
    (offset len : UInt64)
    (data : GeneralBorrowFreshDefaultSequence.Data tree newTag parent offset len) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates
    ((GeneralBorrowFreshDefaultSequence.child data protections).tree)
  roots : ((GeneralBorrowFreshDefaultSequence.child data protections).tree).roots = #[data.root]
  lookup : ((GeneralBorrowFreshDefaultSequence.child data protections).tree).indexOfTag newTag =
    some (GeneralBorrowFreshDefaultSequence.index data)
  node : ∃ node, ((GeneralBorrowFreshDefaultSequence.child data protections).tree).nodeAt
    (GeneralBorrowFreshDefaultSequence.index data) = some node ∧ node.tag = newTag ∧ node.isExposed = false
  nodeFits : ((GeneralBorrowFreshDefaultSequence.child data protections).tree).nodes.data.size ≤ 4294967296
  well : ((GeneralBorrowFreshDefaultSequence.child data protections).tree).locations.WellFormed
  capacity : ((GeneralBorrowFreshDefaultSequence.child data protections).tree).locations.size = tree.locations.size

set_option autoImplicit false in
/-- Graph and allocator metadata of the actual ROOT mutable child, derived from
initial caller-tree data through protector insertion, Read, and construction. -/
def build (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (protections : ProtectedTags)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowFreshDefaultSequence.Data tree newTag parent offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations) : Output tree newTag parent protections offset len data := by
  let registered := protections
  let accessed := tree.performBorrowAccessRange (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have owners := owned
  have good := GeneralBorrowRangeLocal.access tree registered data.parentTag parent data.root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) data.nodeFits data.depth data.children data.parentNode data.parentPresent
    data.roots data.covered data.parentTagPresent data.well offset (offset+len) owners bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (GeneralBorrowRange.LocationOwned accessed.tree registered parent .Write) offset (offset+len) accessed.tree.locations ∧
    accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at framed
  have nodes : accessed.tree.nodes = tree.nodes := by
    have equality := congrArg BorrowTree.nodes framed
    exact equality
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by
    have equality := congrArg BorrowTree.tagMapping framed
    exact equality
  have roots : accessed.tree.roots = tree.roots := by
    have equality := congrArg BorrowTree.roots framed
    exact equality
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.parentNode := by
    change accessed.tree.nodes.get parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let slot := GeneralBorrowFreshMetadataChildDefaultSlot.transport tree accessed.tree data.depth depth nodes mapping rfl parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildDefaultSlot.index slot = GeneralBorrowFreshDefaultSequence.index data := by
    dsimp only [slot]
    rw [GeneralBorrowFreshMetadataChildDefaultSlot.transport_index]
    unfold GeneralBorrowFreshDefaultSequence.index
    cases data.slot <;> rfl
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build accessed.tree depth children covered data.parentTag newTag
    parent data.parentNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded
  have sameTree : GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree data.parentTag newTag offset len =
      (GeneralBorrowFreshDefaultSequence.child data protections).tree := rfl
  refine ⟨metadata.certificates,metadata.roots.trans (roots.trans data.roots),?_,?_,metadata.nodeFits,metadata.well,metadata.capacity.trans good.2.2.2⟩
  · simpa only [indexEq,sameTree] using metadata.lookup
  · simpa only [indexEq,sameTree] using metadata.node

end DuplicatePrefix.GeneralRootDefaultMetadata
