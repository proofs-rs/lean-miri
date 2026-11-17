import duplicate_prefix.GeneralRootDefaultMetadataCore
namespace DuplicatePrefix.GeneralRootDefaultPathFacts
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshReadFrame DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option autoImplicit false in
/-- The original parent remains an ancestor of the actual unprotected mutable
expression. Escaping nodes are unprotected because the sole newly escaping
node is the expression itself. -/
theorem build (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (protections : ProtectedTags)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowFreshDefaultSequence.Data tree newTag parent offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations)
    (unheld : protections.contains newTag = false) :
    let after := (GeneralBorrowFreshDefaultSequence.child data protections).tree
    (∀ tag, newTag ≠ tag → after.indexOfTag tag = tree.indexOfTag tag) ∧
    (∃ node, after.nodeAt parent = some node ∧ node.tag = data.parentNode.tag ∧ node.isExposed = data.parentNode.isExposed) ∧
    (∀ location position,
      position ∈ (source_normal_projection after location protections).topology.ancestorPath parent.toNat →
      position ∈ (source_normal_projection after location protections).topology.ancestorPath (GeneralBorrowFreshDefaultSequence.index data).toNat) ∧
    (∀ location query node, after.nodeAt query = some node →
      query.toNat ∈ (source_normal_projection after location protections).topology.ancestorPath (GeneralBorrowFreshDefaultSequence.index data).toNat →
      query.toNat ∉ (source_normal_projection after location protections).topology.ancestorPath parent.toNat →
      protections.contains node.tag = false) := by
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
    exact (GeneralBorrowFreshMetadataChildDefaultSlot.transport_index tree accessed.tree data.depth depth nodes mapping rfl parent data.slot).trans
      (by unfold GeneralBorrowFreshDefaultSequence.index;cases data.slot <;> rfl)
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build accessed.tree depth children covered data.parentTag newTag
    parent data.parentNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded
  have sameTree : GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree data.parentTag newTag offset len =
      (GeneralBorrowFreshDefaultSequence.child data protections).tree := rfl
  have oldNode := GeneralBorrowFreshMetadataChildDefaultOld.of_slot accessed.tree depth children covered data.parentTag newTag parent data.parentNode
    tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded parent data.parentNode parentPresent
  have forest := fun location => GeneralBorrowFreshDefaultPathData.forest_of_owned accessed.tree protections parent offset len nonzero good.2.2.1 bounded good.2.1 location protections
  have paths := GeneralBorrowFreshDefaultPathData.build accessed.tree depth children covered data.parentTag newTag parent data.parentNode
    tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded protections parent data.parentNode parentPresent forest
    (fun _ _ member => member) (fun _ _ _ _ localParent foreignParent => False.elim (foreignParent localParent))
  refine ⟨?_,oldNode,?_,?_⟩
  · intro tag different
    exact (metadata.oldLookup tag different).trans (by change accessed.tree.tagMapping.get tag = tree.tagMapping.get tag;rw [mapping])
  · simpa only [indexEq,sameTree] using paths.1
  · intro location query node present localChild foreignParent
    have moved := paths.2 location query node present (by simpa only [indexEq,sameTree] using localChild) foreignParent
    rcases moved with free | equal
    · exact free
    · rw [equal];exact unheld
end DuplicatePrefix.GeneralRootDefaultPathFacts
