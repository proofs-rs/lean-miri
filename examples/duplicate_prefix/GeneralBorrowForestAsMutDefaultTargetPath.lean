import duplicate_prefix.GeneralRootDefaultMetadataCore
import duplicate_prefix.GeneralBorrowForestAsMutDefaultSequence
namespace DuplicatePrefix.GeneralBorrowForestAsMutDefaultTargetPath
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshReadFrame DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option autoImplicit false in
/-- The original parent remains an ancestor of the actual unprotected mutable
expression. Escaping nodes are unprotected because the sole newly escaping
node is the expression itself. -/
theorem parent_path (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (protections : ProtectedTags)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowForestAsMutDefaultSequence.Data tree newTag parent offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location protections parent data.primary data.extras)) offset (offset+len) tree.locations)
    (unheld : protections.contains newTag = false) :
    let after := (GeneralBorrowForestAsMutDefaultSequence.child data protections).tree
    ∀ location, (source_normal_projection after location protections).topology.ancestorPath parent.toNat =
      (source_normal_projection tree location protections).topology.ancestorPath parent.toNat := by
  let registered := protections
  let accessed := tree.performBorrowAccessRange (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have owners := owned
  have good := GeneralBorrowForestMutableSlice.access tree registered data.parentTag parent data.primary data.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed data.context data.parentTagPresent data.well data.nodeFits
    offset (offset+len) owners bounds (Nat.le_refl _) (Nat.le_refl _)
  have parentOwners : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned accessed.tree protections parent .Write)
      offset (offset+len) accessed.tree.locations := by
    intro position valid positive lower upper
    obtain ⟨localData⟩ := good.2.1 position valid positive lower upper
    exact ⟨⟨localData.base.forest⟩,localData.base.owned⟩
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
  let depth := depth_on tree accessed.tree nodes data.context.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.context.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.context.anchorNode := by
    change accessed.tree.nodes.get parent = _;rw [nodes];exact data.context.anchorPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let slot := GeneralBorrowFreshMetadataChildDefaultSlot.transport tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildDefaultSlot.index slot = GeneralBorrowForestAsMutDefaultSequence.index data := by
    exact (GeneralBorrowFreshMetadataChildDefaultSlot.transport_index tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot).trans
      (by unfold GeneralBorrowForestAsMutDefaultSequence.index;cases data.slot <;> rfl)
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build accessed.tree depth children covered data.parentTag newTag
    parent data.context.anchorNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded
  have sameTree : GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree data.parentTag newTag offset len =
      (GeneralBorrowForestAsMutDefaultSequence.child data protections).tree := rfl
  have oldNode := GeneralBorrowFreshMetadataChildDefaultOld.of_slot accessed.tree depth children covered data.parentTag newTag parent data.context.anchorNode
    tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded parent data.context.anchorNode parentPresent
  have forest := fun location => GeneralBorrowFreshDefaultPathData.forest_of_owned accessed.tree protections parent offset len nonzero good.2.2.1 bounded parentOwners location protections
  dsimp only
  intro location
  have attached := GeneralBorrowFreshDefaultPathData.attach accessed.tree depth children covered data.parentTag newTag parent data.context.anchorNode
    tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded location location protections (forest location)
  have path := attached.oldPath parent.toNat attached.parentValid attached.parentDifferent
  have topology := GeneralBorrowFreshMetadataChildAllocator.topology_frame tree accessed.tree nodes location location protections
  rw [topology] at path
  exact path
end DuplicatePrefix.GeneralBorrowForestAsMutDefaultTargetPath
