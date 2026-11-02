import duplicate_prefix.GeneralBorrowForestAsMutDefaultSequence
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultOld
import duplicate_prefix.GeneralBorrowFreshFutureClean
import duplicate_prefix.GeneralBorrowForestMutableCleanRange
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowForestDefaultStageVacantClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false in
theorem slot_clean
    (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some node)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (different : query ≠ GeneralBorrowFreshMetadataChildDefaultSlot.index slot)
    (clean : GeneralBorrowFreshFutureClean.Clean tree query) :
    GeneralBorrowFreshFutureClean.Clean
      (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) query := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have modified := GeneralBorrowFreshFutureClean.modified tree.locations (GeneralBorrowFreshMetadataChildDefault.index input) query
      (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside different well bounds clean
    have stageClean : GeneralBorrowFreshFutureClean.Clean (GeneralBorrowFreshMetadataChildDefault.stage input) query := modified
    exact GeneralBorrowFreshFutureClean.shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefault.shape input) query stageClean
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,well,bounds⟩
    have modified := GeneralBorrowFreshFutureClean.modified tree.locations index query
      (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside different well bounds clean
    have stageClean : GeneralBorrowFreshFutureClean.Clean (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) query := modified
    exact GeneralBorrowFreshFutureClean.shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) query stageClean

theorem preserves (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : GeneralBorrowForestAsMutDefaultSequence.Data tree newTag parent offset len)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location protections parent data.primary data.extras))
      offset (offset+len) tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowForestAsMutDefaultSequence.child data protections).tree := by
  let parentTag := data.parentTag
  have nonzero := data.nonzero
  have bounds := data.bounds
  let accessed := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
  have good := GeneralBorrowForestMutableSlice.access tree protections parentTag parent data.primary data.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed data.context data.parentTagPresent data.well data.nodeFits
    offset (offset+len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data accessed.tree location protections parent data.primary data.extras))
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
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
  have tagPresent : accessed.tree.tagMapping.get parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let slot := GeneralBorrowFreshMetadataChildDefaultSlot.transport tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildDefaultSlot.index slot = GeneralBorrowFreshMetadataChildDefaultSlot.index data.slot := by
    exact GeneralBorrowFreshMetadataChildDefaultSlot.transport_index tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build accessed.tree depth children covered parentTag newTag
    parent data.context.anchorNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded
  intro query vacant
  have vacantResult : (GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree parentTag newTag offset len).nodes.get query = none := vacant
  have different : query ≠ GeneralBorrowFreshMetadataChildDefaultSlot.index slot := by
    intro same
    obtain ⟨node,present,_,_⟩ := metadata.node
    rw [same] at vacantResult
    change (GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree parentTag newTag offset len).nodeAt _ = none at vacantResult
    rw [present] at vacantResult
    cases vacantResult
  have oldVacant : accessed.tree.nodes.get query = none := by
    cases previous : accessed.tree.nodes.get query with
    | none => rfl
    | some node =>
      obtain ⟨next,present,_,_⟩ := GeneralBorrowFreshMetadataChildDefaultOld.of_slot accessed.tree depth children covered
        parentTag newTag parent data.context.anchorNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded query node previous
      change (GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree parentTag newTag offset len).nodeAt query = none at vacantResult
      rw [vacantResult] at present
      cases present
  have initialVacant : tree.nodes.get query = none := by rw [nodes] at oldVacant;exact oldVacant
  have readClean := GeneralBorrowForestMutableCleanRange.ranged tree protections parentTag parent data.primary query data.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed data.context data.nodeFits data.parentTagPresent
    initialVacant (clean query initialVacant) data.well offset (offset+len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  exact slot_clean accessed.tree depth children covered parentTag newTag parent data.context.anchorNode tagPresent parentPresent fresh slot
    offset len nonzero good.2.2.1 bounded query different readClean.2

end DuplicatePrefix.GeneralBorrowForestDefaultStageVacantClean
