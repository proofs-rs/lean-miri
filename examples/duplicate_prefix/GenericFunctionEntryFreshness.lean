import duplicate_prefix.GenericFunctionEntryMetadata
import duplicate_prefix.GeneralBorrowFreshMetadataChildProtector
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator

namespace DuplicatePrefix.GenericFunctionEntryFreshness
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
theorem mutable_slot
    (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some node)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (next : BorTag) (nodeFresh : GeneralBorrowProtector.Fresh tree next) (different : newTag ≠ next) :
    let after := GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag newTag offset len
    (GeneralBorrowTagMap.Fresh tree.tagMapping next → GeneralBorrowTagMap.Fresh after.tagMapping next) ∧ GeneralBorrowProtector.Fresh after next := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    constructor
    · intro mapFresh
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildMutable.result input).tagMapping next
      rw [(GeneralBorrowFreshMetadataChildMutable.append input).mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping newTag next _ _ mapFresh different
    · apply GeneralBorrowFreshMetadataChildProtector.of_shape _ _ (GeneralBorrowFreshMetadataChildMutable.shape input) next
      exact GeneralBorrowFreshMetadataChildProtector.staged tree _ parent node (GeneralBorrowFreshChild.child newTag parent)
        _ _ next parentPresent nodeFresh different
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,well,bounds⟩
    constructor
    · intro mapFresh
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildMutableReuse.result input).tagMapping next
      rw [(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping newTag next _ _ mapFresh different
    · apply GeneralBorrowFreshMetadataChildProtector.of_shape _ _ (GeneralBorrowFreshMetadataChildMutableReuse.shape input) next
      exact GeneralBorrowFreshMetadataChildProtector.staged tree _ parent node (GeneralBorrowFreshChild.child newTag parent)
        _ _ next parentPresent nodeFresh different

set_option autoImplicit false in
/-- Future tag freshness is transported from INITIAL caller data through the
actual parent Read and mutable append/reuse constructor. -/
theorem future (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (next : BorTag) (nodeFresh : GeneralBorrowProtector.Fresh tree next) (different : tracker.global.nextPointerTag ≠ next) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    (GeneralBorrowTagMap.Fresh tree.tagMapping next → GeneralBorrowTagMap.Fresh after.tagMapping next) ∧ GeneralBorrowProtector.Fresh after next := by
  let registered := tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector
  let accessed := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have owners := protector_owned_on tree tracker.global.protectedTags tracker.global.nextPointerTag .StrongProtector
    data.protectorFresh data.parent .Write offset (offset+len) data.owned
  have good := GeneralBorrowRangeLocal.access tree registered parentTag data.parent data.root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) data.nodeFits data.depth data.children data.node data.parentPresent
    data.roots data.covered data.tagPresent data.well offset (offset+len) owners bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (GeneralBorrowRange.LocationOwned accessed.tree registered data.parent .Write) offset (offset+len) accessed.tree.locations ∧
    accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
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
  have parentPresent : accessed.tree.nodeAt data.parent = some data.node := by
    change accessed.tree.nodes.get data.parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get parentTag = some data.parent := by rw [mapping];exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let slot := GeneralBorrowFreshMetadataChildMutableSlot.transport tree accessed.tree data.depth depth nodes mapping rfl data.parent data.slot

  have nodeAfter : GeneralBorrowProtector.Fresh accessed.tree next := by
    unfold GeneralBorrowProtector.Fresh at nodeFresh ⊢
    rw [nodes]
    exact nodeFresh
  have result := mutable_slot accessed.tree depth children covered parentTag tracker.global.nextPointerTag data.parent data.node
    tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded next nodeAfter different
  exact ⟨fun mapFresh => result.1 (by rw [mapping];exact mapFresh),result.2⟩

end DuplicatePrefix.GenericFunctionEntryFreshness
