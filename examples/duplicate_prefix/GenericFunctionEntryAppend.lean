import duplicate_prefix.GenericFunctionEntryClean

namespace DuplicatePrefix.GenericFunctionEntryAppend
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- The initial empty freelist selects the actual append branch and derives the
allocator facts needed for the subsequent two shared children. -/
theorem allocator (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (noFree : tree.tagMapping.deassigned.back? = none) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    after.tagMapping.deassigned.back? = none ∧ after.tagMapping.mapping.size = after.nodes.data.size ∧
      after.nodes.data.size = tree.nodes.data.size+1 ∧ after.tagMapping.mapping.size = tree.tagMapping.mapping.size+1 := by
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
  cases slot with
  | append empty aligned fitsIndex =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨accessed.tree,depth,children,covered,parentTag,tracker.global.nextPointerTag,data.parent,data.node,
        tagPresent,parentPresent,fresh,empty,aligned,fitsIndex,offset,len,nonzero,good.2.2.1,bounded⟩
    have metadata := GeneralBorrowFreshMetadataChildMutable.append input
    refine ⟨metadata.noFree,metadata.aligned,?_,?_⟩
    · change (GeneralBorrowFreshMetadataChildMutable.result input).nodes.size = _
      rw [metadata.size]
      change accessed.tree.nodes.data.size+1 = tree.nodes.data.size+1
      rw [nodes]
    · change (GeneralBorrowFreshMetadataChildMutable.result input).tagMapping.mapping.size = _
      rw [metadata.mapping]
      simp only [GeneralBorrowFreshMetadataChildMutable.mapping,input,Array.size_push,mapping]
  | reuse index available valid vacant slack =>
    rw [mapping,noFree] at available
    cases available

end DuplicatePrefix.GenericFunctionEntryAppend
