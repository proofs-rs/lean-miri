import duplicate_prefix.GenericFunctionEntryMetadata
import duplicate_prefix.GeneralBorrowFreshStagePool
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableOld

namespace DuplicatePrefix.GenericFunctionEntryPool
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages GeneralBorrowFreshAllocatorInvariant GeneralBorrowFreshStagePool
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem reuse_pool (input : GeneralBorrowFreshMetadataChildMutableReuse.Input)
    (pool : Pool input.tree.nodes input.tree.tagMapping.deassigned) (accounting : Accounting input.tree) :
    Pool (GeneralBorrowFreshMetadataChildMutableReuse.result input).nodes
      (GeneralBorrowFreshMetadataChildMutableReuse.result input).tagMapping.deassigned ∧
    Accounting (GeneralBorrowFreshMetadataChildMutableReuse.result input) := by
  have attached := GeneralBorrowFreshAllocatorInvariant.attached input.tree.nodes input.tree.tagMapping.deassigned pool
    input.index input.parent input.available input.parentNode (GeneralBorrowFreshChild.child input.newTag input.parent) input.parentPresent
  have stagedPool : Pool (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodes
      (GeneralBorrowFreshMetadataChildMutableReuse.stage input).tagMapping.deassigned := by
    simpa only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,GeneralBorrowFreshMetadataChildMutableReuse.mapping,
      GeneralBorrowFreshMetadataChildMutableReuse.index] using attached
  have metadata := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
  refine ⟨shape_pool _ _ (GeneralBorrowFreshMetadataChildMutableReuse.shape input) stagedPool,?_⟩
  unfold Accounting
  rw [metadata.mappingSize,metadata.freePool,metadata.size]
  have nonempty : 0 < input.tree.tagMapping.deassigned.size := by
    obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp input.available
    rw [eq,Array.size_push];omega
  rw [Array.size_pop]
  unfold Accounting at accounting
  omega

set_option autoImplicit false in
/-- Arbitrary coherent free pools survive the actual ROOT FnEntry protector,
parent Read and mutable constructor. Cleanliness is a separate permission invariant. -/
theorem allocator (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    Pool after.nodes after.tagMapping.deassigned ∧ Accounting after ∧ after.nodes.size ≤ tree.nodes.size+1 ∧
    (∀ query old, tree.nodeAt query = some old → ∃ next, after.nodeAt query = some next ∧
      next.tag = old.tag ∧ next.isExposed = old.isExposed) := by
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
  have readPool : Pool accessed.tree.nodes accessed.tree.tagMapping.deassigned := by rw [nodes,mapping];exact pool
  have readAccounting : Accounting accessed.tree := by unfold Accounting;rw [nodes,mapping];exact accounting
  have oldRead : ∀ query old, tree.nodeAt query = some old → accessed.tree.nodeAt query = some old := by
    intro query old present
    change accessed.tree.nodes.get query = some old
    rw [nodes];exact present
  cases data.slot with
  | append noFree aligned room =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨accessed.tree,depth,children,covered,parentTag,tracker.global.nextPointerTag,data.parent,data.node,
        tagPresent,parentPresent,fresh,by rw [mapping];exact noFree,by rw [mapping,nodes];exact aligned,
        by rw [mapping];exact room,offset,len,nonzero,good.2.2.1,bounded⟩
    have metadata := GeneralBorrowFreshMetadataChildMutable.append input
    have clear := Array.back?_eq_none_iff.mp metadata.noFree
    have resultPool : Pool (GeneralBorrowFreshMetadataChildMutable.result input).nodes
        (GeneralBorrowFreshMetadataChildMutable.result input).tagMapping.deassigned := by
      rw [clear];exact ⟨by simp,by simp,by simp⟩
    have resultAccounting : Accounting (GeneralBorrowFreshMetadataChildMutable.result input) := by
      unfold Accounting;rw [clear,Array.size_empty,Nat.add_zero];exact metadata.aligned
    refine ⟨resultPool,resultAccounting,?_,?_⟩
    · change (GeneralBorrowFreshMetadataChildMutable.result input).nodes.size ≤ tree.nodes.size+1
      rw [metadata.size];change accessed.tree.nodes.size+1 ≤ tree.nodes.size+1;rw [nodes];exact Nat.le_refl _
    · intro query old present
      exact GeneralBorrowFreshMetadataChildMutableOld.append input query old (oldRead query old present)
  | reuse query available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨accessed.tree,depth,children,covered,parentTag,tracker.global.nextPointerTag,data.parent,data.node,
        tagPresent,parentPresent,fresh,query,by rw [mapping];exact available,by rw [nodes];exact valid,
        by rw [nodes];exact vacant,by change data.depth.depth data.parent < accessed.tree.nodes.size;rw [nodes];exact slack,
        offset,len,nonzero,good.2.2.1,bounded⟩
    have result := reuse_pool input readPool readAccounting
    refine ⟨result.1,result.2,?_,?_⟩
    · change (GeneralBorrowFreshMetadataChildMutableReuse.result input).nodes.size ≤ tree.nodes.size+1
      rw [(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).size]
      change accessed.tree.nodes.size ≤ tree.nodes.size+1
      rw [nodes];omega
    · intro query old present
      exact GeneralBorrowFreshMetadataChildMutableOld.reuse input query old (oldRead query old present)

end DuplicatePrefix.GenericFunctionEntryPool
