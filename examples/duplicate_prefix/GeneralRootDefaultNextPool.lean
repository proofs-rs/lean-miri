import duplicate_prefix.GeneralBorrowFreshStagePool
import duplicate_prefix.GeneralBorrowTightAncestry
import duplicate_prefix.GeneralRootDefaultMetadataCore
import duplicate_prefix.GenericAsMutPtrEntryValidity
import duplicate_prefix.GeneralBorrowFreshActiveOnRange
import duplicate_prefix.GeneralBorrowFreshMutableStages
namespace DuplicatePrefix.GeneralRootDefaultNextPool
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshReadFrame DuplicatePrefix.GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
open GeneralBorrowFreshAllocatorInvariant GeneralBorrowFreshStagePool
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
private theorem reuse_pool (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input)
    (pool : Pool input.tree.nodes input.tree.tagMapping.deassigned) (accounting : Accounting input.tree) :
    Pool (GeneralBorrowFreshMetadataChildDefaultReuse.result input).nodes
      (GeneralBorrowFreshMetadataChildDefaultReuse.result input).tagMapping.deassigned ∧
    Accounting (GeneralBorrowFreshMetadataChildDefaultReuse.result input) := by
  have attached := GeneralBorrowFreshAllocatorInvariant.attached input.tree.nodes input.tree.tagMapping.deassigned pool
    input.index input.parent input.available input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.parentPresent
  have stagedPool : Pool (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).nodes
      (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).tagMapping.deassigned := by
    simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,GeneralBorrowFreshMetadataChildDefaultReuse.mapping,
      GeneralBorrowFreshMetadataChildDefaultReuse.index] using attached
  have metadata := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
  refine ⟨shape_pool _ _ (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) stagedPool,?_⟩
  unfold Accounting
  rw [metadata.mappingSize,metadata.freePool,metadata.size]
  have nonempty : 0 < input.tree.tagMapping.deassigned.size := by
    obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp input.available
    rw [eq,Array.size_push];omega
  rw [Array.size_pop]
  unfold Accounting at accounting
  omega

private theorem slot_pool (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some node)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree) :
    let after := GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len
    Pool after.nodes after.tagMapping.deassigned ∧ Accounting after ∧ after.nodes.size ≤ tree.nodes.size+1 := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have metadata := GeneralBorrowFreshMetadataChildDefault.append input
    have clear := Array.back?_eq_none_iff.mp metadata.noFree
    refine ⟨?_,?_,?_⟩
    · change Pool (GeneralBorrowFreshMetadataChildDefault.result input).nodes (GeneralBorrowFreshMetadataChildDefault.result input).tagMapping.deassigned
      rw [clear];exact ⟨by simp,by simp,by simp⟩
    · change Accounting (GeneralBorrowFreshMetadataChildDefault.result input)
      unfold Accounting;rw [clear,Array.size_empty,Nat.add_zero];exact metadata.aligned
    · change (GeneralBorrowFreshMetadataChildDefault.result input).nodes.size ≤ tree.nodes.size+1
      rw [metadata.size];exact Nat.le_refl _
  | reuse query available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        query,available,valid,vacant,slack,offset,len,nonzero,well,bounds⟩
    have result := reuse_pool input pool accounting
    refine ⟨result.1,result.2,?_⟩
    change (GeneralBorrowFreshMetadataChildDefaultReuse.result input).nodes.size ≤ tree.nodes.size+1
    rw [(GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).size]
    change tree.nodes.size ≤ tree.nodes.size+1
    omega

set_option autoImplicit false in
/-- Form the protected FnEntry input after an actual unprotected expression with
an arbitrary coherent pool. All permissions, freshness and allocator premises
concern the initial tree; both stages select their actual append/reuse slots. -/
noncomputable def build (tree : BorrowTree) (newTag nextTag : BorTag) (parent : UniIndex) (protections : ProtectedTags)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowFreshDefaultSequence.Data tree newTag parent offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree parent .Write offset (offset+len))
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (nextFresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (nextNodeFresh : GeneralBorrowProtector.Fresh tree nextTag) (differentTag : newTag ≠ nextTag)
    (cleanVacant : ∀ query, tree.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean tree query) :
    let after := (GeneralBorrowFreshDefaultSequence.child data protections).tree
    Σ' next : GenericAsMutPtrEntryValidity.Data after protections newTag nextTag offset len,
      GeneralBorrowFreshFutureClean.Clean after (GeneralBorrowFreshMutableStages.slot_index next.slot) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin after parent .Write offset (offset+len) := by
  classical
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
  let after := (GeneralBorrowFreshDefaultSequence.child data protections).tree
  have readPool : Pool accessed.tree.nodes accessed.tree.tagMapping.deassigned := by rw [nodes,mapping];exact pool
  have readAccounting : Accounting accessed.tree := by unfold Accounting;rw [nodes,mapping];exact accounting
  have allocator := slot_pool accessed.tree depth children covered data.parentTag newTag parent data.parentNode
    tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded readPool readAccounting
  have sizeBound : after.nodes.size ≤ tree.nodes.size+1 := by
    have size := allocator.2.2
    change after.nodes.size ≤ accessed.tree.nodes.size+1 at size
    rw [nodes] at size;exact size
  let node := Classical.choose metadata.node
  have nodeFacts := Classical.choose_spec metadata.node
  have presentNode : after.nodeAt (GeneralBorrowFreshDefaultSequence.index data) = some node := by
    dsimp only [after,node]
    simpa only [indexEq,sameTree] using nodeFacts.1
  let nextDepth := GeneralBorrowTightAncestry.tight after.nodes metadata.certificates.depth
  have slack : nextDepth.depth (GeneralBorrowFreshDefaultSequence.index data) < after.nodes.size :=
    GeneralBorrowTightAncestry.present_slack after.nodes metadata.certificates.depth _ node presentNode
  have afterFits : after.tagMapping.mapping.size ≤ 4294967295 := by
    have accounted := allocator.2.1
    change Accounting after at accounted
    unfold Accounting at accounted
    omega
  let nextSlot := GeneralBorrowFreshAllocatorInvariant.slot after nextDepth (GeneralBorrowFreshDefaultSequence.index data)
    allocator.1 (empty_aligned after allocator.2.1) (fun _ => afterFits) slack
  let query := GeneralBorrowFreshMutableStages.slot_index nextSlot
  have vacant : after.nodes.get query = none := GeneralBorrowFreshMutableStages.slot_vacant after nextDepth _ nextSlot
  have queryDifferent : query ≠ GeneralBorrowFreshMetadataChildDefaultSlot.index slot := by
    intro equal
    rw [indexEq] at equal
    change after.nodes.get (GeneralBorrowFreshDefaultSequence.index data) = some node at presentNode
    rw [equal,presentNode] at vacant
    cases vacant
  have initiallyVacant : tree.nodes.get query = none := by
    cases initial : tree.nodes.get query with
    | none => rfl
    | some old =>
      have readPresent : accessed.tree.nodeAt query = some old := by change accessed.tree.nodes.get query = some old;rw [nodes];exact initial
      obtain ⟨next,lookup,_,_⟩ := GeneralBorrowFreshMetadataChildDefaultOld.of_slot accessed.tree depth children covered
        data.parentTag newTag parent data.parentNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded query old readPresent
      change after.nodes.get query = some next at lookup
      rw [vacant] at lookup;cases lookup
  have readClean := (GeneralBorrowFreshActiveOnRange.ranged tree protections data.parentTag parent data.root query
    (Size.ofBytes offset) (Size.ofBytes len) .Read .Write .VisitChildrenOfAccessed (fun _ => rfl)
    data.depth data.children data.parentNode data.parentPresent data.roots data.covered data.parentTagPresent
    initiallyVacant (cleanVacant query initiallyVacant) data.well offset (offset+len) owned bounds (Nat.le_refl _) (Nat.le_refl _)).2
  have cleanNext : GeneralBorrowFreshFutureClean.Clean after query :=
    GeneralRootDefaultCleanSlot.mutable_slot accessed.tree depth children covered data.parentTag newTag parent data.parentNode
      tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded query queryDifferent readClean
  have freshness := GeneralRootDefaultFreshSlot.mutable_slot accessed.tree depth children covered data.parentTag newTag parent data.parentNode
    tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded nextTag
    (by rw [framed];exact nextNodeFresh) differentTag
  have freshNext : GeneralBorrowTagMap.Fresh after.tagMapping nextTag := freshness.1 (by rw [mapping];exact nextFresh)
  have nodeFreshNext : GeneralBorrowProtector.Fresh after nextTag := freshness.2
  have childOwned := (GeneralBorrowFreshDefaultSequence.run tree newTag parent offset len data protections owned).2.2.1
  have targetActive := (GeneralBorrowFreshDefaultSequence.run_active tree newTag parent offset len data protections owned active).2.2.2.2
  let next : GenericAsMutPtrEntryValidity.Data after protections newTag nextTag offset len :=
    ⟨GeneralBorrowFreshDefaultSequence.index data,data.root,node,nextDepth,
      metadata.certificates.children,presentNode,metadata.roots.trans (roots.trans data.roots),metadata.certificates.covered,
      (by simpa only [indexEq,sameTree] using metadata.lookup),freshNext,nodeFreshNext,metadata.nodeFits,nextSlot,metadata.well,childOwned⟩
  exact ⟨next,cleanNext,targetActive⟩
end DuplicatePrefix.GeneralRootDefaultNextPool
