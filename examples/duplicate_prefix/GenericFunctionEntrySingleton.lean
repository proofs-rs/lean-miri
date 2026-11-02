import duplicate_prefix.GenericAsMutPtrArgumentCopy
import duplicate_prefix.GeneralBorrowFreshMutableStages
import duplicate_prefix.GeneralBorrowSingletonReuseAllocator

namespace DuplicatePrefix.GenericFunctionEntrySingleton
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem selected (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parent : UniIndex) (slot : Slot tree depth parent) (q : UniIndex)
    (singleton : tree.tagMapping.deassigned = #[q]) :
    q.toNat < tree.nodes.data.size ∧ tree.nodes.get q = none ∧ depth.depth parent < tree.nodes.size ∧
      GeneralBorrowFreshMutableStages.slot_index slot = q := by
  have available : tree.tagMapping.deassigned.back? = some q := by rw [singleton];rfl
  cases slot with
  | append empty aligned fits => rw [available] at empty;cases empty
  | reuse index found bounded vacant slack =>
    have equal : index = q := Option.some.inj (found.symm.trans available)
    subst index
    exact ⟨bounded,vacant,slack,rfl⟩

set_option autoImplicit false in
/-- A singleton freepool makes the actual ROOT FnEntry choose reuse. Its real
protector insertion and parent Read precede the mutable constructor; the
resulting tree is append-ready, with unchanged node count. No operation success
or post-state allocator fact is an input. This is a component metadata lemma. -/
theorem allocator (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (q : UniIndex) (singleton : tree.tagMapping.deassigned = #[q])
    (balanced : tree.tagMapping.mapping.size+1 = tree.nodes.data.size) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    GeneralBorrowSingletonReuseAllocator.Ready tree after ∧
      GeneralBorrowFreshMutableStages.slot_index data.slot = q ∧ q.toNat < tree.tagMapping.mapping.size+1 := by
  have chosen := selected tree data.depth data.parent data.slot q singleton
  have qBound : q.toNat < tree.tagMapping.mapping.size+1 := by rw [balanced];exact chosen.1
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
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : accessed.tree.nodes = tree.nodes := nodeEq
  have mappingEq := congrArg BorrowTree.tagMapping framed
  have mapping : accessed.tree.tagMapping = tree.tagMapping := mappingEq
  let depth := depth_on tree accessed.tree nodes data.depth
  have graph : GeneralBorrowGraph.ChildNodes accessed.tree ∧ GeneralBorrowGraph.RootsCover accessed.tree := by
    rw [framed]
    exact graph_on tree accessed.tree.locations data.children data.covered
  have parentPresent : accessed.tree.nodeAt data.parent = some data.node := by
    change accessed.tree.nodes.get data.parent = _
    rw [nodes]
    exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get parentTag = some data.parent := by rw [mapping];exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [mapping];exact data.tagFresh
  have before := GeneralBorrowSingletonReuseAllocator.read_initial tree q singleton balanced (.concrete parentTag)
    (Size.ofBytes offset) (Size.ofBytes len) registered .VisitChildrenOfAccessed
  have available : accessed.tree.tagMapping.deassigned.back? = some q := by rw [before.1];rfl
  have valid : q.toNat < accessed.tree.nodes.data.size := by rw [nodes];exact chosen.1
  have vacant : accessed.tree.nodes.get q = none := by rw [nodes];exact chosen.2.1
  have slack : depth.depth data.parent < accessed.tree.nodes.size := by change data.depth.depth data.parent < _;rw [nodes];exact chosen.2.2.1
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
    ⟨accessed.tree,depth,graph.1,graph.2,parentTag,tracker.global.nextPointerTag,data.parent,data.node,
      tagPresent,parentPresent,fresh,q,available,valid,vacant,slack,offset,len,nonzero,good.2.2.1,bounded⟩
  have result := GeneralBorrowSingletonReuseAllocator.mutable input before.1 before.2
  have nodeSize : accessed.tree.nodes.size = tree.nodes.size := congrArg UniValMap.size nodes
  have mapSize : accessed.tree.tagMapping.mapping.size = tree.tagMapping.mapping.size := congrArg (fun tags => tags.mapping.size) mapping
  refine ⟨⟨result.empty,result.aligned,result.mappingSize.trans (congrArg (fun size => size+1) mapSize),result.nodeSize.trans nodeSize⟩,chosen.2.2.2,qBound⟩

end DuplicatePrefix.GenericFunctionEntrySingleton
