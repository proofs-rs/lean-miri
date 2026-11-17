import duplicate_prefix.GeneralBorrowFreshStageMetadata
import duplicate_prefix.GeneralBorrowFreshAllocatorInvariant
namespace DuplicatePrefix.GeneralBorrowFreshStagePool
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAllocatorInvariant DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReadFrame
open DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Accounting (tree : BorrowTree) : Prop :=
  tree.tagMapping.mapping.size + tree.tagMapping.deassigned.size = tree.nodes.size

theorem empty_aligned (tree : BorrowTree) (accounting : Accounting tree)
    (empty : tree.tagMapping.deassigned.back? = none) : tree.tagMapping.mapping.size = tree.nodes.data.size := by
  have clear := Array.back?_eq_none_iff.mp empty
  unfold Accounting at accounting
  simpa only [clear,Array.size_empty,Nat.add_zero,UniValMap.size] using accounting

theorem shape_pool (before after : BorrowTree) (same : treeShape after = treeShape before)
    (pool : Pool before.nodes before.tagMapping.deassigned) : Pool after.nodes after.tagMapping.deassigned := by
  have mapping := GeneralBorrowFreshMetadata.mapping before after same
  have size := GeneralBorrowFreshMetadata.node_size before after same
  refine ⟨?_,?_,?_⟩
  · intro query member
    rw [mapping] at member
    change query.toNat < after.nodes.size
    rw [size]
    exact pool.bounded query member
  · intro query member
    rw [mapping] at member
    have lookup := GeneralBorrowFreshMetadata.lookup_shape before after same query
    rw [pool.vacant query member] at lookup
    cases found : after.nodes.get query with
    | none => rfl
    | some node => simp [found] at lookup
  · rw [mapping];exact pool.nodup

theorem shape_accounting (before after : BorrowTree) (same : treeShape after = treeShape before)
    (accounting : Accounting before) : Accounting after := by
  unfold Accounting
  rw [GeneralBorrowFreshMetadata.mapping before after same,GeneralBorrowFreshMetadata.node_size before after same]
  exact accounting

namespace Reuse
open GeneralBorrowFreshMetadataChildSharedReuse

theorem result (input : Input) (pool : Pool input.tree.nodes input.tree.tagMapping.deassigned)
    (accounting : Accounting input.tree) :
    Pool (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes
      (GeneralBorrowFreshMetadataChildSharedReuse.result input).tagMapping.deassigned ∧
    Accounting (GeneralBorrowFreshMetadataChildSharedReuse.result input) := by
  have attached := GeneralBorrowFreshAllocatorInvariant.attached input.tree.nodes input.tree.tagMapping.deassigned pool
    input.index input.parent input.available input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) input.parentPresent
  have stagedPool : Pool (stage input).nodes (stage input).tagMapping.deassigned := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,mapping,GeneralBorrowFreshMetadataChildSharedReuse.index] using attached
  have metadata := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
  have bound := shape_pool (stage input) (GeneralBorrowFreshMetadataChildSharedReuse.result input) (shape input) stagedPool
  refine ⟨bound,?_⟩
  unfold Accounting
  rw [metadata.mappingSize,metadata.freePool,metadata.size]
  have nonempty : 0 < input.tree.tagMapping.deassigned.size := by
    obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp input.available
    rw [eq,Array.size_push]
    omega
  rw [Array.size_pop]
  unfold Accounting at accounting
  omega
end Reuse

namespace Append
open GeneralBorrowFreshMetadataChildShared

theorem result (input : Input) :
    Pool (GeneralBorrowFreshMetadataChildShared.result input).nodes
      (GeneralBorrowFreshMetadataChildShared.result input).tagMapping.deassigned ∧
    Accounting (GeneralBorrowFreshMetadataChildShared.result input) := by
  have metadata := GeneralBorrowFreshMetadataChildShared.append input
  have clear := Array.back?_eq_none_iff.mp metadata.noFree
  refine ⟨?_,?_⟩
  · rw [clear]
    exact ⟨by simp,by simp,by simp⟩
  · unfold Accounting
    rw [clear,Array.size_empty,Nat.add_zero]
    exact metadata.aligned
end Append

/-- An actual shared stage preserves arbitrary coherent free pools and the
mapping/free/table accounting equation. Parent Read, child construction and
SIFA metadata are handled by existing checked components; no operation success
is a premise. This allocator theorem asserts no slot permission cleanliness. -/
theorem stage (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree) :
    Pool (child data protections isProtected).tree.nodes (child data protections isProtected).tree.tagMapping.deassigned ∧
    Accounting (child data protections isProtected).tree := by
  let accessed := read data protections isProtected
  have owners := GeneralBorrowFreshStageMetadata.registered_owned tree newTag parent offset len data protections isProtected writable owned
  have good := GeneralBorrowFreshMixedRead.access tree (registered protections newTag isProtected) data.parentTag parent data.root
    (Size.ofBytes offset) (Size.ofBytes len) writable .VisitChildrenOfAccessed data.nodeFits data.depth data.children data.parentNode
    data.parentPresent data.roots data.covered data.parentTagPresent data.well offset (offset+len) owners data.bounds
    (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ OwnedOn (Combined accessed.tree (registered protections newTag isProtected) parent writable)
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at framed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : accessed.tree.nodes = tree.nodes := nodeEq
  have mappingEq := congrArg BorrowTree.tagMapping framed
  have mapping : accessed.tree.tagMapping = tree.tagMapping := mappingEq
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.parentNode := by change accessed.tree.nodes.get parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact data.bounds
  cases data.slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
        by rw [mapping];exact noFree,by rw [mapping,nodes];exact aligned,by rw [mapping];exact fits,
        isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
    exact Append.result input
  | reuse query available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
        query,by rw [mapping];exact available,by rw [nodes];exact bounded,by rw [nodes];exact vacant,
        by change data.depth.depth parent < accessed.tree.nodes.size;rw [nodes];exact slack,
        isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
    have readPool : Pool accessed.tree.nodes accessed.tree.tagMapping.deassigned := by rw [nodes,mapping];exact pool
    have readAccounting : Accounting accessed.tree := by unfold Accounting;rw [nodes,mapping];exact accounting
    exact Reuse.result input readPool readAccounting
end DuplicatePrefix.GeneralBorrowFreshStagePool
