import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowSharedAllocatorInvariant
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcAllocator DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReadFrame
open DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- SIFA changes permissions and flags but preserves node tags, sparse presence
and the complete tag map. Reverse node_fields transports live-node coherence. -/
theorem shape_tags (before after : BorrowTree) (same : treeShape after = treeShape before)
    (coherent : NodeTags before) : NodeTags after := by
  intro index node present
  obtain ⟨old,oldPresent,tag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm index node present
  have lookup := coherent index old oldPresent
  rw [tag] at lookup
  change after.tagMapping.get node.tag = some index
  rw [GeneralBorrowFreshMetadata.mapping before after same]
  exact lookup

theorem insert_tags (tree : BorrowTree) (index : UniIndex) (newNode : TreeNode)
    (newLookup : tree.tagMapping.get newNode.tag = some index) (coherent : NodeTags tree) :
    NodeTags {tree with nodes := tree.nodes.insert index newNode} := by
  intro query node present
  change (tree.nodes.insert index newNode).get query = some node at present
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowFreshLocation.get_same] at present
    cases present
    exact newLookup
  · rw [GeneralBorrowFreshLocation.get_other tree.nodes index query newNode same] at present
    exact coherent query node present

theorem push_tags (tree : BorrowTree) (newTag : BorTag) (index : UniIndex) (free : Array UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (coherent : NodeTags tree) :
    NodeTags {tree with tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),free⟩} := by
  intro query node present
  have old := coherent query node present
  have absent : tree.tagMapping.get newTag = none := by
    unfold UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find tree.tagMapping newTag fresh]
    rfl
  have different : newTag ≠ node.tag := by
    intro same
    rw [←same,absent] at old
    cases old
  change (⟨tree.tagMapping.mapping.push (newTag,index),free⟩ : UniKeyMap BorTag).get node.tag = some query
  rw [GeneralBorrowTagMap.pushed_get_old tree.tagMapping newTag node.tag different index free]
  exact old

theorem staged_tags (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (newTag : BorTag) (tag : newNode.tag = newTag) (free : Array UniIndex) (locations : DedupRangeMap LocationTree)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (coherent : NodeTags tree) :
    NodeTags (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode
      ⟨tree.tagMapping.mapping.push (newTag,index),free⟩ locations) := by
  let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (newTag,index),free⟩
  have extended := push_tags tree newTag index free fresh coherent
  have newLookup : mapping.get newNode.tag = some index := by
    rw [tag]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping newTag fresh index free
  have parentLookup : mapping.get parentNode.tag = some parent := extended parent parentNode parentPresent
  have first := insert_tags {tree with tagMapping := mapping} index newNode newLookup extended
  have second := insert_tags {tree with tagMapping := mapping,nodes := tree.nodes.insert index newNode}
    parent {parentNode with children := parentNode.children.push index} parentLookup first
  simpa only [NodeTags,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
    GeneralBorrowFreshNode.attachedNodes,mapping] using second

namespace Append
open GeneralBorrowFreshMetadataChildShared

theorem preserves (input : Input) (initial : Invariant input.tree) : Invariant (result input) := by
  have allocated := GeneralBorrowFreshStagePool.Append.result input
  have staged := staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned
    (locations input) input.parentPresent input.fresh initial.nodeTags
  have coherent : NodeTags (stage input) := by
    simpa only [stage,mapping] using staged
  have tags := shape_tags (stage input) (result input) (shape input) coherent
  refine ⟨allocated.1,allocated.2,?_,tags⟩
  have same := (GeneralBorrowFreshMetadataChildShared.append input).mapping
  unfold KeyUnique
  rw [same]
  exact fresh_push_unique input.tree.tagMapping input.newTag (index input) input.tree.tagMapping.deassigned initial.unique input.fresh
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildSharedReuse

theorem preserves (input : Input) (initial : Invariant input.tree) : Invariant (result input) := by
  have allocated := GeneralBorrowFreshStagePool.Reuse.result input initial.pool initial.accounting
  have staged := staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned.pop
    (locations input) input.parentPresent input.fresh initial.nodeTags
  have coherent : NodeTags (stage input) := by
    simpa only [stage,mapping] using staged
  have tags := shape_tags (stage input) (result input) (shape input) coherent
  refine ⟨allocated.1,allocated.2,?_,tags⟩
  have same := (GeneralBorrowFreshMetadataChildSharedReuse.reuse input).mapping
  unfold KeyUnique
  rw [same]
  exact fresh_push_unique input.tree.tagMapping input.newTag (index input) input.tree.tagMapping.deassigned.pop initial.unique input.fresh
end Reuse

/-- Data-driven successful shared history step. The initial structural borrow
contract and slice ownership derive the real parent Read and Frozen constructor
success, rather than assuming a successful mutation or covering arbitrary
partially-mutating newChild error branches. -/
theorem shared_stage (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (initial : Invariant tree) :
    (read data protections isProtected).status = .Completed ∧ (child data protections isProtected).outcome = .ok () ∧
    Invariant (child data protections isProtected).tree := by
  have success := GeneralBorrowFreshSharedSequence.run tree newTag parent offset len data protections isProtected writable owned
  refine ⟨success.1,success.2.1,?_⟩
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
  have mapEq := congrArg BorrowTree.tagMapping framed
  have mapping : accessed.tree.tagMapping = tree.tagMapping := mapEq
  have readInvariant : Invariant accessed.tree := by
    rw [framed]
    exact ⟨initial.pool,initial.accounting,initial.unique,initial.nodeTags⟩
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
    exact Append.preserves input readInvariant
  | reuse query available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
        query,by rw [mapping];exact available,by rw [nodes];exact bounded,by rw [nodes];exact vacant,
        by change data.depth.depth parent < accessed.tree.nodes.size;rw [nodes];exact slack,
        isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
    exact Reuse.preserves input readInvariant
end DuplicatePrefix.GeneralBorrowSharedAllocatorInvariant
