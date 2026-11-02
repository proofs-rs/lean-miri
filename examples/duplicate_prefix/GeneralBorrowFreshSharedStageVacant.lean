import duplicate_prefix.GeneralBorrowFreshStageMetadata
namespace DuplicatePrefix.GeneralBorrowFreshSharedStageVacant
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReadFrame
open DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem shape_vacant (before after : BorrowTree) (same : treeShape after = treeShape before)
    (query : UniIndex) (vacant : before.nodes.get query = none) : after.nodes.get query = none := by
  have mapped := GeneralBorrowFreshMetadata.lookup_shape before after same query
  rw [vacant] at mapped
  cases found : after.nodes.get query with
  | none => rfl
  | some node => rw [found] at mapped;cases mapped

private theorem append_vacant (input : GeneralBorrowFreshMetadataChildShared.Input)
    (query : UniIndex) (absent : input.tree.nodes.get query = none)
    (different : query ≠ GeneralBorrowFreshMetadataChildShared.index input) :
    (GeneralBorrowFreshMetadataChildShared.result input).nodes.get query = none := by
  have notParent : query ≠ input.parent := by
    intro equal
    have absentParent : input.tree.nodeAt input.parent = none := by rw [←equal];exact absent
    rw [input.parentPresent] at absentParent
    cases absentParent
  have attachedVacant := (GeneralBorrowFreshGraph.other_lookup input.tree
    (GeneralBorrowFreshMetadataChildShared.index input) input.parent query input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
    (GeneralBorrowFreshMetadataChildShared.at_end input) input.parentPresent notParent different).trans absent
  have stageVacant : (GeneralBorrowFreshMetadataChildShared.stage input).nodes.get query = none := by
    simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using attachedVacant
  exact shape_vacant _ _ (GeneralBorrowFreshMetadataChildShared.shape input) query stageVacant

private theorem reuse_vacant (input : GeneralBorrowFreshMetadataChildSharedReuse.Input)
    (query : UniIndex) (absent : input.tree.nodes.get query = none) (different : query ≠ input.index) :
    (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.get query = none := by
  have notParent : query ≠ input.parent := by
    intro equal
    have absentParent : input.tree.nodeAt input.parent = none := by rw [←equal];exact absent
    rw [input.parentPresent] at absentParent
    cases absentParent
  have attachedVacant := (GeneralBorrowFreshMetadataChildReuseGraph.other_lookup input.tree input.index input.parent query input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) input.vacant input.parentPresent notParent different).trans absent
  have stageVacant : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodes.get query = none := by
    simpa only [GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildSharedReuse.index,GeneralBorrowFreshMetadataChildAttach.staged,
      GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using attachedVacant
  exact shape_vacant _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input) query stageVacant

set_option autoImplicit false in
/-- A different initially vacant slot remains vacant after the real parent
Read, shared append or reuse, and ancestor SIFA update. -/
theorem vacant (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (query : UniIndex) (absent : tree.nodes.get query = none) (different : query ≠ index data) :
    (child data protections isProtected).tree.nodes.get query = none := by
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
  have rootsEq := congrArg BorrowTree.roots framed
  have roots : accessed.tree.roots = tree.roots := rootsEq
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.parentNode := by change accessed.tree.nodes.get parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact data.bounds
  have vacantRead : accessed.tree.nodes.get query = none := by rw [nodes];exact absent
  cases slotEq : data.slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
        (by rw [mapping];exact noFree),(by rw [mapping,nodes];exact aligned),(by rw [mapping];exact fits),
        isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
    have distinct : query ≠ GeneralBorrowFreshMetadataChildShared.index input := by
      simpa only [index,GeneralBorrowFreshSharedWithinStages.slot_index,slotEq,
        GeneralBorrowFreshMetadataChildShared.index,input,mapping] using different
    exact append_vacant input query vacantRead distinct
  | reuse candidate available bounded vacantIndex slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
        candidate,(by rw [mapping];exact available),(by rw [nodes];exact bounded),(by rw [nodes];exact vacantIndex),
        (by change data.depth.depth parent < accessed.tree.nodes.size;rw [nodes];exact slack),
        isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
    have distinct : query ≠ input.index := by
      simpa only [index,GeneralBorrowFreshSharedWithinStages.slot_index,slotEq,input] using different
    exact reuse_vacant input query vacantRead distinct
end DuplicatePrefix.GeneralBorrowFreshSharedStageVacant
