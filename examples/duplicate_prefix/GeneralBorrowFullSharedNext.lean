import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
namespace DuplicatePrefix.GeneralBorrowFullSharedNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared
open DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual parent children update and SIFA preserve its tag, parent link
and exposure flag, while producing the precise new parent node. -/
theorem parent_fields (input : Input) :
    ∃ node, (result input).nodeAt input.parent = some node ∧ node.tag = input.parentNode.tag ∧
      node.parent = input.parentNode.parent ∧ node.isExposed = input.parentNode.isExposed := by
  let updated := GeneralBorrowFreshGraph.updatedParent input.parentNode (index input)
  have stagedPresent : (stage input).nodeAt input.parent = some updated := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,updated,BorrowTree.nodeAt] using
      GeneralBorrowFreshGraph.parent_lookup input.tree (index input) input.parent input.parentNode
        (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) (at_end input) input.parentPresent
  obtain ⟨node,present,tag,parent,_,_⟩ := GeneralBorrowFreshMetadata.node_fields (stage input) (result input)
    (shape input) input.parent updated stagedPresent
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (stage input) (result input) (exposure input) input.parent
  change (stage input).nodes.get input.parent = some updated at stagedPresent
  rw [stagedPresent,present] at flags
  exact ⟨node,present,tag,parent,by simpa only [Option.map_some,Option.some.injEq,updated,GeneralBorrowFreshGraph.updatedParent] using flags⟩

private noncomputable def finish (input : Input) (nextTag : BorTag)
    (metadata : GeneralBorrowFreshMetadataChildShared.Output input)
    (room : input.tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping nextTag) (different : input.newTag ≠ nextTag)
     : Input := by
  let node := Classical.choose (parent_fields input)
  have nodeFacts := Classical.choose_spec (parent_fields input)
  have geometry := GeneralBorrowFreshSharedGeometry.append_frame input
  have mapsize : (result input).tagMapping.mapping.size = input.tree.tagMapping.mapping.size+1 := by
    rw [metadata.mapping]
    simp only [mapping,Array.size_push]
  have bounds : input.offset.toNat+input.len.toNat ≤ (result input).locations.size.bytes.toNat := by
    rw [geometry.2]
    exact input.bounds
  have parentDifferent : input.newTag ≠ input.parentTag := by
    have present := input.parentTagPresent
    have absent : input.tree.tagMapping.get input.newTag = none := by
      unfold UniKeyMap.get
      rw [GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh]
      rfl
    intro same
    rw [←same,absent] at present
    cases present
  exact {
    tree := result input,depth := metadata.certificates.depth,children := metadata.certificates.children,covered := metadata.certificates.covered
    parentTag := input.parentTag,newTag := nextTag,parent := input.parent,parentNode := node
    parentTagPresent := (metadata.oldLookup input.parentTag parentDifferent).trans input.parentTagPresent
    parentPresent := nodeFacts.1
    fresh := GeneralBorrowFreshMetadataChildAllocator.append_fresh input nextTag fresh different
    noFree := metadata.noFree,aligned := metadata.aligned,fits := by rw [mapsize];exact room
    isProtected := false,offset := input.offset,len := input.len,nonzero := input.nonzero,well := geometry.1,bounds := bounds }

/-- Form the next real shared Input on the SAME original parent, rather than
on the previous new child. Freshness and one-node headroom concern the initial
tag map. Neither the previous nor the next operation's success is a premise. -/
noncomputable def next (input : Input) (nextTag : BorTag)
    (room : input.tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping nextTag) (different : input.newTag ≠ nextTag)
     : Input :=
  finish input nextTag (GeneralBorrowFreshMetadataChildShared.append input) room fresh different

theorem next_fields (input : Input) (nextTag : BorTag)
    (room : input.tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping nextTag) (different : input.newTag ≠ nextTag)
     :
    let after := next input nextTag room fresh different
    after.tree = result input ∧ after.parent = input.parent ∧ after.parentTag = input.parentTag ∧
      after.newTag = nextTag ∧ after.offset = input.offset ∧ after.len = input.len ∧ after.isProtected = false ∧
      after.parentNode.tag = input.parentNode.tag ∧ after.parentNode.parent = input.parentNode.parent ∧
      after.parentNode.isExposed = input.parentNode.isExposed := by
  have nodeFacts := Classical.choose_spec (parent_fields input)
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,nodeFacts.2.1,nodeFacts.2.2.1,nodeFacts.2.2.2⟩
end DuplicatePrefix.GeneralBorrowFullSharedNext
