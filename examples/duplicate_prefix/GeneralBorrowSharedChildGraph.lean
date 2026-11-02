import duplicate_prefix.GeneralBorrowSharedReadMetadata
import duplicate_prefix.GeneralBorrowProtectedChildOld
namespace DuplicatePrefix.GeneralBorrowSharedChildGraph
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshGraph GeneralBorrowFreshAnchor GeneralBorrowNodeUpdate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

private theorem transfer (before after : BorrowTree)
    (shape : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (query : UniIndex) (node : TreeNode) (present : before.nodeAt query = some node) :
    ∃ next, after.nodeAt query = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧ next.isExposed = node.isExposed := by
  obtain ⟨next,found,tag,parent,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape query node present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after exposure query
  change before.nodes.get query = some node at present
  rw [found,present] at flags
  exact ⟨next,found,tag,parent,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

private theorem old_attach (tree : BorrowTree) (child parent query : UniIndex) (parentNode newNode oldNode : TreeNode)
    (present : tree.nodeAt parent = some parentNode) (old : tree.nodeAt query = some oldNode)
    (parentLookup : (attached tree child parent parentNode newNode).nodeAt parent = some (updatedParent parentNode child))
    (otherLookup : query ≠ parent → (attached tree child parent parentNode newNode).nodeAt query = tree.nodeAt query) :
    ∃ next, (attached tree child parent parentNode newNode).nodeAt query = some next ∧
      next.tag = oldNode.tag ∧ next.parent = oldNode.parent ∧ next.isExposed = oldNode.isExposed := by
  by_cases same : query = parent
  · subst query
    have equal : oldNode = parentNode := Option.some.inj (old.symm.trans present)
    subst oldNode
    exact ⟨updatedParent parentNode child,parentLookup,rfl,rfl,rfl⟩
  · exact ⟨oldNode,(otherLookup same).trans old,rfl,rfl,rfl⟩

/-- Exact fresh-child and every-old-node graph metadata of actual shared
construction. Both real allocator choices and the ancestor SIFA update are
included. This is independent of held policy and source permission profiles. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen held
    ∃ child,actual.tree.indexOfTag newTag = some child ∧
      (∃ node,actual.tree.nodeAt child = some node ∧ node.tag = newTag ∧ node.parent = some parent ∧ node.isExposed = false) ∧
      (∀ query oldNode,tree.nodeAt query = some oldNode →
        ∃ next,actual.tree.nodeAt query = some next ∧ next.tag = oldNode.tag ∧ next.parent = oldNode.parent ∧ next.isExposed = oldNode.isExposed) := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildShared.index input
    have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
    have newPresent : (GeneralBorrowFreshMetadataChildShared.stage input).nodeAt child = some (sharedNode newTag parent) :=
      GeneralBorrowFreshGraph.new_lookup tree child parent parentNode (sharedNode newTag parent) atEnd present
    obtain ⟨node,nodePresent,tag,edge,hidden⟩ := transfer _ _ (GeneralBorrowFreshMetadataChildShared.shape input)
      (GeneralBorrowFreshMetadataChildShared.exposure input) child (sharedNode newTag parent) newPresent
    refine ⟨child,(GeneralBorrowFreshMetadataChildShared.append input).freshLookup,⟨node,nodePresent,tag,edge,hidden⟩,?_⟩
    intro query oldNode old
    have different : query ≠ child := by
      intro same
      have bounded := lookup_valid tree.nodes query oldNode old
      rw [same,atEnd] at bounded
      omega
    obtain ⟨middle,middlePresent,oldTag,oldParent,oldHidden⟩ := old_attach tree child parent query parentNode (sharedNode newTag parent)
      oldNode present old (GeneralBorrowFreshGraph.parent_lookup tree child parent parentNode (sharedNode newTag parent) atEnd present)
      (fun notParent => GeneralBorrowFreshGraph.other_lookup tree child parent query parentNode (sharedNode newTag parent)
        atEnd present notParent different)
    obtain ⟨next,found,nextTag,nextParent,nextHidden⟩ := transfer (GeneralBorrowFreshMetadataChildShared.stage input) _
      (GeneralBorrowFreshMetadataChildShared.shape input) (GeneralBorrowFreshMetadataChildShared.exposure input) query middle middlePresent
    exact ⟨next,found,nextTag.trans oldTag,nextParent.trans oldParent,nextHidden.trans oldHidden⟩
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have newPresent : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodeAt child = some (sharedNode newTag parent) :=
      GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree child parent parentNode (sharedNode newTag parent) vacant present
    obtain ⟨node,nodePresent,tag,edge,hidden⟩ := transfer _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
      (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) child (sharedNode newTag parent) newPresent
    refine ⟨child,(GeneralBorrowFreshMetadataChildSharedReuse.reuse input).freshLookup,⟨node,nodePresent,tag,edge,hidden⟩,?_⟩
    intro query oldNode old
    have different : query ≠ child := by
      intro same
      change tree.nodes.get query = some oldNode at old
      rw [same,vacant] at old
      contradiction
    obtain ⟨middle,middlePresent,oldTag,oldParent,oldHidden⟩ := old_attach tree child parent query parentNode (sharedNode newTag parent)
      oldNode present old (GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree child parent parentNode (sharedNode newTag parent) vacant present)
      (fun notParent => GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree child parent query parentNode (sharedNode newTag parent)
        vacant present notParent different)
    obtain ⟨next,found,nextTag,nextParent,nextHidden⟩ := transfer (GeneralBorrowFreshMetadataChildSharedReuse.stage input) _
      (GeneralBorrowFreshMetadataChildSharedReuse.shape input) (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) query middle middlePresent
    exact ⟨next,found,nextTag.trans oldTag,nextParent.trans oldParent,nextHidden.trans oldHidden⟩
end DuplicatePrefix.GeneralBorrowSharedChildGraph
