import duplicate_prefix.GeneralBorrowSharedChildGraph
namespace DuplicatePrefix.S02SameDestinationRejectedResultLeaf
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
    ∃ next, after.nodeAt query = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧ next.children = node.children ∧ next.isExposed = node.isExposed := by
  obtain ⟨next,found,tag,parent,children,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape query node present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after exposure query
  change before.nodes.get query = some node at present
  rw [found,present] at flags
  exact ⟨next,found,tag,parent,children,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (oldNode : TreeNode) (old : tree.nodeAt query = some oldNode)
    (notParent : query ≠ parent) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen held
    ∃ next,actual.tree.nodeAt query = some next ∧ next.tag = oldNode.tag ∧
      next.parent = oldNode.parent ∧ next.children = oldNode.children ∧ next.isExposed = oldNode.isExposed := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildShared.index input
    have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
    have different : query ≠ child := by
      intro same
      have bounded := lookup_valid tree.nodes query oldNode old
      rw [same,atEnd] at bounded
      omega
    have stagePresent : (GeneralBorrowFreshMetadataChildShared.stage input).nodeAt query = some oldNode := by
      exact (GeneralBorrowFreshGraph.other_lookup tree child parent query parentNode (sharedNode newTag parent)
        atEnd present notParent different).trans old
    exact transfer _ _ (GeneralBorrowFreshMetadataChildShared.shape input) (GeneralBorrowFreshMetadataChildShared.exposure input) query oldNode stagePresent
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have different : query ≠ child := by
      intro same
      change tree.nodes.get query = some oldNode at old
      rw [same,vacant] at old
      cases old
    have stagePresent : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodeAt query = some oldNode := by
      exact (GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree child parent query parentNode (sharedNode newTag parent)
        vacant present notParent different).trans old
    exact transfer _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input) (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) query oldNode stagePresent
end DuplicatePrefix.S02SameDestinationRejectedResultLeaf
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResultLeaf.construct) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved leaf constructor dependency {dependency}"
