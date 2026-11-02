import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
namespace DuplicatePrefix.S02SameDestinationAcceptedHelperLeaf
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshGraph GeneralBorrowFreshChild GeneralBorrowNodeUpdate
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
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (oldNode : TreeNode) (old : tree.nodeAt query = some oldNode)
    (notParent : query ≠ parent) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true
    ∃ next,actual.tree.nodeAt query = some next ∧ next.tag = oldNode.tag ∧
      next.parent = oldNode.parent ∧ next.children = oldNode.children ∧ next.isExposed = oldNode.isExposed := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildMutable.index input
    have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
    have different : query ≠ child := by
      intro same
      have bounded := lookup_valid tree.nodes query oldNode old
      rw [same,atEnd] at bounded
      omega
    have stagePresent : (GeneralBorrowFreshMetadataChildMutable.stage input).nodeAt query = some oldNode := by
      exact (GeneralBorrowFreshGraph.other_lookup tree child parent query parentNode (GeneralBorrowFreshChild.child newTag parent)
        atEnd present notParent different).trans old
    exact transfer _ _ (GeneralBorrowFreshMetadataChildMutable.shape input) (GeneralBorrowFreshMetadataChildMutable.exposure input) query oldNode stagePresent
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have different : query ≠ child := by
      intro same
      change tree.nodes.get query = some oldNode at old
      rw [same,vacant] at old
      cases old
    have stagePresent : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodeAt query = some oldNode := by
      exact (GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree child parent query parentNode (GeneralBorrowFreshChild.child newTag parent)
        vacant present notParent different).trans old
    exact transfer _ _ (GeneralBorrowFreshMetadataChildMutableReuse.shape input) (GeneralBorrowFreshMetadataChildMutableReuse.exposure input) query oldNode stagePresent
end DuplicatePrefix.S02SameDestinationAcceptedHelperLeaf
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedHelperLeaf.construct) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved leaf constructor dependency {dependency}"
