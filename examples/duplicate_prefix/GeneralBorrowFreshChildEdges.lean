import duplicate_prefix.GeneralBorrowFreshParentTagOrder
import duplicate_prefix.GeneralBorrowProtectedChildMetadata
import duplicate_prefix.GeneralBorrowDefaultChildMetadata
namespace DuplicatePrefix.GeneralBorrowFreshChildEdges
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshGraph
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem retained (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode old : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (present : tree.nodeAt query = some old) :
    ∃ node, (attached tree index parent parentNode newNode).nodeAt query = some node ∧ node.tag = old.tag ∧ node.parent = old.parent := by
  by_cases same : query = parent
  · subst query
    cases Option.some.inj (present.symm.trans parentPresent)
    exact ⟨_,GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant parentPresent,rfl,rfl⟩
  · have different : query ≠ index := by intro equal;subst query;change tree.nodes.get index = some old at present;rw [vacant] at present;cases present
    exact ⟨old,(GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode newNode vacant parentPresent same different).trans present,rfl,rfl⟩

theorem old_staged (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (after : BorrowTree)
    (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape
      (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations))
    (query : UniIndex) (old : TreeNode) (present : tree.nodeAt query = some old) :
    ∃ node, after.nodeAt query = some node ∧ node.tag = old.tag ∧ node.parent = old.parent := by
  obtain ⟨staged,lookup,tag,parentEq⟩ := retained tree index parent query parentNode newNode old vacant parentPresent present
  have stageLookup : (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations).nodeAt query = some staged := lookup
  obtain ⟨node,nodePresent,nodeTag,nodeParent,_,_⟩ := GeneralBorrowFreshMetadata.node_fields _ after same query staged stageLookup
  exact ⟨node,nodePresent,nodeTag.trans tag,nodeParent.trans parentEq⟩

/-- Actual fresh child edge and all old tag/parent fields, for coherent allocator append or reuse. -/
theorem protected_child (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let after := GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag newTag offset len
    (∃ child node, after.indexOfTag newTag = some child ∧ after.nodeAt child = some node ∧
      node.tag = newTag ∧ node.parent = some parent) ∧
    (∀ query old, tree.nodeAt query = some old → ∃ node, after.nodeAt query = some node ∧
      node.tag = old.tag ∧ node.parent = old.parent) := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutable.append input
    obtain ⟨node,nodePresent,tag,parentEq,_,_,_⟩ := data.newNode
    refine ⟨⟨GeneralBorrowFreshMetadataChildMutable.index input,node,data.freshLookup,nodePresent,tag,parentEq⟩,?_⟩
    intro query old oldPresent
    exact old_staged tree _ parent parentNode _
      (GeneralBorrowFreshParentTagOrder.vacant_at_end tree _ (GeneralBorrowFreshMetadataChildMutable.at_end input))
      present _ _ _ (GeneralBorrowFreshMetadataChildMutable.shape input) query old oldPresent
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    obtain ⟨node,nodePresent,tag,parentEq,_,_,_⟩ := data.newNode
    refine ⟨⟨child,node,data.freshLookup,nodePresent,tag,parentEq⟩,?_⟩
    intro query old oldPresent
    exact old_staged tree child parent parentNode _ vacant present _ _ _
      (GeneralBorrowFreshMetadataChildMutableReuse.shape input) query old oldPresent

/-- Actual fresh child edge and all old tag/parent fields, for coherent allocator append or reuse. -/
theorem default_child (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let after := GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len
    (∃ child node, after.indexOfTag newTag = some child ∧ after.nodeAt child = some node ∧
      node.tag = newTag ∧ node.parent = some parent) ∧
    (∀ query old, tree.nodeAt query = some old → ∃ node, after.nodeAt query = some node ∧
      node.tag = old.tag ∧ node.parent = old.parent) := by
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefault.append input
    obtain ⟨node,nodePresent,tag,parentEq,_,_,_⟩ := data.newNode
    refine ⟨⟨GeneralBorrowFreshMetadataChildDefault.index input,node,data.freshLookup,nodePresent,tag,parentEq⟩,?_⟩
    intro query old oldPresent
    exact old_staged tree _ parent parentNode _
      (GeneralBorrowFreshParentTagOrder.vacant_at_end tree _ (GeneralBorrowFreshMetadataChildDefault.at_end input))
      present _ _ _ (GeneralBorrowFreshMetadataChildDefault.shape input) query old oldPresent
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
    obtain ⟨node,nodePresent,tag,parentEq,_,_,_⟩ := data.newNode
    refine ⟨⟨child,node,data.freshLookup,nodePresent,tag,parentEq⟩,?_⟩
    intro query old oldPresent
    exact old_staged tree child parent parentNode _ vacant present _ _ _
      (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) query old oldPresent
end DuplicatePrefix.GeneralBorrowFreshChildEdges
