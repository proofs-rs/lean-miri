import duplicate_prefix.S03EmptyTagState
import duplicate_prefix.GeneralBorrowProtectedChildMetadata
import duplicate_prefix.GeneralBorrowProtectedSiblingActivityConstructor

namespace DuplicatePrefix.S03EmptyReturnConstructorFacts
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open S03EmptyTagState GeneralBorrowView GeneralBorrowSifa
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

theorem fresh_ne (tree : BorrowTree) (tag zeroTag : BorTag) (index : UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (tagged : tree.indexOfTag zeroTag = some index) : tag ≠ zeroTag := by
  have absent : tree.indexOfTag tag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh,Option.map_none]
  intro same
  rw [same,tagged] at absent
  cases absent

private theorem sifa (tree : BorrowTree) (tag : BorTag) (query start : UniIndex)
    (data : Data tree tag query) : Nonempty (Data (sourceUpdateSifa tree start .None).1 tag query) := by
  obtain ⟨node,present,same,parent,children,permission,hidden⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    tree start .None query data.node data.present
  refine ⟨⟨node,?_,present,same.trans data.sameTag,children.trans data.leaf,hidden.trans data.hidden,?_⟩⟩
  · unfold BorrowTree.indexOfTag
    rw [GeneralBorrowFreshMetadata.mapping tree _ (GeneralBorrowSifaView.preserves tree start .None)]
    exact data.tagged
  · exact S03EmptyTagState.shape tree _ (GeneralBorrowSifaView.preserves tree start .None) query data.inactive

theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input) (zeroTag : BorTag) (query : UniIndex)
    (data : Data input.tree zeroTag query) (notParent : query ≠ input.parent) :
    Nonempty (Data (GeneralBorrowFreshMetadataChildMutable.result input) zeroTag query) := by
  have notNew : query ≠ GeneralBorrowFreshMetadataChildMutable.index input := by
    intro equal
    have bound := GeneralBorrowNodeUpdate.lookup_valid input.tree.nodes query data.node data.present
    rw [equal,GeneralBorrowFreshMetadataChildMutable.at_end input] at bound
    omega
  have different := fresh_ne input.tree input.newTag zeroTag query input.fresh data.tagged
  have inactive := S03EmptyTagState.modified input.tree (GeneralBorrowFreshMetadataChildMutable.index input) query
    (Size.ofBytes input.offset) (Size.ofBytes input.len) GeneralBorrowFreshChild.inside notNew input.well input.bounds data.inactive
  have stageData : Data (GeneralBorrowFreshMetadataChildMutable.stage input) zeroTag query := by
    refine ⟨data.node,?_,?_,data.sameTag,data.leaf,data.hidden,inactive⟩
    · exact (GeneralBorrowTagMap.pushed_get_old input.tree.tagMapping input.newTag zeroTag different _ _).trans data.tagged
    · change ((input.tree.nodes.insert _ _).insert input.parent _).get query = some data.node
      rw [GeneralBorrowFreshLocation.get_other _ input.parent query _ notParent,
        GeneralBorrowFreshLocation.get_other _ (GeneralBorrowFreshMetadataChildMutable.index input) query _ notNew]
      exact data.present
  rw [GeneralBorrowFreshMetadataChildMutable.tree_eq]
  exact sifa _ zeroTag query input.parent stageData

theorem reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) (zeroTag : BorTag) (query : UniIndex)
    (data : Data input.tree zeroTag query) (notParent : query ≠ input.parent) :
    Nonempty (Data (GeneralBorrowFreshMetadataChildMutableReuse.result input) zeroTag query) := by
  have notNew : query ≠ input.index := by
    intro equal
    subst query
    have found := data.present
    rw [show input.tree.nodeAt input.index = none from input.vacant] at found
    cases found
  have different := fresh_ne input.tree input.newTag zeroTag query input.fresh data.tagged
  have inactive := S03EmptyTagState.modified input.tree input.index query
    (Size.ofBytes input.offset) (Size.ofBytes input.len) GeneralBorrowFreshChild.inside notNew input.well input.bounds data.inactive
  have stageData : Data (GeneralBorrowFreshMetadataChildMutableReuse.stage input) zeroTag query := by
    refine ⟨data.node,?_,?_,data.sameTag,data.leaf,data.hidden,inactive⟩
    · exact (GeneralBorrowTagMap.pushed_get_old input.tree.tagMapping input.newTag zeroTag different _ _).trans data.tagged
    · change ((input.tree.nodes.insert _ _).insert input.parent _).get query = some data.node
      dsimp only [GeneralBorrowFreshMetadataChildMutableReuse.index]
      rw [GeneralBorrowFreshLocation.get_other _ input.parent query _ notParent,
        GeneralBorrowFreshLocation.get_other _ input.index query _ notNew]
      exact data.present
  rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq]
  exact sifa _ zeroTag query input.parent stageData

/-- The actual protected positive constructor preserves the old empty tag's
inactive leaf and produces the return child's full edge/tag/hidden metadata. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag zeroTag : BorTag) (parent query : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (data : Data tree zeroTag query) (notParent : query ≠ parent) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    Nonempty (Data result.tree zeroTag query) ∧
      ∃ child node, result.tree.indexOfTag newTag = some child ∧ result.tree.nodeAt child = some node ∧
        node.tag = newTag ∧ node.parent = some parent ∧ node.children = #[] ∧ node.isExposed = false := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    obtain ⟨node,nodePresent,nodeTag,nodeParent,nodeChildren,_,nodeHidden⟩ := (GeneralBorrowFreshMetadataChildMutable.append input).newNode
    exact ⟨append input zeroTag query data notParent,_,node,(GeneralBorrowFreshMetadataChildMutable.append input).freshLookup,
      nodePresent,nodeTag,nodeParent,nodeChildren,nodeHidden⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    obtain ⟨node,nodePresent,nodeTag,nodeParent,nodeChildren,_,nodeHidden⟩ := (GeneralBorrowFreshMetadataChildMutableReuse.reuse input).newNode
    exact ⟨reuse input zeroTag query data notParent,_,node,(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).freshLookup,
      nodePresent,nodeTag,nodeParent,nodeChildren,nodeHidden⟩

end DuplicatePrefix.S03EmptyReturnConstructorFacts
