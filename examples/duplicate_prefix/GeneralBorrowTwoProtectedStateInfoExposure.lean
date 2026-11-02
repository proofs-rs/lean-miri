import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableOld
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoExposure
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def OnlyTag (tree : BorrowTree) (tag : BorTag) : Prop :=
  ∀ index node,tree.nodeAt index = some node → node.isExposed = true → node.tag = tag

theorem shape (before after : BorrowTree) (tag : BorTag)
    (same : treeShape after = treeShape before)
    (flags : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (initial : OnlyTag before tag) : OnlyTag after tag := by
  intro index node found exposed
  obtain ⟨old,present,tagEq,flagEq⟩ := GeneralBorrowFreshMetadataChildMutableOld.transfer after before same.symm flags.symm index node found
  exact tagEq.symm.trans (initial index old present (flagEq.trans exposed))

theorem staged (tree : BorrowTree) (tag : BorTag) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (present : tree.nodeAt parent = some parentNode) (different : index ≠ parent)
    (hidden : newNode.isExposed = false) (initial : OnlyTag tree tag) :
    OnlyTag (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations) tag := by
  intro query node found exposed
  change ((tree.nodes.insert index newNode).insert parent {parentNode with children := parentNode.children.push index}).get query = some node at found
  by_cases isParent : query = parent
  · subst query
    rw [GeneralBorrowFreshLocation.get_same] at found
    cases found
    exact initial parent parentNode present exposed
  · rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent] at found
    by_cases isIndex : query = index
    · subst query
      rw [GeneralBorrowFreshLocation.get_same] at found
      cases found
      rw [hidden] at exposed
      cases exposed
    · rw [GeneralBorrowFreshLocation.get_other _ index query _ isIndex] at found
      exact initial query node found exposed

theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input) (tag : BorTag)
    (initial : OnlyTag input.tree tag) : OnlyTag (GeneralBorrowFreshMetadataChildMutable.result input) tag := by
  apply shape (GeneralBorrowFreshMetadataChildMutable.stage input) _ tag (GeneralBorrowFreshMetadataChildMutable.shape input)
    (GeneralBorrowFreshMetadataChildMutable.exposure input)
  apply staged input.tree tag (GeneralBorrowFreshMetadataChildMutable.index input) input.parent input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) _ _ input.parentPresent
  · intro same
    have bound := GeneralBorrowNodeUpdate.lookup_valid input.tree.nodes input.parent input.parentNode input.parentPresent
    rw [←same,GeneralBorrowFreshMetadataChildMutable.at_end input] at bound
    omega
  · rfl
  · exact initial

theorem mark (tree after : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (nodes : after.nodes = tree.nodes.insert index {node with isExposed := true})
    (tagged : node.tag = tag) (initial : OnlyTag tree tag) : OnlyTag after tag := by
  intro query value found exposed
  change after.nodes.get query = some value at found
  rw [nodes] at found
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowFreshLocation.get_same] at found
    cases found
    exact tagged
  · rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
    exact initial query value found exposed
end DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoExposure
