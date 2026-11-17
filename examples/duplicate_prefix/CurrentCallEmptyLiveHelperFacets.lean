import duplicate_prefix.CurrentCallZeroSharedBoolFrame
namespace DuplicatePrefix.CurrentCallEmptyLiveHelperFacets
open Miri Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Two actual zero Shared constructors retain the Bool leaf and its write
activity. The source may gain children; only its current tag, hidden status
and quiescence are retained for release. -/
theorem two (tree : BorrowTree)
    (firstParent firstTag : BorTag) (first : EmptyForestSharedPool.Input tree firstParent firstTag)
    (secondParent secondTag : BorTag) (second : EmptyForestSharedPool.Input first.after secondParent secondTag)
    (target : UniIndex) (node : TreeNode) (present : tree.nodes.get target=some node)
    (firstDifferent : target≠first.parent) (secondDifferent : target≠second.parent)
    (lower upper : UInt64) (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper)
    (source : UniIndex) (sourceTag : BorTag) (sourceNode : TreeNode)
    (sourceTagged : tree.indexOfTag sourceTag=some source) (sourceAt : tree.nodes.get source=some sourceNode)
    (sourceHidden : sourceNode.isExposed=false) (quiet : S04ReturnReleaseInactive.Quiescent tree source) :
    (∃next,second.after.nodes.get target=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧next.children=node.children ∧next.isExposed=node.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin second.after target .Write lower upper ∧
    second.after.indexOfTag sourceTag=some source ∧
    (∃next,second.after.nodes.get source=some next ∧next.tag=sourceNode.tag ∧next.parent=sourceNode.parent ∧next.isExposed=false) ∧
    S04ReturnReleaseInactive.Quiescent second.after source := by
  obtain ⟨⟨middle,middleAt,middleTag,middleParent,middleChildren,middleExposed⟩,middleActive,middleQuiet⟩:=
    CurrentCallZeroSharedBoolFrame.facets tree firstParent firstTag first target node present firstDifferent lower upper active source quiet
  obtain ⟨⟨next,nextAt,nextTag,nextParent,nextChildren,nextExposed⟩,nextActive,nextQuiet⟩:=
    CurrentCallZeroSharedBoolFrame.facets first.after secondParent secondTag second target middle middleAt secondDifferent lower upper middleActive source middleQuiet
  obtain ⟨sourceMiddle,sourceMiddleAt,sourceMiddleTag,sourceMiddleParent,sourceMiddleExposed⟩:=S03EmptySharedFrame.old_node first source sourceNode sourceAt
  obtain ⟨sourceNext,sourceNextAt,sourceNextTag,sourceNextParent,sourceNextExposed⟩:=S03EmptySharedFrame.old_node second source sourceMiddle sourceMiddleAt
  exact ⟨⟨next,nextAt,nextTag.trans middleTag,nextParent.trans middleParent,nextChildren.trans middleChildren,nextExposed.trans middleExposed⟩,
    nextActive,S03EmptySharedFrame.tagged second sourceTag source (S03EmptySharedFrame.tagged first sourceTag source sourceTagged),
    ⟨sourceNext,sourceNextAt,sourceNextTag.trans sourceMiddleTag,sourceNextParent.trans sourceMiddleParent,sourceNextExposed.trans (sourceMiddleExposed.trans sourceHidden)⟩,nextQuiet⟩
end
end DuplicatePrefix.CurrentCallEmptyLiveHelperFacets
