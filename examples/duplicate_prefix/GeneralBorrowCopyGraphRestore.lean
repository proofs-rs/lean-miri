import duplicate_prefix.GeneralBorrowExposedScopedTwoWriteReadRestore
import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowCopyGraphRestore
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem restore (before after : BorrowTree) (frame : after={before with locations:=after.locations})
    (protections : ProtectedTags) (child expr target selected head : UniIndex) (tail : List UniIndex) (tag : BorTag)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags before) (covered : GeneralBorrowGraph.RootsCover before)
    (short : before.nodes.size<65536) (fits : before.nodes.data.size≤4294967296)
    (targetNode exprNode childNode : TreeNode)
    (targetPresent : before.nodeAt target=some targetNode) (targetTag : targetNode.tag=tag) (targetHidden : targetNode.isExposed=false)
    (exprPresent : before.nodeAt expr=some exprNode) (exprFree : protections.contains exprNode.tag=false)
    (childPresent : before.nodeAt child=some childNode) (childFree : protections.contains childNode.tag=false)
    (paths : ∀ location,(source_normal_projection before location protections).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection before location protections).topology.ancestorPath target.toNat)
    (context : GeneralBorrowExposedKnownRootRangeData.Context before child selected head tail)
    (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedLeafWriteReadClosed.Data after location protections child selected head tail)) lower upper after.locations) :
    GeneralBorrowGcAllocator.NodeTags after ∧ GeneralBorrowGraph.RootsCover after ∧ after.nodes.size<65536 ∧ after.nodes.data.size≤4294967296 ∧
      after.indexOfTag tag=some target ∧
      (∃ targetNode,after.nodeAt target=some targetNode ∧ targetNode.tag=tag ∧ targetNode.isExposed=false) ∧
      Nonempty (GeneralBorrowExposedKnownRootRangeData.Context after target selected head tail) ∧
      (∀ kind,GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
        (GeneralBorrowExposedKnownRootRangeData.Data after location protections target selected head tail kind)) lower upper after.locations) := by
  have afterTags : GeneralBorrowGcAllocator.NodeTags after := by rw [frame];exact nodeTags
  have targetAfter : after.nodeAt target=some targetNode := by rw [frame];exact targetPresent
  have exprAfter : after.nodeAt expr=some exprNode := by rw [frame];exact exprPresent
  have childAfter : after.nodeAt child=some childNode := by rw [frame];exact childPresent
  have pathsAfter (location : LocationTree) : (source_normal_projection after location protections).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection after location protections).topology.ancestorPath target.toNat := by rw [frame];exact paths location
  have contextAfter : GeneralBorrowExposedKnownRootRangeData.Context after child selected head tail := by
    rw [frame]
    exact {
      anchorNode:=context.anchorNode
      selectedNode:=context.selectedNode
      anchorPresent:=context.anchorPresent
      selectedPresent:=context.selectedPresent
      roots:=context.roots
      depth:=context.depth
      children:=context.children
      tags:=context.tags }
  have restored:=GeneralBorrowExposedScopedTwoWriteReadRestore.owned_on after protections child expr target selected head tail contextAfter
    targetNode exprNode childNode targetAfter exprAfter exprFree childAfter childFree pathsAfter lower upper owned
  have tagged : after.indexOfTag tag=some target := by
    have lookup:=afterTags target targetNode targetAfter
    change after.indexOfTag targetNode.tag=some target at lookup
    rw [targetTag] at lookup
    exact lookup
  refine ⟨afterTags,?_,?_,?_,tagged,⟨targetNode,targetAfter,targetTag,targetHidden⟩,restored.1,restored.2⟩
  · rw [frame];exact covered
  · rw [frame];exact short
  · rw [frame];exact fits
end DuplicatePrefix.GeneralBorrowCopyGraphRestore
