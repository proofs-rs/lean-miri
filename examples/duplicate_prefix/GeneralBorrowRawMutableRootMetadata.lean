import duplicate_prefix.GeneralBorrowRawMutableOldMetadata
import duplicate_prefix.GeneralBorrowRawMutableProtectors
import duplicate_prefix.GeneralBorrowRawMutablePolicyMetadata
namespace DuplicatePrefix.GeneralBorrowRawMutableRootMetadata
open Miri Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem order_transport (before after : BorrowTree) (selected : UniIndex)
    (nodes : after.nodes = before.nodes) (roots : after.roots = before.roots)
    (order : ∀ valid : 0 < before.roots.size, selected ≠ before.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder before) :
    ∀ valid : 0 < after.roots.size, selected ≠ after.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder after := by
  simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,nodes,roots] using order

/-- Derive all current ROOT release metadata from the phase-entry source node,
the actual constructor resource ledger and the exact post-copy graph frame. -/
theorem current (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (sourceNode : TreeNode) (sourcePresent : tree.nodeAt input.parent = some sourceNode)
    (hidden : sourceNode.isExposed = false)
    (packet : GeneralBorrowRawAsMutToCopy.Input)
    (secondFresh : (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag.value < 18446744073709551615)
    (resources : GeneralBorrowRawAsMutCopyLedger.Resources
      (GeneralBorrowRawFnEntryArgument.finalTree
        (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
        (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag input.offset input.len)
      (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) secondFresh)
        (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag)
      (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag packet)
    (packetId : packet.id = allocation) (selected : packet.selected = input.selected)
    (current : BorrowTree) (nodes : current.nodes = packet.entry.allocation.extra.nodes)
    (roots : current.roots = packet.entry.allocation.extra.roots) :
    (∃ node, current.nodeAt input.parent = some node ∧ node.tag = sourceNode.tag ∧ node.isExposed = false) ∧
    current.roots.toList.Nodup ∧ current.nodes.size < 65536 ∧
    (∀ valid : 0 < current.roots.size, packet.selected ≠ current.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder current) ∧
    (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags = tracker.global.protectedTags := by
  have old := GeneralBorrowRawMutableOldMetadata.old_node tree tracker allocation runtime input headroom tagsRoom input.parent sourceNode sourcePresent
  dsimp only at old
  obtain ⟨node,present,tag,exposed⟩ := old
  have presentCurrent : current.nodeAt input.parent = some node := by
    change current.nodes.get input.parent = some node
    rw [nodes,resources.treeEq]
    exact present
  have policy := GeneralBorrowRawMutablePolicyMetadata.metadata tree tracker allocation runtime input headroom tagsRoom
  dsimp only at policy
  have rootsEq : current.roots =
      (GeneralBorrowRawFnEntryArgument.finalTree
        (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
        (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag input.offset input.len).roots := by rw [roots,resources.treeEq]
  have nodesEq : current.nodes =
      (GeneralBorrowRawFnEntryArgument.finalTree
        (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
        (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag input.offset input.len).nodes := by rw [nodes,resources.treeEq]
  refine ⟨⟨node,presentCurrent,tag,exposed.trans hidden⟩,?_,?_,?_,?_⟩
  · rw [rootsEq];exact policy.1
  · rw [nodesEq];exact policy.2.1
  · have actual := order_transport _ current input.selected nodesEq rootsEq policy.2.2
    simpa only [selected] using actual
  · unfold GeneralBorrowRawAsMutToCopy.held
    rw [resources.trackerEq,resources.tagEq,packetId]
    exact GeneralBorrowRawMutableProtectors.unchanged tree tracker allocation runtime input headroom tagsRoom secondFresh
end DuplicatePrefix.GeneralBorrowRawMutableRootMetadata
