import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame
import duplicate_prefix.GeneralBorrowFreshRootScopedAsMutCopyLedger
import duplicate_prefix.GeneralBorrowFreshRootScopedMutableEdges
import duplicate_prefix.GeneralBorrowFreshRootScopedAsMutCopyResources
import duplicate_prefix.GeneralBorrowFreshRootScopedParentReanchor
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedMutableParentRestore
open Miri Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Read/Write copy and actual protector release leave exact node metadata. -/
theorem copy_nodes (packet : GeneralBorrowFreshRootScopedAsMutToCopy.Input) :
    let released := (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
    let read := released.performBorrowAccessRange (.concrete packet.tag) (Size.ofBytes packet.offset) (Size.ofBytes packet.count)
      .Read (GeneralBorrowFreshRootScopedAsMutToCopy.held packet).global.protectedTags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete packet.tag) (Size.ofBytes (packet.offset+packet.count)) (Size.ofBytes packet.count)
      .Write (GeneralBorrowFreshRootScopedAsMutToCopy.held packet).global.protectedTags .VisitChildrenOfAccessed
    write.tree.nodes = packet.entry.allocation.extra.nodes := by
  obtain ⟨input,_,_,_⟩ := GeneralBorrowFreshRootScopedAsMutCopyResources.copy_input packet
  have operations := GeneralBorrowFreshRootScopedCopyInput.accesses _ _ _ _ _ _ input
  have releaseFrame := GeneralBorrowStructuralReleaseGeometryFrame.release packet.entry.allocation.extra packet.tracker.global.protectedTags packet.tag
  have releaseNodes := congrArg BorrowTree.nodes releaseFrame
  exact operations.2.1.nodes.trans (operations.1.nodes.trans releaseNodes)

/-- Reanchor the current full post-copy child capability through both actual
mutable temporary edges to the original call-time source. Both temporary-tag
absences are derived from fresh allocation and real singleton endCall. -/
theorem restore (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (packet : GeneralBorrowFreshRootScopedAsMutToCopy.Input)
    (secondFresh : (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag.value < 18446744073709551615)
    (resources : GeneralBorrowFreshRootScopedAsMutCopyLedger.Resources
      (GeneralBorrowFreshRootScopedFnEntryArgument.finalTree
        (GeneralBorrowFreshRootScopedDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
        (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag input.offset input.len)
      (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) secondFresh)
        (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag)
      (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag packet)
    (packetId : packet.id = allocation)
    (current : BorrowTree) (nodes : current.nodes = packet.entry.allocation.extra.nodes)
    (currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts current (GeneralBorrowFreshRootScopedAsMutToCopy.held packet).global)
    (positive : GeneralBorrowFreshRootScopedRow.Positive current (GeneralBorrowFreshRootScopedAsMutToCopy.held packet).global.protectedTags
      packet.anchor packet.selected packet.maximum packet.offset packet.len) :
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive current (GeneralBorrowFreshRootScopedAsMutToCopy.held packet).global.protectedTags
      input.parent packet.selected packet.maximum packet.offset packet.len) := by
  have initialEdges := GeneralBorrowFreshRootScopedMutableEdges.edges tree tracker allocation runtime input headroom tagsRoom
  dsimp only at initialEdges
  obtain ⟨fresh,parent,child,parentNode,childNode,parentLookup,childLookup,parentPresent,childPresent,parentTag,parentEdge,childTag,childEdge,parentAbsent,childAbsent⟩ := initialEdges
  have packetLookup := packet.tagged
  rw [resources.treeEq,resources.tagEq] at packetLookup
  have sameChild : child = packet.anchor := Option.some.inj (childLookup.symm.trans packetLookup)
  subst child
  have currentChild : current.nodeAt packet.anchor = some childNode := by
    change current.nodes.get packet.anchor = some childNode
    rw [nodes,resources.treeEq]
    exact childPresent
  have currentParent : current.nodeAt parent = some parentNode := by
    change current.nodes.get parent = some parentNode
    rw [nodes,resources.treeEq]
    exact parentPresent
  have protectionFrame : (GeneralBorrowFreshRootScopedAsMutToCopy.held packet).global.protectedTags =
      ((TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) fresh)
        (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag).global.endCall
          (({} : FrameState).addProtector allocation (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag)).protectedTags := by
    unfold GeneralBorrowFreshRootScopedAsMutToCopy.held
    rw [resources.trackerEq,resources.tagEq,packetId]
  apply GeneralBorrowFreshRootScopedParentReanchor.twice current _ currentRuntime packet.anchor parent input.parent packet.selected packet.maximum packet.offset packet.len
    childNode parentNode currentChild currentParent childEdge parentEdge _ _ positive
  · rw [protectionFrame];exact childAbsent
  · rw [protectionFrame];exact parentAbsent
end DuplicatePrefix.GeneralBorrowFreshRootScopedMutableParentRestore
