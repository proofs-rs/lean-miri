import duplicate_prefix.S02SameDestinationAcceptedDefaultLookup
import duplicate_prefix.S02FnEntryBinding
import duplicate_prefix.GeneralBorrowRawMutableParentRestore
import duplicate_prefix.GeneralBorrowRawDefaultOrder
import duplicate_prefix.GeneralBorrowRawFnEntryOrder
namespace DuplicatePrefix.S02SameDestinationAcceptedCopyMetadata
open Miri Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The exact release and both actual range accesses preserve the tag mapping. -/
theorem copy_tags (packet : GeneralBorrowRawAsMutToCopy.Input) :
    let released := (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
    let read := released.performBorrowAccessRange (.concrete packet.tag) (Size.ofBytes packet.offset) (Size.ofBytes packet.count)
      .Read (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete packet.tag) (Size.ofBytes (packet.offset+packet.count)) (Size.ofBytes packet.count)
      .Write (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags .VisitChildrenOfAccessed
    write.tree.tagMapping = packet.entry.allocation.extra.tagMapping := by
  obtain ⟨input,_,_,_⟩ := GeneralBorrowRawAsMutCopyResources.copy_input packet
  have operations := GeneralBorrowRawCopyInput.accesses _ _ _ _ _ _ input
  have release := GeneralBorrowStructuralReleaseGeometryFrame.release packet.entry.allocation.extra packet.tracker.global.protectedTags packet.tag
  have releaseTags := congrArg BorrowTree.tagMapping release
  exact operations.2.1.tags.trans (operations.1.tags.trans releaseTags)

/-- Unconditional initial parent order and every old mapped tag survive both
actual mutable constructors and the current copy graph. -/
theorem current (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (ordered : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
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
    (current : BorrowTree) (nodes : current.nodes = packet.entry.allocation.extra.nodes)
    (tags : current.tagMapping = packet.entry.allocation.extra.tagMapping) :
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder current ∧
    (∀ tag query, tree.indexOfTag tag = some query → current.indexOfTag tag = some query) := by
  let expr := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
  let advanced := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  obtain ⟨exprRuntime,_capacity,_short,next,nextTag,_selected,_maximum,nextOffset,nextLen⟩ := GeneralBorrowRawDefaultResources.resources tree tracker runtime input headroom tagsRoom
  have exprOrder := GeneralBorrowRawDefaultOrder.order tree tracker runtime input ordered
  have helperOrder := GeneralBorrowRawFnEntryOrder.order expr advanced {} allocation exprRuntime next exprOrder
  simp only [nextTag,nextOffset,nextLen] at helperOrder
  constructor
  · unfold GeneralBorrowWildcardParentTagOrder.ParentTagOrder
    rw [nodes,resources.treeEq]
    exact helperOrder
  · intro tag query mapped
    have exprMapped := S02SameDestinationAcceptedDefaultLookup.mapped tree tracker runtime input tag query mapped
    have helperMapped := S02FnEntryBinding.mapped expr advanced {} allocation exprRuntime next tag query exprMapped
    simp only [nextTag,nextOffset,nextLen] at helperMapped
    unfold BorrowTree.indexOfTag
    rw [tags,resources.treeEq]
    exact helperMapped
end
end DuplicatePrefix.S02SameDestinationAcceptedCopyMetadata
