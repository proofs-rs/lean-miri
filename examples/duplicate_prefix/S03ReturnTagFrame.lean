import duplicate_prefix.S03ReturnChildMetadata
namespace DuplicatePrefix.S03ReturnTagFrame
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The actual protection Read, protected-child constructor and uninit Write
retain every different tag lookup, including absence. No success equation,
final tag map or canonical starting tree is assumed. -/
theorem run (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global) :
    let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
    let protectedTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let written := (protectedTree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write fullGlobal.protectedTags .VisitChildrenOfAccessed).tree
    ∀ tag, tracker.global.nextPointerTag ≠ tag → written.indexOfTag tag = tree.indexOfTag tag := by
  obtain ⟨_,_,_,registeredRuntime,⟨registeredPositive⟩,fresh⟩ := GeneralBorrowFnEntryRegistration.prepare tree tracker.global frame allocation
    input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,readRuntime,⟨readPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  have parentTagged : read.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  obtain ⟨parentNode,parentPresent⟩ := readPositive.sourcePresent input.parent rfl
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro equal;have p:=input.positive.positive;rw [equal] at p;contradiction
  obtain ⟨child,node,childTagged,childPresent,childTag,childParent,childLeaf,childHidden,oldLookup⟩ :=
    S03ReturnChildMetadata.construct read.tree registration.1 readRuntime input.parentTag tracker.global.nextPointerTag
      input.parent parentNode parentTagged parentPresent freshAfter room input.offset input.len nonzero readPositive.bounds
  let protectedTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  have childTagged' : protectedTree.indexOfTag tracker.global.nextPointerTag = some child := childTagged
  have childPresent' : protectedTree.nodeAt child = some node := childPresent
  have tagDifferent := S03EmptyReturnConstructorFacts.fresh_ne tree tracker.global.nextPointerTag input.parentTag input.parent fresh input.tagged
  have parentTagged' : protectedTree.indexOfTag input.parentTag = some input.parent :=
    (oldLookup input.parentTag tagDifferent).trans parentTagged
  let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  let written := (protectedTree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write fullGlobal.protectedTags .VisitChildrenOfAccessed).tree
  have writeFrame := GeneralBorrowFreshReadFrame.frame protectedTree (.concrete tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write fullGlobal.protectedTags .VisitChildrenOfAccessed
  change ∀ tag, tracker.global.nextPointerTag ≠ tag → written.indexOfTag tag = tree.indexOfTag tag
  intro tag different
  calc
    written.indexOfTag tag = protectedTree.indexOfTag tag := by
      unfold BorrowTree.indexOfTag
      rw [congrArg BorrowTree.tagMapping writeFrame]
    _ = read.tree.indexOfTag tag := oldLookup tag different
    _ = tree.indexOfTag tag := by
      unfold BorrowTree.indexOfTag
      rw [contract.tags]

end DuplicatePrefix.S03ReturnTagFrame
