import duplicate_prefix.S03EmptyReturnConstructorFacts
import duplicate_prefix.GeneralBorrowRawFnEntryResources

namespace DuplicatePrefix.S03EmptyReturnBorrowFacts
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open S03EmptyTagState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The real return-protection Read and positive protected constructor keep
an existing empty FnEntry tag inactive; the ensuing actual Write supplies the
pop scan's Quiescent condition. No post-operation capability is a premise. -/
theorem run (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (zeroTag : BorTag) (query : UniIndex) (data : Data tree zeroTag query) (notParent : query ≠ input.parent) :
    let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
    let protectedTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let written := (protectedTree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write fullGlobal.protectedTags .VisitChildrenOfAccessed).tree
    Nonempty (Data protectedTree zeroTag query) ∧ Nonempty (Data written zeroTag query) ∧
      S04ReturnReleaseInactive.Quiescent written query ∧
      ∃ child node, written.indexOfTag tracker.global.nextPointerTag = some child ∧
        written.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧
        node.parent = some input.parent ∧ node.children = #[] ∧ node.isExposed = false := by
  obtain ⟨_,_,_,registeredRuntime,⟨registeredPositive⟩,fresh⟩ := GeneralBorrowFnEntryRegistration.prepare tree tracker.global frame allocation
    input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  let afterRead := S03EmptyTagState.access tree registration.1 registeredRuntime zeroTag input.parentTag query input.parent input.selected input.maximum
    data notParent input.offset input.len registeredPositive input.tagged .Read .VisitChildrenOfAccessed
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
  obtain ⟨⟨afterConstruct⟩,child,node,childTagged,childPresent,childTag,childParent,childLeaf,childHidden⟩ :=
    S03EmptyReturnConstructorFacts.construct read.tree registration.1 readRuntime input.parentTag tracker.global.nextPointerTag zeroTag
      input.parent query parentNode parentTagged parentPresent freshAfter room input.offset input.len nonzero readPositive.bounds afterRead notParent
  let protectedTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  have protectedData : Data protectedTree zeroTag query := afterConstruct
  have childTagged' : protectedTree.indexOfTag tracker.global.nextPointerTag = some child := childTagged
  have childPresent' : protectedTree.nodeAt child = some node := childPresent
  obtain ⟨protectedRuntime,_,_,_,_,_,_,resourceChild,resourceTagged,⟨protectedPositive⟩,_⟩ :=
    GeneralBorrowRawFnEntryResources.resources tree tracker frame allocation runtime input
  have sameChild : resourceChild = child := Option.some.inj (resourceTagged.symm.trans childTagged')
  subst resourceChild
  have tagDifferent := S03EmptyReturnConstructorFacts.fresh_ne tree tracker.global.nextPointerTag zeroTag query fresh data.tagged
  have different : query ≠ child := by
    intro equal
    have found := childPresent'
    rw [←equal] at found
    have nodesEqual := Option.some.inj (found.symm.trans protectedData.present)
    have tagsEqual := congrArg TreeNode.tag nodesEqual
    rw [childTag,protectedData.sameTag] at tagsEqual
    exact tagDifferent tagsEqual
  let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  let written := (protectedTree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write fullGlobal.protectedTags .VisitChildrenOfAccessed).tree
  let afterWrite := S03EmptyTagState.access protectedTree fullGlobal protectedRuntime zeroTag tracker.global.nextPointerTag query child input.selected input.maximum
    protectedData different input.offset input.len protectedPositive childTagged' .Write .VisitChildrenOfAccessed
  have writeFrame := GeneralBorrowFreshReadFrame.frame protectedTree (.concrete tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write fullGlobal.protectedTags .VisitChildrenOfAccessed
  refine ⟨⟨protectedData⟩,⟨afterWrite⟩,?_,child,node,?_,?_,childTag,childParent,childLeaf,childHidden⟩
  · intro position valid state stored
    exact Or.inl (afterWrite.inactive position valid state stored)
  · unfold BorrowTree.indexOfTag
    rw [congrArg BorrowTree.tagMapping writeFrame]
    exact childTagged'
  · change written.nodes.get child = some node
    rw [congrArg BorrowTree.nodes writeFrame]
    exact childPresent'

end DuplicatePrefix.S03EmptyReturnBorrowFacts
