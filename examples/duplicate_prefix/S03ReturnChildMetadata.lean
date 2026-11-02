import duplicate_prefix.S03EmptyReturnConstructorFacts
import duplicate_prefix.GeneralBorrowRawFnEntryResources

namespace DuplicatePrefix.S03ReturnChildMetadata
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The actual protected constructor supplies full new-child metadata and
retains every old tag binding, for append and sparse vacant-slot reuse. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child node, result.tree.indexOfTag newTag = some child ∧ result.tree.nodeAt child = some node ∧
      node.tag = newTag ∧ node.parent = some parent ∧ node.children = #[] ∧ node.isExposed = false ∧
      ∀ tag, newTag ≠ tag → result.tree.indexOfTag tag = tree.indexOfTag tag := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let metadata := GeneralBorrowFreshMetadataChildMutable.append input
    obtain ⟨node,nodePresent,nodeTag,nodeParent,nodeChildren,_,nodeHidden⟩ := metadata.newNode
    exact ⟨_,node,metadata.freshLookup,nodePresent,nodeTag,nodeParent,nodeChildren,nodeHidden,metadata.oldLookup⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    let metadata := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    obtain ⟨node,nodePresent,nodeTag,nodeParent,nodeChildren,_,nodeHidden⟩ := metadata.newNode
    exact ⟨_,node,metadata.freshLookup,nodePresent,nodeTag,nodeParent,nodeChildren,nodeHidden,metadata.oldLookup⟩

/-- Canonical return protection and its actual Write retain the original
concrete parent tag and produce the hidden return-child edge. No empty tag,
operation-success or future metadata is supplied by the caller. -/
theorem run (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global) :
    let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
    let protectedTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let written := (protectedTree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write fullGlobal.protectedTags .VisitChildrenOfAccessed).tree
    written.indexOfTag input.parentTag = some input.parent ∧
      ∃ child node, written.indexOfTag tracker.global.nextPointerTag = some child ∧
        written.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧
        node.parent = some input.parent ∧ node.children = #[] ∧ node.isExposed = false := by
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
    construct read.tree registration.1 readRuntime input.parentTag tracker.global.nextPointerTag
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
  refine ⟨?_,child,node,?_,?_,childTag,childParent,childLeaf,childHidden⟩
  · unfold BorrowTree.indexOfTag
    rw [congrArg BorrowTree.tagMapping writeFrame]
    exact parentTagged'
  · unfold BorrowTree.indexOfTag
    rw [congrArg BorrowTree.tagMapping writeFrame]
    exact childTagged'
  · change written.nodes.get child = some node
    rw [congrArg BorrowTree.nodes writeFrame]
    exact childPresent'

end DuplicatePrefix.S03ReturnChildMetadata
