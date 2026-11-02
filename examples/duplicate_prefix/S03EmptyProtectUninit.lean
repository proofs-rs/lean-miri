import duplicate_prefix.S03ReturnProtectionRaw
import duplicate_prefix.S03EmptyReturnBorrowFacts
import duplicate_prefix.S03ReturnChildMetadata
import duplicate_prefix.S04ReturnReleaseParent

namespace DuplicatePrefix.S03EmptyProtectUninit
open Miri Miri.Input Miri.Interpreter Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext S03EmptyTagState DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem hidden_tag (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (hidden : node.isExposed = false) :
    ∀ query value, tree.nodeAt query = some value → value.tag = tag → value.isExposed = false := by
  intro query value found sameTag
  have mapped := runtime.formed.allocator.nodeTags query value found
  rw [sameTag] at mapped
  have equal : query = index := Option.some.inj (mapped.symm.trans tagged)
  subst query
  have same : value = node := Option.some.inj (found.symm.trans present)
  exact same ▸ hidden

/-- The actual configured protect+uninit call now carries the empty tag's
produced release facts on the same returned allocation. Only residual local
headroom is used; no renewed whole-call resource budget is required. -/
theorem invoke_concrete
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (zeroTag : BorTag) (zeroIndex : UniIndex) (zero : Data input.entry.allocation.extra zeroTag zeroIndex)
    (different : ∀ anchor, input.source = some anchor → zeroIndex ≠ anchor)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (owned : borrowFrame.protectedTags = #[(input.id,zeroTag)])
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync, row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    ∃ updated,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
        (Storage.withCurrent frames frame before) =
        .ok () (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated) ∧
      updated.extra = written ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
      Nonempty (Data written zeroTag zeroIndex) ∧ S04ReturnReleaseInactive.Quiescent written zeroIndex ∧
      (borrowFrame.addProtector input.id input.tracker.global.nextPointerTag).protectedTags =
        #[(input.id,zeroTag),(input.id,input.tracker.global.nextPointerTag)] ∧
      S04ReturnReleaseParent.HiddenFrame written (borrowFrame.addProtector input.id input.tracker.global.nextPointerTag) ∧
      ∃ parent child node, written.indexOfTag tag = some parent ∧
        written.indexOfTag input.tracker.global.nextPointerTag = some child ∧ written.nodeAt child = some node ∧
        node.tag = input.tracker.global.nextPointerTag ∧ node.parent = some parent ∧ node.isExposed = false ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some child) input.selectedRoot input.maximum input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write input.offset (input.offset+1) := by
  obtain ⟨raw,parentTag,offset,length,_,_⟩ := S03ReturnProtectionRaw.packet input runtime distinct order headroom fresh tag concrete
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  obtain ⟨_,parent,source,parentTagged⟩ := binding
  have rawParent : raw.parent = parent := by
    have actual := raw.tagged
    rw [parentTag] at actual
    exact Option.some.inj (actual.symm.trans parentTagged)
  have notParent : zeroIndex ≠ raw.parent := by rw [rawParent];exact different parent source
  have facts := S03EmptyReturnBorrowFacts.run input.entry.allocation.extra input.tracker borrowFrame input.id runtime raw zeroTag zeroIndex zero notParent
  have metadata := S03ReturnChildMetadata.run input.entry.allocation.extra input.tracker borrowFrame input.id runtime raw
  simp only [parentTag,offset,length] at facts metadata
  obtain ⟨_,⟨afterZero⟩,quiet,child,node,childTagged,childPresent,childSame,childParent,_,childHidden⟩ := facts
  obtain ⟨updated,actual,extra,bytes,len,mutable,afterRuntime,afterOrder,owner,ownerTagged,positive,activity⟩ :=
    S03ReturnProtectionRaw.invoke_concrete budget before model place input runtime distinct order headroom fresh tag concrete
      frames frame borrowFrame frameBorrow sync extras outside
  have sameChild : owner = child := Option.some.inj (ownerTagged.symm.trans childTagged)
  subst owner
  have hiddenZero := hidden_tag _ _ afterRuntime zeroTag zeroIndex afterZero.node afterZero.tagged afterZero.present afterZero.hidden
  have hiddenReturn := hidden_tag _ _ afterRuntime input.tracker.global.nextPointerTag child node childTagged childPresent childHidden
  have protectedOwned : (borrowFrame.addProtector input.id input.tracker.global.nextPointerTag).protectedTags =
      #[(input.id,zeroTag),(input.id,input.tracker.global.nextPointerTag)] := by
    simp only [FrameState.addProtector,owned]
    rfl
  refine ⟨updated,actual,extra,bytes,len,mutable,afterRuntime,afterOrder,⟨afterZero⟩,quiet,protectedOwned,?_,raw.parent,child,node,?_,
    childTagged,childPresent,childSame,childParent,childHidden,positive,activity⟩
  · intro row member index value found sameTag
    rw [protectedOwned] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with equal | equal
    · subst row;exact hiddenZero index value found sameTag
    · subst row;exact hiddenReturn index value found sameTag
  · exact metadata.1

end
end DuplicatePrefix.S03EmptyProtectUninit
