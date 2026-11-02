import duplicate_prefix.S03LiveWildcardProtection
import duplicate_prefix.S03ReturnInitTail
namespace DuplicatePrefix.S03LiveWildcardInitTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification S03EmptyTagState
open TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
/-- Actual generic post-argument tail for an original wildcard return pointer.
Both incoming live argument provenances share this current zero-tag packet.
Protection, uninit and pushDone execute from current metadata internally. -/
theorem run
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : input.pointer.provenance = .wildcard)
    (zeroTag : BorTag) (zeroIndex : UniIndex) (zero : S03EmptyTagState.Data input.entry.allocation.extra zeroTag zeroIndex)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (owned : borrowFrame.protectedTags = #[(input.id,zeroTag)])
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat)
    (body : frame.body = RootBody.reflected.body.body) (localSize : frame.locals.size = 25)
    (dead0 : (frame.locals[0]'(by omega)).value = .dead)
    (dead6 : (frame.locals[6]'(by omega)).value = .dead)
    (dead13 : (frame.locals[13]'(by omega)).value = .dead)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    ∃ tree updated,
      let global := registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
      let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
        (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
      (RootEntryTail.tail (ExecutionMachine.callHooks (config options remaining span) limits) place
        (Storage.withCurrent frames frame before) =
        .ok () (Storage.withCurrent frames
          (CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame
            {frame with location := .unwinding ⟨601⟩} borrowFrame input.id input.tracker.global.nextPointerTag
              with location := .unwinding ⟨559⟩})
          (S04ProtectUninit.finished before place input frames {frame with location := .unwinding ⟨601⟩}
            borrowFrame fresh tree updated).machine) ∧
      updated.extra = written ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      written.locations.size = input.entry.allocation.extra.locations.size ∧
      written.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 ∧
      DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
      written.nodes.size < 65536 ∧ written.roots.toList.Nodup ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
      GeneralBorrowFreshRootSupportCutoff.ExposedBound written input.tracker.global.nextPointerTag ∧
      ∃ child, written.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        written.roots = input.entry.allocation.extra.roots.push child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive written global.protectedTags
          child child input.tracker.global.nextPointerTag input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write input.offset (input.offset+1) ∧
        ∃ node, written.nodeAt child = some node ∧ node.tag = input.tracker.global.nextPointerTag ∧
          node.parent = none ∧ node.children = #[] ∧ node.isExposed = false) ∧
      Nonempty (S03EmptyTagState.Data written zeroTag zeroIndex) ∧
      S04ReturnReleaseInactive.Quiescent written zeroIndex ∧
      (borrowFrame.addProtector input.id input.tracker.global.nextPointerTag).protectedTags =
        #[(input.id,zeroTag),(input.id,input.tracker.global.nextPointerTag)] ∧
      S04ReturnReleaseParent.HiddenFrame written (borrowFrame.addProtector input.id input.tracker.global.nextPointerTag) := by
  let changed := {frame with location := FrameLocation.unwinding ⟨601⟩}
  obtain ⟨tree,updated,⟨protect,properties⟩,zeroAfter,quietAfter,ownedAfter,hiddenAfter⟩ :=
    S03LiveWildcardProtection.invoke limits.retag before model place input runtime distinct order headroom fresh wildcard
      zeroTag zeroIndex zero frames changed borrowFrame frameBorrow owned sync extras outside
  have tail := S03ReturnInitTail.after_protection limits before model place input frames frame borrowFrame
    frameBorrow fresh tree updated protect body localSize dead0 dead6 dead13 dead14 noClocks identity callee
  exact ⟨tree,updated,⟨tail,properties⟩,zeroAfter,quietAfter,ownedAfter,hiddenAfter⟩

end
end DuplicatePrefix.S03LiveWildcardInitTail
