import duplicate_prefix.S03LiveEmptyState
import duplicate_prefix.RootEntryTail
import duplicate_prefix.RootEntryFinish
import duplicate_prefix.S03LiveEmptyResultMetadata

namespace DuplicatePrefix.S03LiveEmptyInitTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification S03EmptyTagState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The actual post-argument tail carries the produced zero-tag release packet
through return protection and pushDone. No completed tail is assumed. -/
theorem run
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (zeroTag : BorTag) (zeroIndex : UniIndex) (zero : S03EmptyTagState.Data input.entry.allocation.extra zeroTag zeroIndex)
    (different : ∀ anchor, input.source = some anchor → zeroIndex ≠ anchor)
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
    let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
      input.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    ∃ updated,
      RootEntryTail.tail (ExecutionMachine.callHooks (config options remaining span) limits) place
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
  let changed := {frame with location := FrameLocation.unwinding ⟨601⟩}
  obtain ⟨updated,protect,extra,bytes,length,mutable,properties⟩ := S03EmptyProtectUninit.invoke_concrete limits.retag before model place input
    runtime distinct order headroom fresh tag concrete zeroTag zeroIndex zero different frames changed borrowFrame frameBorrow owned sync extras outside
  have physical := S03LiveEmptyResultMetadata.physical limits.retag before model place input runtime distinct order headroom fresh
    tag concrete frames changed borrowFrame frameBorrow sync extras outside _ updated protect
  let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
  let protectedState := S04ProtectUninit.finished before place input frames changed borrowFrame fresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed borrowFrame input.id input.tracker.global.nextPointerTag
  have finish := RootEntryFinish.actual_finish options limits remaining span frames protectedFrame protectedState.machine
    body localSize dead0 dead6 dead13 dead14 noClocks
  have localSpan := CallEntryLocals.root_span0 options limits remaining span frames frame before body identity callee
  have getFrame := CallEntryLocals.get_frame options limits remaining span frames frame before
  have setFrame := CallEntryLocals.set_frame options limits remaining span frames frame changed before
  have compat : (ExecutionMachine.callHooks (config options remaining span) limits).checkArgumentCompat ()
      RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret (Storage.withCurrent frames changed before) =
      .ok true (Storage.withCurrent frames changed before) := by
    change (config options remaining span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () remaining span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  have protection : (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames changed before) = .ok () protectedState := protect
  refine ⟨updated,?_,extra,bytes,length,mutable,physical.1,physical.2.1,physical.2.2,properties⟩
  unfold RootEntryTail.tail RootCallCore.spanAt
  simp only [bind,EStateM.bind]
  rw [localSpan]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind]
  dsimp only [changed] at setFrame compat protection
  rw [setFrame]
  simp only [EStateM.bind]
  rw [compat]
  simp only [EStateM.bind,Bool.not_true,↓reduceIte,pure,EStateM.pure]
  rw [protection]
  simp only [EStateM.bind]
  exact finish

end
end DuplicatePrefix.S03LiveEmptyInitTail
