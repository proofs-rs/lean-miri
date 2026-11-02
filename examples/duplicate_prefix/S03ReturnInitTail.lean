import duplicate_prefix.S03IntegerZeroState
import duplicate_prefix.S03ReturnProtectionMetadata

namespace DuplicatePrefix.S03ReturnInitTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Exact shared post-argument source tail. Branch-specific protection proves
its equation before this local composition lemma is used. -/
theorem after_protection
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (protect : TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag limits.retag place
      (Storage.withCurrent frames {frame with location := .unwinding ⟨601⟩} before) =
      .ok () (S04ProtectUninit.finished before place input frames {frame with location := .unwinding ⟨601⟩}
        borrowFrame fresh tree updated))
    (body : frame.body = RootBody.reflected.body.body) (localSize : frame.locals.size = 25)
    (dead0 : (frame.locals[0]'(by omega)).value = .dead)
    (dead6 : (frame.locals[6]'(by omega)).value = .dead)
    (dead13 : (frame.locals[13]'(by omega)).value = .dead)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    RootEntryTail.tail (ExecutionMachine.callHooks (config options remaining span) limits) place
      (Storage.withCurrent frames frame before) =
      .ok () (Storage.withCurrent frames
        (CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame
          {frame with location := .unwinding ⟨601⟩} borrowFrame input.id input.tracker.global.nextPointerTag
            with location := .unwinding ⟨559⟩})
        (S04ProtectUninit.finished before place input frames {frame with location := .unwinding ⟨601⟩}
          borrowFrame fresh tree updated).machine) := by
  let changed := {frame with location := FrameLocation.unwinding ⟨601⟩}
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
end DuplicatePrefix.S03ReturnInitTail
