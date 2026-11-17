import duplicate_prefix.LanguageZeroDone
import duplicate_prefix.LanguageZeroCallCore
import duplicate_prefix.LanguageZeroSpans
import duplicate_prefix.CallEntryLocals
import duplicate_prefix.ScopedFrame

/-! Actual no-argument tail of `Call.initStackFrame` for the runtime guard.
    The source FnEntry retag scope is retained and reduces to its empty loop. -/
namespace DuplicatePrefix.LanguageZeroTail
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev Hooks := LanguageZeroCallCore.Hooks

noncomputable def spanAt (h : Hooks) (span : SpanRef) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let frame ← h.getFrame
  h.setFrame {frame with location := .unwinding span}

noncomputable def action (h : Hooks) (destinationOp : OpTy Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (_, calleeIndex) ← h.withRetagMode () .FnEntry (pure (0,0))
  spanAt h (← h.localSpan CopyPreconditions.Bodies.checkLanguage.loaded.body 0)
  unless ← h.checkArgumentCompat () GuardCompilerFacts.languageAbi.ret GuardCompilerFacts.languageAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  LanguageZeroCallCore.require (calleeIndex == GuardCompilerFacts.languageAbi.args.size)
    "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit ()
  h.pushDone ()

theorem core_eq (h : Hooks) (destination : RuntimeStackPlace Provenance) :
    LanguageZeroCallCore.core h destination = (do
      let destinationOp ← h.placeToOp () destination
      h.pushRaw () GuardCompilerFacts.languageCall.callee CopyPreconditions.Bodies.checkLanguage.loaded
        destination (.goto (some 1) .Continue)
      action h destinationOp) := by
  unfold LanguageZeroCallCore.core action
  simp only [bind_assoc]
  rfl

theorem action_actual (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (preamble : SpanRef) (located : frame.location = .unwinding preamble)
    (trackNone : frame.trackCallerArg = none)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = GuardCompilerFacts.languageCall.callee)
    (destinationOp : OpTy Provenance) (immediate : ∃ value, destinationOp.op = .immediate value)
    (valid : 0 < frame.locals.size) (dead : frame.locals[0].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (retEq : GuardCompilerFacts.languageAbi.ret = GuardCompilerFacts.languageAbi.ret) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      destinationOp (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (LanguageZeroDone.doneFrame frame) machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span frames frame machine
  have trackFrame : {frame with trackCallerArg := none} = frame := by rw [← trackNone]
  rw [located] at trackFrame
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span frames frame frame machine
  have scopeFact : h.withRetagMode () .FnEntry (EStateM.pure (0,0)) (Storage.withCurrent frames frame machine) =
      .ok (0,0) (Storage.withCurrent frames frame machine) := by
    change MachineHooks.withRetagMode .FnEntry (EStateM.pure (0,0)) _ = _
    apply ScopedFrame.same_machine (EStateM.pure (0,0)) frames frame frame machine tracker .FnEntry (0,0) tracked
    simp [ScopedFrame.entered, pure, EStateM.pure]
  have localSpan := LanguageZeroSpans.actual_local_span options limits (remaining+1) span frames frame machine
    body identity callee
  have setLocal := CallEntryLocals.set_span options limits (remaining+1) span frames frame machine
    ⟨LanguageZeroSpans.spanIndex⟩
  change spanAt h ⟨LanguageZeroSpans.spanIndex⟩ (Storage.withCurrent frames frame machine) = _ at setLocal
  have compat : h.checkArgumentCompat () GuardCompilerFacts.languageAbi.ret GuardCompilerFacts.languageAbi.ret
      (Storage.withCurrent frames {frame with location := .unwinding ⟨LanguageZeroSpans.spanIndex⟩} machine) =
      .ok true (Storage.withCurrent frames {frame with location := .unwinding ⟨LanguageZeroSpans.spanIndex⟩} machine) := by
    change (PreparedContracts.actualConfig options () (remaining+1) span).calls.compiler.checkArgumentCompat
      () GuardCompilerFacts.languageAbi.ret GuardCompilerFacts.languageAbi.ret _ = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).callCompiler]
    rw [retEq]
    exact GuardCompilerFacts.language_return_compat _ options.compatibilityBudget _
  let frameAtSpan := {frame with location := .unwinding (⟨LanguageZeroSpans.spanIndex⟩ : SpanRef)}
  have setPreamble := CallEntryLocals.set_span options limits (remaining+1) span frames frameAtSpan machine preamble
  change spanAt h preamble (Storage.withCurrent frames frameAtSpan machine) = _ at setPreamble
  have done := LanguageZeroDone.push_done options limits (remaining+1) span frames frame machine body valid dead noClocks
  unfold action
  simp only [bind, EStateM.bind]
  rw [getFrame]
  dsimp only
  rw [located]
  simp only [pure, EStateM.pure, bind, EStateM.bind]
  rw [trackFrame, setFrame]
  simp only [bind, EStateM.bind]
  rw [scopeFact]
  simp only [bind, EStateM.bind]
  rw [localSpan]
  simp only [bind, EStateM.bind]
  rw [setLocal]
  simp only [bind, EStateM.bind]
  rw [compat]
  simp only [ite_true, bind, EStateM.bind]
  rcases immediate with ⟨value, opEq⟩
  simp only [opEq, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind]
  rw [setPreamble]
  simp only [bind, EStateM.bind]
  have argsSize : GuardCompilerFacts.languageAbi.args.size = 0 := by
    have h := congrArg (fun x => x.1.size) GuardCompilerFacts.language_abi_shape
    simpa using h
  simp only [LanguageZeroCallCore.require, argsSize, Nat.reduceBEq, Bool.true_eq_false,
    ↓reduceIte, pure, EStateM.pure, bind, EStateM.bind]
  have afterFrame : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).afterFrameInit ()
      (Storage.withCurrent frames {frameAtSpan with location := .unwinding preamble} machine) =
      .ok () (Storage.withCurrent frames {frameAtSpan with location := .unwinding preamble} machine) := by rfl
  rw [afterFrame]
  simp only [EStateM.bind]
  have pushDone : h.pushDone () (Storage.withCurrent frames
      {frameAtSpan with location := .unwinding preamble} machine) =
      CallMachine.pushDone (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle
        (Storage.withCurrent frames {frameAtSpan with location := .unwinding preamble} machine) := by rfl
  rw [pushDone]
  have frameEq : {frameAtSpan with location := .unwinding preamble} = frame := by
    cases frame
    simp_all [frameAtSpan]
  rw [frameEq]
  exact done

end
end DuplicatePrefix.LanguageZeroTail

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.LanguageZeroTail.core_eq,
      ``DuplicatePrefix.LanguageZeroTail.action_actual] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved runtime zero tail dependency {dependency}"
