import duplicate_prefix.LenDone
import duplicate_prefix.LenLocalStages
import duplicate_prefix.LenCallCore
namespace DuplicatePrefix.LenFinish
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def action (h : RootCallCore.RootHooks) (preamble : MIR.SpanRef) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  LenCallCore.spanAt h (← h.localSpan LenHelper.body.body 0)
  unless ← h.checkArgumentCompat () LenHelper.abi.ret LenHelper.abi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  LenCallCore.spanAt h preamble
  LenCallCore.require (1 == LenHelper.abi.args.size) "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit ()
  h.pushDone ()

theorem finish (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (preamble : MIR.SpanRef)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (valid : 0 < frame.locals.size) (dead : frame.locals[0].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) preamble
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (LenDone.doneFrame {frame with location := .unwinding preamble}) machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let f0 := {frame with location := .unwinding ⟨LenSpans.span0⟩}
  let fp := {frame with location := .unwinding preamble}
  have query := LenLocalStages.span0 options limits remaining span frames frame machine body identity callee
  have set0 := CallEntryLocals.set_span options limits remaining span frames frame machine ⟨LenSpans.span0⟩
  change LenCallCore.spanAt h ⟨LenSpans.span0⟩ (Storage.withCurrent frames frame machine) = _ at set0
  have compat : h.checkArgumentCompat () LenHelper.abi.ret LenHelper.abi.ret
      (Storage.withCurrent frames f0 machine) = .ok true (Storage.withCurrent frames f0 machine) := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    exact LenEntryFacts.return_compat _ options.compatibilityBudget _
  have setp := CallEntryLocals.set_span options limits remaining span frames f0 machine preamble
  change LenCallCore.spanAt h preamble (Storage.withCurrent frames f0 machine) = _ at setp
  have done := LenDone.push_done options () remaining span frames fp machine body valid dead noClocks
  unfold action
  simp only [bind,EStateM.bind]
  rw [query]
  dsimp only
  rw [set0]
  dsimp only [f0] at compat setp
  dsimp only
  rw [compat]
  simp only [ite_true,bind,EStateM.bind]
  rw [setp]
  dsimp only
  simp only [LenCallCore.require, LenCallFacts.abi_flags.2.2,
    Nat.reduceBEq, Bool.true_eq_false, ↓reduceIte, pure,Pure.pure,EStateM.pure,
    bind,EStateM.bind]
  exact done
end
end DuplicatePrefix.LenFinish
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LenFinish.finish) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata finish dependency {dependency}"
