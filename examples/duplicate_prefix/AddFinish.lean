import duplicate_prefix.AddDone
import duplicate_prefix.AddLocalStages
import duplicate_prefix.AddCallCore
namespace DuplicatePrefix.AddFinish
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def action (h : RootCallCore.RootHooks) (preamble : MIR.SpanRef) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  AddCallCore.spanAt h (← h.localSpan HelperCompilerFacts.addBody.body 0)
  unless ← h.checkArgumentCompat () HelperCompilerFacts.addAbi.ret HelperCompilerFacts.addAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  AddCallCore.spanAt h preamble
  let _ ← AddCallCore.implicitAbi 2
  AddCallCore.require (3 == HelperCompilerFacts.addAbi.args.size) "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit ()
  h.pushDone ()

theorem finish (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (preamble : MIR.SpanRef)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee)
    (valid : 0 < frame.locals.size) (dead : frame.locals[0].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) preamble
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (AddDone.doneFrame {frame with location := .unwinding preamble}) machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let f0 := {frame with location := .unwinding ⟨615⟩}
  let fp := {frame with location := .unwinding preamble}
  have query := AddLocalStages.span0 options limits remaining span frames frame machine body identity callee
  have set0 := CallEntryLocals.set_span options limits remaining span frames frame machine ⟨615⟩
  change AddCallCore.spanAt h ⟨615⟩ (Storage.withCurrent frames frame machine) = _ at set0
  have compat : h.checkArgumentCompat () HelperCompilerFacts.addAbi.ret HelperCompilerFacts.addAbi.ret
      (Storage.withCurrent frames f0 machine) = .ok true (Storage.withCurrent frames f0 machine) := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    exact AddEntryFacts.return_compat _ options.compatibilityBudget _
  have setp := CallEntryLocals.set_span options limits remaining span frames f0 machine preamble
  change AddCallCore.spanAt h preamble (Storage.withCurrent frames f0 machine) = _ at setp
  have done := AddDone.push_done options () remaining span frames fp machine body valid dead noClocks
  have implicitQuery : AddCallCore.implicitAbi 2 =
      (pure (HelperCompilerFacts.addAbi.args.getD 2 HelperCompilerFacts.addAbi.ret) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (ArgAbi MIR.TyId)) := by
    unfold AddCallCore.implicitAbi AddCallCore.checkedAt
    have valid : 2 < HelperCompilerFacts.addAbi.args.size := by rw [AddCallFacts.abi_flags.2.2]; decide
    simp only [Array.getElem?_eq_getElem valid, Array.getD, valid, ↓reduceDIte]
    with_unfolding_all rfl
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
  rw [implicitQuery]
  simp only [AddCallCore.require, AddCallFacts.abi_flags.2.2,
    Nat.reduceBEq, Bool.true_eq_false, ↓reduceIte, pure,Pure.pure,EStateM.pure,
    bind,EStateM.bind]
  exact done
end
end DuplicatePrefix.AddFinish
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddFinish.finish) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata finish dependency {dependency}"
