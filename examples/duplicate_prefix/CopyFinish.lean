import duplicate_prefix.CopyDone
import duplicate_prefix.CopyEntryLocalStages
import duplicate_prefix.CopyCallCore
namespace DuplicatePrefix.CopyFinish
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def action (h : CopyCallCore.RootHooks) (preamble : MIR.SpanRef) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  CopyCallCore.spanAt h (← h.localSpan HelperCompilerFacts.copyBody.body 0)
  unless ← h.checkArgumentCompat () HelperCompilerFacts.copyAbi.ret HelperCompilerFacts.copyAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  CopyCallCore.spanAt h preamble
  let _ ← CopyCallCore.implicitAbi 3
  CopyCallCore.require (4 == HelperCompilerFacts.copyAbi.args.size) "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit ()
  h.pushDone ()

theorem finish (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (preamble : MIR.SpanRef)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (valid : 0 < frame.locals.size) (dead : frame.locals[0].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) preamble
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (CopyDone.doneFrame {frame with location := .unwinding preamble}) machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let f0 := {frame with location := .unwinding ⟨619⟩}
  let fp := {frame with location := .unwinding preamble}
  have query := CopyEntryLocalStages.local_span options limits remaining span frames frame machine body identity callee 0
  have set0 := CallEntryLocals.set_span options limits remaining span frames frame machine ⟨619⟩
  change CopyCallCore.spanAt h ⟨619⟩ (Storage.withCurrent frames frame machine) = _ at set0
  have compat : h.checkArgumentCompat () HelperCompilerFacts.copyAbi.ret HelperCompilerFacts.copyAbi.ret
      (Storage.withCurrent frames f0 machine) = .ok true (Storage.withCurrent frames f0 machine) := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    exact CopyEntryFacts.return_compat _ options.compatibilityBudget _
  have setp := CallEntryLocals.set_span options limits remaining span frames f0 machine preamble
  change CopyCallCore.spanAt h preamble (Storage.withCurrent frames f0 machine) = _ at setp
  have done := CopyDone.push_done options () remaining span frames fp machine body valid dead noClocks
  have implicitQuery : CopyCallCore.implicitAbi 3 =
      (pure (HelperCompilerFacts.copyAbi.args.getD 3 HelperCompilerFacts.copyAbi.ret) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (ArgAbi MIR.TyId)) := by
    unfold CopyCallCore.implicitAbi CopyCallCore.checkedAt
    have valid : 3 < HelperCompilerFacts.copyAbi.args.size := by rw [CopyCallFacts.abi_flags.2.2]; decide
    simp only [Array.getElem?_eq_getElem valid, Array.getD, valid, ↓reduceDIte]
    with_unfolding_all rfl
  change h.localSpan HelperCompilerFacts.copyBody.body 0 (Storage.withCurrent frames frame machine) = EStateM.Result.ok ⟨619⟩ (Storage.withCurrent frames frame machine) at query
  unfold action
  simp only [bind,EStateM.bind]
  rw [query]
  dsimp only
  rw [set0]
  dsimp only [f0] at compat setp
  dsimp only
  rw [compat]
  simp only [ite_true,EStateM.bind]
  rw [setp]
  dsimp only
  rw [implicitQuery]
  simp only [CopyCallCore.require, CopyCallFacts.abi_flags.2.2,
    Nat.reduceBEq, ↓reduceIte, pure,Pure.pure,EStateM.pure,
    ]
  exact done
end
end DuplicatePrefix.CopyFinish
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CopyFinish.finish) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata finish dependency {dependency}"
