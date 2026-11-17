import duplicate_prefix.LenSpans
import duplicate_prefix.CallEntryLocals
namespace DuplicatePrefix.LenLocalStages
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CallEntryLocals
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem layout1 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (valid : 1 < frame.locals.size) (uncached : frame.locals[1].layout = none) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localLayout () 1
      (Storage.withCurrent frames frame machine) =
      .ok LenHelper.rawLayout
        (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame 1 LenHelper.rawLayout valid) machine) := by
  apply layout_uncached _ () frames frame machine 1 LenHelper.rawLayout valid uncached
  change (PreparedContracts.actualConfig options () remaining span).compiler.layout () 1 _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).layout]
  exact LenLocals.compute_local1 frames frame machine body identity callee


theorem span0 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      LenHelper.body.body 0 (Storage.withCurrent frames frame machine) =
      .ok ⟨LenSpans.span0⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact LenSpans.local0_span frames frame machine body identity callee


theorem span1 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      LenHelper.body.body 1 (Storage.withCurrent frames frame machine) =
      .ok ⟨LenSpans.span1⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact LenSpans.local1_span frames frame machine body identity callee

end DuplicatePrefix.LenLocalStages
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.LenLocalStages.layout1, ``DuplicatePrefix.LenLocalStages.span0, ``DuplicatePrefix.LenLocalStages.span1] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata local-stage dependency {dependency}"
