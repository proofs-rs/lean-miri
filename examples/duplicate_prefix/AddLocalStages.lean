import duplicate_prefix.AddSpans
import duplicate_prefix.CallEntryLocals
namespace DuplicatePrefix.AddLocalStages
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CallEntryLocals
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem layout1 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee)
    (valid : 1 < frame.locals.size) (uncached : frame.locals[1].layout = none) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localLayout () 1
      (Storage.withCurrent frames frame machine) =
      .ok CopyCompilerFacts.destPointerLayout
        (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame 1 CopyCompilerFacts.destPointerLayout valid) machine) := by
  apply layout_uncached _ () frames frame machine 1 CopyCompilerFacts.destPointerLayout valid uncached
  change (PreparedContracts.actualConfig options () remaining span).compiler.layout () 1 _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).layout]
  exact AddLocals.compute_local1 frames frame machine body identity callee


theorem layout2 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee)
    (valid : 2 < frame.locals.size) (uncached : frame.locals[2].layout = none) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localLayout () 2
      (Storage.withCurrent frames frame machine) =
      .ok RootCompilerFacts.usizeLayout
        (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame 2 RootCompilerFacts.usizeLayout valid) machine) := by
  apply layout_uncached _ () frames frame machine 2 RootCompilerFacts.usizeLayout valid uncached
  change (PreparedContracts.actualConfig options () remaining span).compiler.layout () 2 _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).layout]
  exact AddLocals.compute_local2 frames frame machine body identity callee


theorem span0 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      HelperCompilerFacts.addBody.body 0 (Storage.withCurrent frames frame machine) =
      .ok ⟨615⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact AddSpans.local0_span frames frame machine body identity callee


theorem span1 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      HelperCompilerFacts.addBody.body 1 (Storage.withCurrent frames frame machine) =
      .ok ⟨616⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact AddSpans.local1_span frames frame machine body identity callee

theorem span2 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      HelperCompilerFacts.addBody.body 2 (Storage.withCurrent frames frame machine) =
      .ok ⟨617⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact AddSpans.local2_span frames frame machine body identity callee

end DuplicatePrefix.AddLocalStages
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AddLocalStages.layout1, ``DuplicatePrefix.AddLocalStages.span0, ``DuplicatePrefix.AddLocalStages.span1, ``DuplicatePrefix.AddLocalStages.span2, ``DuplicatePrefix.AddLocalStages.layout2] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata local-stage dependency {dependency}"
