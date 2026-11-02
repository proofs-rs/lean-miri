import duplicate_prefix.CopyEntrySpans
namespace DuplicatePrefix.CopyEntryLocalStages
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
 theorem argument_layout (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) (index : Fin 3)
    (valid : index.val+1 < frame.locals.size) (uncached : frame.locals[index.val+1].layout = none) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localLayout () (index.val+1)
      (Storage.withCurrent frames frame machine) = .ok (CopyArgumentStage.layout index)
        (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame (index.val+1) (CopyArgumentStage.layout index) valid) machine) := by
  apply CallEntryLocals.layout_uncached _ () frames frame machine (index.val+1) (CopyArgumentStage.layout index) valid uncached
  change (PreparedContracts.actualConfig options () remaining span).compiler.layout () (index.val+1) _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).layout]
  exact CopyEntryLocals.compute_argument frames frame machine body identity callee index
 theorem local_span (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) (index : Fin 4) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan HelperCompilerFacts.copyBody.body index.val
      (Storage.withCurrent frames frame machine) = .ok ⟨CopyEntrySpans.spanAt index⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact CopyEntrySpans.local_span frames frame machine body identity callee index
end DuplicatePrefix.CopyEntryLocalStages
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyEntryLocalStages.argument_layout, ``DuplicatePrefix.CopyEntryLocalStages.local_span] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved copy entry local stage {dependency}"
