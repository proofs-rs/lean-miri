import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.DuplicatePrefixTerminalStack

namespace DuplicatePrefix.DuplicatePrefixCompletedCallResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
noncomputable section

/-- Internal completed-trace adapter. Its execution facts must be derived by
the public caller theorem, never supplied as reference-validity assumptions.
Normal terminal false derives empty stack from the production driver; a full
successful trace then yields NoErrors, NoUB and every-prefix step success. -/
theorem of_trace (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (argument : DuplicatePrefixSliceArgument.Argument) (len count : UInt64)
    (place : MPlaceTy Provenance) (installed finalState : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (call : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining + 1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len),
        .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩, before⟩ = .ok () installed)
    (entry : CallSafety.IsCallEntry 1 installed)
    (trace : SuccessfulTrace.Trace (config options (remaining + 1) span) limits installed finalState)
    (terminal : ExecutionMachine.step (config options (remaining + 1) span) limits () finalState =
      (finalState, .ok false)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  let cfg := config options (remaining + 1) span
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨cfg, limits, fun _ _ => True⟩
  have empty : finalState.stack.frames = #[] :=
    DuplicatePrefixTerminalStack.terminal_empty (ExecutionMachine.stepHooks cfg limits) () finalState finalState terminal
  have returned : CallSafety.pastCallBoundary 1 finalState := by
    unfold CallSafety.pastCallBoundary CallSafety.frameDepth
    rw [empty]
    decide
  have noErrors : CallSafety.NoErrorsBeforeReturn context 1 installed :=
    SuccessfulTrace.no_errors context 1 installed finalState entry trace returned
  exact ⟨installed, finalState, call, trace, terminal, empty, noErrors,
    CallSafety.noErrors_implies_noUB context 1 installed noErrors,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.DuplicatePrefixCompletedCallResult
