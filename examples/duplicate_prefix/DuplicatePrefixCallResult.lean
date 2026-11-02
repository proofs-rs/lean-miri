import duplicate_prefix.GenericFunctionPoolSafety
namespace DuplicatePrefix.DuplicatePrefixCallResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
noncomputable section
/-- Common call-time safety POSTCONDITION, independent of root shape, provenance
and history. It does not define admissible callers: no input-validity or coverage
claim follows merely from introducing this result. The canonical empty-stack
call boundary and fixed Unit choice remain explicit. No error, including an
Unsupported result or exhausted fuel, counts as successful execution. -/
def Result (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len count : UInt64) (place : MPlaceTy Provenance) : Prop :=
  let cfg := config options (remaining+1) span
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨cfg,limits,fun _ _=>True⟩
  ∃ installed finalState,
    Call.initStackFrame (ExecutionMachine.callHooks cfg limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        pointer len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
        .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩=.ok () installed ∧
    SuccessfulTrace.Trace cfg limits installed finalState ∧
    ExecutionMachine.step cfg limits () finalState=(finalState,.ok false) ∧
    finalState.stack.frames=#[] ∧
    CallSafety.NoErrorsBeforeReturn context 1 installed ∧
    CallSafety.NoUBBeforeReturn context 1 installed ∧
    (∀ reachableState,SuccessfulTrace.Trace cfg limits installed reachableState→
      ∃ next continuing,ExecutionMachine.step cfg limits () reachableState=(next,.ok continuing))

/-- Existing PoolInput already proves this common result for every count.
Its concrete positive single-root and other caller restrictions are retained;
this adapter neither strengthens them nor declares them ordinary validity. -/
theorem pool (s : GenericFunctionEntryCommon.PoolInput) (count : UInt64) :
    Result s.options s.limits s.remaining s.span s.before
      (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len count s.place := by
  obtain ⟨installed,finalState,call,trace,terminal,empty,safety,reachableState⟩ := GenericFunctionPoolSafety.invoke s count
  have returned : CallSafety.pastCallBoundary 1 finalState := by
    unfold CallSafety.pastCallBoundary CallSafety.frameDepth
    rw [empty]
    decide
  exact ⟨installed,finalState,call,trace,terminal,empty,
    SuccessfulTrace.no_errors _ 1 installed finalState safety.1 trace returned,safety,reachableState⟩
end
end DuplicatePrefix.DuplicatePrefixCallResult
