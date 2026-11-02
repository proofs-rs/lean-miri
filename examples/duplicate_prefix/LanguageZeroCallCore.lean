import duplicate_prefix.GuardFunctionConstant
import duplicate_prefix.CallItemDispatch
import duplicate_prefix.GenericCallStages

/-! The zero-argument runtime guard call's actual initStackFrame source prefix. -/
namespace DuplicatePrefix.LanguageZeroCallCore
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

abbrev Hooks := CallHooks Provenance CanonicalConfigFacts.RootState Unit MachineHooks.FrameExtra
  Unit ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)

noncomputable def require (condition : Bool) (message : String) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit :=
  unless condition do throw (.invalidProgram message)

noncomputable def spanAt (h : Hooks) (span : SpanRef) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let frame ← h.getFrame
  h.setFrame {frame with location := .unwinding span}

noncomputable def core (h : Hooks) (destination : RuntimeStackPlace Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let destinationOp ← h.placeToOp () destination
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  h.pushRaw () GuardCompilerFacts.languageCall.callee CopyPreconditions.Bodies.checkLanguage.loaded
    destination (.goto (some 1) .Continue)
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (_, calleeIndex) ← h.withRetagMode () .FnEntry (pure (0, 0))
  spanAt h (← h.localSpan CopyPreconditions.Bodies.checkLanguage.loaded.body 0)
  unless ← h.checkArgumentCompat () GuardCompilerFacts.languageAbi.ret GuardCompilerFacts.languageAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == GuardCompilerFacts.languageAbi.args.size)
    "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit ()
  h.pushDone ()

theorem actual_entry_eq (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (destination : RuntimeStackPlace Provenance) :
    Call.initStackFrame
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      GuardCompilerFacts.languageCall.callee CopyPreconditions.Bodies.checkLanguage.loaded
      GuardCompilerFacts.languageAbi #[] false destination (.goto (some 1) .Continue) =
      core (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
        destination := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  have requires : h.requiresCallerLocation GuardCompilerFacts.languageCall.callee = pure false := by
    funext state
    -- The checked rustc source caller-location query is used by the actual hook.
    change (PreparedContracts.actualConfig options () remaining span).virtual.compiler.requiresCallerLocation
      GuardCompilerFacts.languageCall.callee state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).virtualCompiler]
    with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime GuardCompilerFacts.languageCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
        MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
    rw [GuardCompilerFacts.language_caller_location]
  have abi : h.fnAbiOfInstance () GuardCompilerFacts.languageCall.callee #[] = pure GuardCompilerFacts.languageAbi := by
    funext state
    exact GuardCompilerFacts.actual_language_abi options () remaining span state
  have features : h.checkTargetFeatures () GuardCompilerFacts.languageCall.callee = pure () := by
    funext state
    change ExecutionCallLeaves.checkTargetFeatures
      (PreparedContracts.actualConfig options () remaining span).calls.compiler.targetFeatures
      GuardCompilerFacts.languageCall.callee state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
        options.compatibilityBudget).targetFeatures.required GuardCompilerFacts.languageCall.callee =
        (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser
          (Array ExecutionCallLeaves.TargetFeature)) := by
      with_unfolding_all change (match CompilerTargetFeatures.required
        PreparedReflection.actual.compiler.intrinsics GuardCompilerFacts.languageCall.callee with
        | .ok value => pure value
        | .error reason => throw (StepError.unsupported reason) :
          MachineHooks.M MiriMemoryKind Machine.RootUser
            (Array ExecutionCallLeaves.TargetFeature)) = _
      rw [GuardCompilerFacts.language_target_features]
    unfold ExecutionCallLeaves.checkTargetFeatures
    simp [query, bind, EStateM.bind, pure, EStateM.pure]
  have closure : h.nonCapturingClosure () GuardCompilerFacts.languageCall.callee GuardCompilerFacts.languageAbi = pure false := by
    funext state
    exact GuardCompilerFacts.actual_language_noncapturing options () remaining span limits state
  have variadic : h.abiVariadic GuardCompilerFacts.languageAbi = false := by
    change GuardCompilerFacts.languageAbi.cVariadic = false
    decide +kernel
  have calleeVariadic : h.abiVariadic GuardCompilerFacts.languageAbi = false := by
    change GuardCompilerFacts.languageAbi.cVariadic = false
    decide +kernel
  have canUnwind : h.abiCanUnwind GuardCompilerFacts.languageAbi = true := by
    change GuardCompilerFacts.languageAbi.canUnwind = true
    decide +kernel
  have conv : h.sameConvention GuardCompilerFacts.languageAbi GuardCompilerFacts.languageAbi = true := by
    change (GuardCompilerFacts.languageAbi.conv == GuardCompilerFacts.languageAbi.conv) = true
    decide +kernel
  have args : h.abiArgs GuardCompilerFacts.languageAbi = GuardCompilerFacts.languageAbi.args := rfl
  have calleeArgs : h.abiArgs GuardCompilerFacts.languageAbi = GuardCompilerFacts.languageAbi.args := rfl
  have callerArgsEmpty : GuardCompilerFacts.languageAbi.args.size = 0 := by decide +kernel
  have calleeArgsEmpty : GuardCompilerFacts.languageAbi.args.size = 0 := by decide +kernel
  have ret : h.abiReturn GuardCompilerFacts.languageAbi = GuardCompilerFacts.languageAbi.ret := rfl
  have calleeRet : h.abiReturn GuardCompilerFacts.languageAbi = GuardCompilerFacts.languageAbi.ret := rfl
  change Call.initStackFrame h () _ _ _ _ _ _ _ = core h destination
  generalize hDef : h = hooks at *
  unfold Call.initStackFrame core
  unfold_call_require
  unfold_internal ".Call.at?"
  unfold_internal ".Call.setSpan"
  simp [requires, abi, features, closure, variadic, calleeVariadic, canUnwind, conv, args,
    calleeArgs, callerArgsEmpty, calleeArgsEmpty, ret, calleeRet,
    GuardCompilerFacts.source_body_shapes.1,
    List.range'_succ, List.forIn_cons, List.forIn_nil, bind_assoc, spanAt, require]
  congr 1
  funext destinationOp
  cases destinationOp with
  | mk operand layout => cases operand <;> rfl

end DuplicatePrefix.LanguageZeroCallCore

#print axioms DuplicatePrefix.LanguageZeroCallCore.actual_entry_eq
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LanguageZeroCallCore.actual_entry_eq) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved language zero core dependency {dependency}"
