import duplicate_prefix.RuntimeFunctionConstant
import duplicate_prefix.CallItemDispatch
import duplicate_prefix.GenericCallStages

/-! The zero-argument runtime guard call's actual initStackFrame source prefix. -/
namespace DuplicatePrefix.RuntimeZeroCallCore
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
  h.pushRaw () GuardCompilerFacts.runtimeCall.callee CopyPreconditions.Bodies.languageRuntime.loaded
    destination (.goto (some 1) .Continue)
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (_, calleeIndex) ← h.withRetagMode () .FnEntry (pure (0, 0))
  spanAt h (← h.localSpan CopyPreconditions.Bodies.languageRuntime.loaded.body 0)
  unless ← h.checkArgumentCompat () GuardCompilerFacts.languageAbi.ret GuardCompilerFacts.runtimeAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == GuardCompilerFacts.runtimeAbi.args.size)
    "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit ()
  h.pushDone ()

theorem actual_entry_eq (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (destination : RuntimeStackPlace Provenance) :
    Call.initStackFrame
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      GuardCompilerFacts.runtimeCall.callee CopyPreconditions.Bodies.languageRuntime.loaded
      GuardCompilerFacts.languageAbi #[] false destination (.goto (some 1) .Continue) =
      core (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
        destination := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  have requires : h.requiresCallerLocation GuardCompilerFacts.runtimeCall.callee = pure false := by
    funext state
    -- The checked rustc source caller-location query is used by the actual hook.
    change (PreparedContracts.actualConfig options () remaining span).virtual.compiler.requiresCallerLocation
      GuardCompilerFacts.runtimeCall.callee state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).virtualCompiler]
    with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime GuardCompilerFacts.runtimeCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
        MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
    rw [GuardCompilerFacts.runtime_caller_location]
  have abi : h.fnAbiOfInstance () GuardCompilerFacts.runtimeCall.callee #[] =
      pure GuardCompilerFacts.runtimeAbi := by
    funext state
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.fnAbiOfInstance
      () GuardCompilerFacts.runtimeCall.callee #[] state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    with_unfolding_all change (match CompilerInstanceAbi.abiOfInstance
      PreparedReflection.actual.compiler.lifecycle.instances GuardCompilerFacts.runtimeCall.callee #[] with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi TyId)) state = _
    rw [RuntimeCallQueries.function_abi]
  have features : h.checkTargetFeatures () GuardCompilerFacts.runtimeCall.callee = pure () := by
    funext state
    change ExecutionCallLeaves.checkTargetFeatures
      (PreparedContracts.actualConfig options () remaining span).calls.compiler.targetFeatures
      GuardCompilerFacts.runtimeCall.callee state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
        options.compatibilityBudget).targetFeatures.required GuardCompilerFacts.runtimeCall.callee =
        (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser
          (Array ExecutionCallLeaves.TargetFeature)) := by
      with_unfolding_all change (match CompilerTargetFeatures.required
        PreparedReflection.actual.compiler.intrinsics GuardCompilerFacts.runtimeCall.callee with
        | .ok value => pure value
        | .error reason => throw (StepError.unsupported reason) :
          MachineHooks.M MiriMemoryKind Machine.RootUser
            (Array ExecutionCallLeaves.TargetFeature)) = _
      rw [GuardCompilerFacts.runtime_target_features]
    unfold ExecutionCallLeaves.checkTargetFeatures
    simp [query, bind, EStateM.bind, pure, EStateM.pure]
  have closure : h.nonCapturingClosure () GuardCompilerFacts.runtimeCall.callee GuardCompilerFacts.runtimeAbi = pure false := by
    funext state
    exact GuardCompilerFacts.actual_runtime_noncapturing options () remaining span limits state
  have variadic : h.abiVariadic GuardCompilerFacts.languageAbi = false := by
    change GuardCompilerFacts.languageAbi.cVariadic = false
    decide +kernel
  have calleeVariadic : h.abiVariadic GuardCompilerFacts.runtimeAbi = false := by
    change GuardCompilerFacts.runtimeAbi.cVariadic = false
    decide +kernel
  have canUnwind : h.abiCanUnwind GuardCompilerFacts.runtimeAbi = true := by
    change GuardCompilerFacts.runtimeAbi.canUnwind = true
    decide +kernel
  have conv : h.sameConvention GuardCompilerFacts.languageAbi GuardCompilerFacts.runtimeAbi = true := by
    change (GuardCompilerFacts.languageAbi.conv == GuardCompilerFacts.runtimeAbi.conv) = true
    decide +kernel
  have args : h.abiArgs GuardCompilerFacts.languageAbi = GuardCompilerFacts.languageAbi.args := rfl
  have calleeArgs : h.abiArgs GuardCompilerFacts.runtimeAbi = GuardCompilerFacts.runtimeAbi.args := rfl
  have callerArgsEmpty : GuardCompilerFacts.languageAbi.args.size = 0 := by decide +kernel
  have calleeArgsEmpty : GuardCompilerFacts.runtimeAbi.args.size = 0 := by decide +kernel
  have ret : h.abiReturn GuardCompilerFacts.languageAbi = GuardCompilerFacts.languageAbi.ret := rfl
  have calleeRet : h.abiReturn GuardCompilerFacts.runtimeAbi = GuardCompilerFacts.runtimeAbi.ret := rfl
  change Call.initStackFrame h () _ _ _ _ _ _ _ = core h destination
  generalize hDef : h = hooks at *
  unfold Call.initStackFrame core
  unfold_call_require
  unfold_internal ".Call.at?"
  unfold_internal ".Call.setSpan"
  simp [requires, abi, features, closure, variadic, calleeVariadic, canUnwind, conv, args,
    calleeArgs, callerArgsEmpty, calleeArgsEmpty, ret, calleeRet,
    GuardCompilerFacts.source_body_shapes.2.2.1,
    List.range'_succ, List.forIn_cons, List.forIn_nil, bind_assoc, spanAt, require]
  congr 1
  funext destinationOp
  cases destinationOp with
  | mk operand layout => cases operand <;> rfl

end DuplicatePrefix.RuntimeZeroCallCore

#print axioms DuplicatePrefix.RuntimeZeroCallCore.actual_entry_eq
