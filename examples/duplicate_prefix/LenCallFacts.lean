import duplicate_prefix.GuardCompilerFacts
import duplicate_prefix.LenHelper
namespace DuplicatePrefix.LenCallFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem len_caller_location : CompilerRuntimeQueries.requiresCallerLocation
    PreparedReflection.actual.compiler.lifecycle.calls.runtime LenHelper.resolved.callee = .ok false := by with_unfolding_all rfl

theorem len_target_features : CompilerTargetFeatures.required
    PreparedReflection.actual.compiler.intrinsics LenHelper.resolved.callee = .ok #[] := by with_unfolding_all rfl

theorem len_not_closure : CompilerCallFacts.isClosureLike
    PreparedReflection.actual.compiler.intrinsics LenHelper.resolved.callee = .ok false := by with_unfolding_all rfl

theorem actual_len_caller_location (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).requiresCallerLocation
      LenHelper.resolved.callee state = .ok false state := by
  change (PreparedContracts.actualConfig options choice remaining span).virtual.compiler.requiresCallerLocation
    LenHelper.resolved.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).virtualCompiler]
  with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime LenHelper.resolved.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
      MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
  rw [len_caller_location]
  rfl


theorem actual_len_target_features (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).checkTargetFeatures
      choice LenHelper.resolved.callee state = .ok () state := by
  change ExecutionCallLeaves.checkTargetFeatures
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.targetFeatures LenHelper.resolved.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).targetFeatures.required LenHelper.resolved.callee =
      (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) := by
    with_unfolding_all change (match CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
        LenHelper.resolved.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) = _
    rw [len_target_features]
  unfold ExecutionCallLeaves.checkTargetFeatures
  rw [query]
  rfl


theorem actual_len_noncapturing (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).nonCapturingClosure
      choice LenHelper.resolved.callee LenHelper.abi state = .ok false state := by
  change ExecutionCallLeaves.nonCapturingClosure (PreparedContracts.actualConfig options choice remaining span).calls.compiler
    LenHelper.resolved.callee LenHelper.abi state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).isClosureLike LenHelper.resolved.callee =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    with_unfolding_all change (match CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics LenHelper.resolved.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [len_not_closure]
  unfold ExecutionCallLeaves.nonCapturingClosure
  rw [query]
  rfl


theorem actual_len_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.fnAbiOfInstance
      choice LenHelper.resolved.callee #[] state = .ok LenHelper.abi state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  with_unfolding_all change (match LenHelper.abiQuery with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) state = _
  rw [LenHelper.abi_eq]
  rfl

theorem actual_len_load (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).helpers.loadMir choice LenHelper.resolved.callee state =
      .ok LenHelper.body state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).loadMir]
  with_unfolding_all change (match LenHelper.bodyQuery with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler call pipeline: {reason}") : MachineHooks.M MiriMemoryKind Machine.RootUser LoadedBody) state = _
  rw [LenHelper.body_eq]
  rfl

theorem abi_flags : LenHelper.abi.cVariadic = false ∧ LenHelper.abi.canUnwind = true ∧
    LenHelper.abi.args.size = 1 := by decide +kernel

theorem body_flags : LenHelper.body.body.argumentCount = 1 ∧
    LenHelper.body.body.spreadArgument = none := by with_unfolding_all exact ⟨rfl,rfl⟩

theorem abi_layouts : LenHelper.abi.ret.layout = RootCompilerFacts.usizeLayout ∧
    (LenHelper.abi.args.getD 0 LenHelper.abi.ret).layout = LenHelper.rawLayout := by
  constructor <;> with_unfolding_all rfl

end
end DuplicatePrefix.LenCallFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.LenCallFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
