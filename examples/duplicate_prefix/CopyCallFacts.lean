import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.GuardCompilerFacts
namespace DuplicatePrefix.CopyCallFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem copy_caller_location : CompilerRuntimeQueries.requiresCallerLocation
    PreparedReflection.actual.compiler.lifecycle.calls.runtime HelperCompilerFacts.copyCall.callee = .ok true := by with_unfolding_all rfl

theorem copy_target_features : CompilerTargetFeatures.required
    PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.copyCall.callee = .ok #[] := by with_unfolding_all rfl

theorem copy_not_closure : CompilerCallFacts.isClosureLike
    PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.copyCall.callee = .ok false := by with_unfolding_all rfl

theorem actual_copy_caller_location (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).requiresCallerLocation
      HelperCompilerFacts.copyCall.callee state = .ok true state := by
  change (PreparedContracts.actualConfig options choice remaining span).virtual.compiler.requiresCallerLocation
    HelperCompilerFacts.copyCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).virtualCompiler]
  with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime HelperCompilerFacts.copyCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
      MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
  rw [copy_caller_location]
  rfl


theorem actual_copy_target_features (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).checkTargetFeatures
      choice HelperCompilerFacts.copyCall.callee state = .ok () state := by
  change ExecutionCallLeaves.checkTargetFeatures
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.targetFeatures HelperCompilerFacts.copyCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).targetFeatures.required HelperCompilerFacts.copyCall.callee =
      (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) := by
    with_unfolding_all change (match CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
        HelperCompilerFacts.copyCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) = _
    rw [copy_target_features]
  unfold ExecutionCallLeaves.checkTargetFeatures
  rw [query]
  rfl


theorem actual_copy_noncapturing (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).nonCapturingClosure
      choice HelperCompilerFacts.copyCall.callee HelperCompilerFacts.copyAbi state = .ok false state := by
  change ExecutionCallLeaves.nonCapturingClosure (PreparedContracts.actualConfig options choice remaining span).calls.compiler
    HelperCompilerFacts.copyCall.callee HelperCompilerFacts.copyAbi state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).isClosureLike HelperCompilerFacts.copyCall.callee =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    with_unfolding_all change (match CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.copyCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [copy_not_closure]
  unfold ExecutionCallLeaves.nonCapturingClosure
  rw [query]
  rfl


theorem actual_copy_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.fnAbiOfInstance
      choice HelperCompilerFacts.copyCall.callee #[] state = .ok HelperCompilerFacts.copyAbi state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  with_unfolding_all change (match (HelperCompilerFacts.abiQuery HelperCompilerFacts.copyCall.callee) with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) state = _
  rw [HelperCompilerFacts.copy_abi_eq]
  rfl

theorem actual_copy_load (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).helpers.loadMir choice HelperCompilerFacts.copyCall.callee state =
      .ok HelperCompilerFacts.copyBody state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).loadMir]
  with_unfolding_all change (match (HelperCompilerFacts.bodyQuery HelperCompilerFacts.copyCall.callee) with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler call pipeline: {reason}") : MachineHooks.M MiriMemoryKind Machine.RootUser LoadedBody) state = _
  rw [HelperCompilerFacts.copy_body_eq]
  rfl

theorem abi_flags : HelperCompilerFacts.copyAbi.cVariadic = false ∧ HelperCompilerFacts.copyAbi.canUnwind = true ∧
    HelperCompilerFacts.copyAbi.args.size = 4 := by decide +kernel

theorem body_flags : HelperCompilerFacts.copyBody.body.argumentCount = 3 ∧
    HelperCompilerFacts.copyBody.body.spreadArgument = none := by with_unfolding_all exact ⟨rfl,rfl⟩


end
end DuplicatePrefix.CopyCallFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CopyCallFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
