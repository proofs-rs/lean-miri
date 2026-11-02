import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.GuardCompilerFacts
namespace DuplicatePrefix.AddCallFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem add_caller_location : CompilerRuntimeQueries.requiresCallerLocation
    PreparedReflection.actual.compiler.lifecycle.calls.runtime HelperCompilerFacts.addCall.callee = .ok true := by with_unfolding_all rfl

theorem add_target_features : CompilerTargetFeatures.required
    PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.addCall.callee = .ok #[] := by with_unfolding_all rfl

theorem add_not_closure : CompilerCallFacts.isClosureLike
    PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.addCall.callee = .ok false := by with_unfolding_all rfl

theorem actual_add_caller_location (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).requiresCallerLocation
      HelperCompilerFacts.addCall.callee state = .ok true state := by
  change (PreparedContracts.actualConfig options choice remaining span).virtual.compiler.requiresCallerLocation
    HelperCompilerFacts.addCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).virtualCompiler]
  with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime HelperCompilerFacts.addCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
      MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
  rw [add_caller_location]
  rfl


theorem actual_add_target_features (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).checkTargetFeatures
      choice HelperCompilerFacts.addCall.callee state = .ok () state := by
  change ExecutionCallLeaves.checkTargetFeatures
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.targetFeatures HelperCompilerFacts.addCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).targetFeatures.required HelperCompilerFacts.addCall.callee =
      (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) := by
    with_unfolding_all change (match CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
        HelperCompilerFacts.addCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) = _
    rw [add_target_features]
  unfold ExecutionCallLeaves.checkTargetFeatures
  rw [query]
  rfl


theorem actual_add_noncapturing (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).nonCapturingClosure
      choice HelperCompilerFacts.addCall.callee HelperCompilerFacts.addAbi state = .ok false state := by
  change ExecutionCallLeaves.nonCapturingClosure (PreparedContracts.actualConfig options choice remaining span).calls.compiler
    HelperCompilerFacts.addCall.callee HelperCompilerFacts.addAbi state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).isClosureLike HelperCompilerFacts.addCall.callee =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    with_unfolding_all change (match CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.addCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [add_not_closure]
  unfold ExecutionCallLeaves.nonCapturingClosure
  rw [query]
  rfl


theorem actual_add_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.fnAbiOfInstance
      choice HelperCompilerFacts.addCall.callee #[] state = .ok HelperCompilerFacts.addAbi state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  with_unfolding_all change (match (HelperCompilerFacts.abiQuery HelperCompilerFacts.addCall.callee) with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) state = _
  rw [HelperCompilerFacts.add_abi_eq]
  rfl

theorem actual_add_load (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).helpers.loadMir choice HelperCompilerFacts.addCall.callee state =
      .ok HelperCompilerFacts.addBody state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).loadMir]
  with_unfolding_all change (match (HelperCompilerFacts.bodyQuery HelperCompilerFacts.addCall.callee) with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler call pipeline: {reason}") : MachineHooks.M MiriMemoryKind Machine.RootUser LoadedBody) state = _
  rw [HelperCompilerFacts.add_body_eq]
  rfl

theorem abi_flags : HelperCompilerFacts.addAbi.cVariadic = false ∧ HelperCompilerFacts.addAbi.canUnwind = true ∧
    HelperCompilerFacts.addAbi.args.size = 3 := by decide +kernel

theorem body_flags : HelperCompilerFacts.addBody.body.argumentCount = 2 ∧
    HelperCompilerFacts.addBody.body.spreadArgument = none := by with_unfolding_all exact ⟨rfl,rfl⟩


end
end DuplicatePrefix.AddCallFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.AddCallFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
