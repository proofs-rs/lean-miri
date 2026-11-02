import duplicate_prefix.GuardCompilerFacts
import duplicate_prefix.AsMutPtrFacts
import duplicate_prefix.ActualReferenceMetadata
namespace DuplicatePrefix.AsMutCallFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem as_mut_ptr_caller_location : CompilerRuntimeQueries.requiresCallerLocation
    PreparedReflection.actual.compiler.lifecycle.calls.runtime HelperCompilerFacts.asMutPtrCall.callee = .ok false := by with_unfolding_all rfl

theorem as_mut_ptr_target_features : CompilerTargetFeatures.required
    PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.asMutPtrCall.callee = .ok #[] := by with_unfolding_all rfl

theorem as_mut_ptr_not_closure : CompilerCallFacts.isClosureLike
    PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.asMutPtrCall.callee = .ok false := by with_unfolding_all rfl

theorem actual_as_mut_ptr_caller_location (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).requiresCallerLocation
      HelperCompilerFacts.asMutPtrCall.callee state = .ok false state := by
  change (PreparedContracts.actualConfig options choice remaining span).virtual.compiler.requiresCallerLocation
    HelperCompilerFacts.asMutPtrCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).virtualCompiler]
  with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime HelperCompilerFacts.asMutPtrCall.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
      MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
  rw [as_mut_ptr_caller_location]
  rfl


theorem actual_as_mut_ptr_target_features (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).checkTargetFeatures
      choice HelperCompilerFacts.asMutPtrCall.callee state = .ok () state := by
  change ExecutionCallLeaves.checkTargetFeatures
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.targetFeatures HelperCompilerFacts.asMutPtrCall.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).targetFeatures.required HelperCompilerFacts.asMutPtrCall.callee =
      (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) := by
    with_unfolding_all change (match CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
        HelperCompilerFacts.asMutPtrCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) = _
    rw [as_mut_ptr_target_features]
  unfold ExecutionCallLeaves.checkTargetFeatures
  rw [query]
  rfl


theorem actual_as_mut_ptr_noncapturing (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).nonCapturingClosure
      choice HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrAbi state = .ok false state := by
  change ExecutionCallLeaves.nonCapturingClosure (PreparedContracts.actualConfig options choice remaining span).calls.compiler
    HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrAbi state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).isClosureLike HelperCompilerFacts.asMutPtrCall.callee =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    with_unfolding_all change (match CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics HelperCompilerFacts.asMutPtrCall.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [as_mut_ptr_not_closure]
  unfold ExecutionCallLeaves.nonCapturingClosure
  rw [query]
  rfl


theorem actual_as_mut_ptr_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.fnAbiOfInstance
      choice HelperCompilerFacts.asMutPtrCall.callee #[] state = .ok HelperCompilerFacts.asMutPtrAbi state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  with_unfolding_all change (match (HelperCompilerFacts.abiQuery HelperCompilerFacts.asMutPtrCall.callee) with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) state = _
  rw [HelperCompilerFacts.as_mut_ptr_abi_eq]
  rfl

theorem actual_as_mut_ptr_load (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).helpers.loadMir choice HelperCompilerFacts.asMutPtrCall.callee state =
      .ok HelperCompilerFacts.asMutPtrBody state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).loadMir]
  with_unfolding_all change (match (HelperCompilerFacts.bodyQuery HelperCompilerFacts.asMutPtrCall.callee) with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler call pipeline: {reason}") : MachineHooks.M MiriMemoryKind Machine.RootUser LoadedBody) state = _
  rw [HelperCompilerFacts.as_mut_ptr_body_eq]
  rfl

theorem abi_flags : HelperCompilerFacts.asMutPtrAbi.cVariadic = false ∧ HelperCompilerFacts.asMutPtrAbi.canUnwind = true ∧
    HelperCompilerFacts.asMutPtrAbi.args.size = 1 := by decide +kernel

theorem body_flags : HelperCompilerFacts.asMutPtrBody.body.argumentCount = 1 ∧
    HelperCompilerFacts.asMutPtrBody.body.spreadArgument = none := by with_unfolding_all exact ⟨rfl,rfl⟩

theorem abi_layouts : HelperCompilerFacts.asMutPtrAbi.ret.layout = CopyCompilerFacts.destPointerLayout ∧
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret).layout = ActualReferenceMetadata.reference := by
  constructor <;> with_unfolding_all rfl

end
end DuplicatePrefix.AsMutCallFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.AsMutCallFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
