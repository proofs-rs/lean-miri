import duplicate_prefix.GuardCompilerFacts
import duplicate_prefix.PtrMetadataHelper
namespace DuplicatePrefix.MetadataCallFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem metadata_caller_location : CompilerRuntimeQueries.requiresCallerLocation
    PreparedReflection.actual.compiler.lifecycle.calls.runtime PtrMetadataHelper.resolved.callee = .ok false := by with_unfolding_all rfl

theorem metadata_target_features : CompilerTargetFeatures.required
    PreparedReflection.actual.compiler.intrinsics PtrMetadataHelper.resolved.callee = .ok #[] := by with_unfolding_all rfl

theorem metadata_not_closure : CompilerCallFacts.isClosureLike
    PreparedReflection.actual.compiler.intrinsics PtrMetadataHelper.resolved.callee = .ok false := by with_unfolding_all rfl

theorem actual_metadata_caller_location (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).requiresCallerLocation
      PtrMetadataHelper.resolved.callee state = .ok false state := by
  change (PreparedContracts.actualConfig options choice remaining span).virtual.compiler.requiresCallerLocation
    PtrMetadataHelper.resolved.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).virtualCompiler]
  with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime PtrMetadataHelper.resolved.callee with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
      MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
  rw [metadata_caller_location]
  rfl


theorem actual_metadata_target_features (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).checkTargetFeatures
      choice PtrMetadataHelper.resolved.callee state = .ok () state := by
  change ExecutionCallLeaves.checkTargetFeatures
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.targetFeatures PtrMetadataHelper.resolved.callee state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).targetFeatures.required PtrMetadataHelper.resolved.callee =
      (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) := by
    with_unfolding_all change (match CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
        PtrMetadataHelper.resolved.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) = _
    rw [metadata_target_features]
  unfold ExecutionCallLeaves.checkTargetFeatures
  rw [query]
  rfl


theorem actual_metadata_noncapturing (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options choice remaining span) limits).nonCapturingClosure
      choice PtrMetadataHelper.resolved.callee PtrMetadataHelper.abi state = .ok false state := by
  change ExecutionCallLeaves.nonCapturingClosure (PreparedContracts.actualConfig options choice remaining span).calls.compiler
    PtrMetadataHelper.resolved.callee PtrMetadataHelper.abi state = _
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).isClosureLike PtrMetadataHelper.resolved.callee =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    with_unfolding_all change (match CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics PtrMetadataHelper.resolved.callee with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [metadata_not_closure]
  unfold ExecutionCallLeaves.nonCapturingClosure
  rw [query]
  rfl


theorem actual_metadata_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).calls.compiler.fnAbiOfInstance
      choice PtrMetadataHelper.resolved.callee #[] state = .ok PtrMetadataHelper.abi state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  with_unfolding_all change (match PtrMetadataHelper.abiQuery with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) state = _
  rw [PtrMetadataHelper.abi_eq]
  rfl

theorem actual_metadata_load (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options choice remaining span).helpers.loadMir choice PtrMetadataHelper.resolved.callee state =
      .ok PtrMetadataHelper.body state := by
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).loadMir]
  with_unfolding_all change (match PtrMetadataHelper.bodyQuery with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler call pipeline: {reason}") : MachineHooks.M MiriMemoryKind Machine.RootUser LoadedBody) state = _
  rw [PtrMetadataHelper.body_eq]
  rfl

theorem abi_flags : PtrMetadataHelper.abi.cVariadic = false ∧ PtrMetadataHelper.abi.canUnwind = true ∧
    PtrMetadataHelper.abi.args.size = 1 := by decide +kernel

theorem body_flags : PtrMetadataHelper.body.body.argumentCount = 1 ∧
    PtrMetadataHelper.body.body.spreadArgument = none := by with_unfolding_all exact ⟨rfl,rfl⟩

theorem abi_layouts : PtrMetadataHelper.abi.ret.layout = RootCompilerFacts.usizeLayout ∧
    (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret).layout = PtrMetadataHelper.rawLayout := by
  constructor <;> with_unfolding_all rfl

end
end DuplicatePrefix.MetadataCallFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.MetadataCallFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
