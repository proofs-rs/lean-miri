import duplicate_prefix.MetadataCallQueries
namespace DuplicatePrefix.MetadataCalleeLeaves
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem instance_kind (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).instanceKind
      PtrMetadataHelper.resolved.callee = (pure (.Item 13) : MachineHooks.M MiriMemoryKind Machine.RootUser CallInstanceKind) := by
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.instanceKind _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  dsimp only [CompilerCallConstruction.compiler, CompilerExecutionCallLeaves.make]
  unfold_internal ".CompilerExecutionCallLeaves.lift"
  with_unfolding_all rfl

theorem signature (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).functionSignature ()
      MetadataCallQueries.functionLayout =
      (pure (1,.Rust) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × ABI.ExternAbi)) := by
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.functionSignature () _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  dsimp only [CompilerCallConstruction.compiler, CompilerExecutionCallLeaves.make]
  rw [MetadataCallQueries.functionLayout_shape.1, MetadataCallQueries.function_signature_query]
  rfl

theorem kind (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).functionKind MetadataCallQueries.functionLayout.ty =
      (pure (.FnDef 13 (PreparedReflection.fixedInstance PtrMetadataHelper.resolved.callee).genericArgs) : MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) := by
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.functionKind _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  with_unfolding_all change (match CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions MetadataCallQueries.functionLayout.ty with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) = _
  rw [MetadataCallQueries.functionLayout_shape.1,MetadataCallQueries.function_kind]
  with_unfolding_all rfl
end
end DuplicatePrefix.MetadataCalleeLeaves
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.MetadataCalleeLeaves.signature, ``DuplicatePrefix.MetadataCalleeLeaves.kind] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata callee leaves dependency {dependency}"
