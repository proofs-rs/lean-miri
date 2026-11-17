import duplicate_prefix.AddFunctionFacts
namespace DuplicatePrefix.AddCalleeLeaves
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem instance_kind (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).instanceKind
      HelperCompilerFacts.addCall.callee = (pure (.Item 8) : MachineHooks.M MiriMemoryKind Machine.RootUser CallInstanceKind) := by
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.instanceKind _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  dsimp only [CompilerCallConstruction.compiler, CompilerExecutionCallLeaves.make]
  unfold_internal ".CompilerExecutionCallLeaves.lift"
  with_unfolding_all rfl

theorem signature (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).functionSignature ()
      AddFunctionFacts.functionLayout =
      (pure (2,.Rust) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × ABI.ExternAbi)) := by
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.functionSignature () _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  dsimp only [CompilerCallConstruction.compiler, CompilerExecutionCallLeaves.make]
  rw [AddFunctionFacts.functionLayout_shape.1, AddFunctionFacts.function_signature_query]
  rfl

theorem kind (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).functionKind AddFunctionFacts.functionLayout.ty =
      (pure (.FnDef (PreparedReflection.fixedInstance HelperCompilerFacts.addCall.callee).instanceKind.defId (PreparedReflection.fixedInstance HelperCompilerFacts.addCall.callee).genericArgs) : MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) := by
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.functionKind _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  with_unfolding_all change (match CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions AddFunctionFacts.functionLayout.ty with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) = _
  rw [AddFunctionFacts.functionLayout_shape.1,AddFunctionFacts.function_kind]
end
end DuplicatePrefix.AddCalleeLeaves
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AddCalleeLeaves.signature, ``DuplicatePrefix.AddCalleeLeaves.kind] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata callee leaves dependency {dependency}"
