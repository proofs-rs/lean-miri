import duplicate_prefix.CopyFunctionFacts
namespace DuplicatePrefix.CopyCalleeLeaves
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem signature (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).functionSignature ()
      CopyFunctionFacts.functionLayout =
      (pure (3,.Rust) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × ABI.ExternAbi)) := by
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.functionSignature () _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  simp only [CompilerCallConstruction.compiler,CompilerExecutionCallLeaves.make]
  rw [CopyFunctionFacts.functionLayout_shape.1,CopyFunctionFacts.function_signature_query]
  simp only [bind,Except.bind,pure,Except.pure]
  rw [CopyFunctionFacts.decode_rust_extern_abi cmp]
  with_unfolding_all rfl

theorem kind (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).functionKind CopyFunctionFacts.functionLayout.ty =
      (pure (.FnDef HelperCompilerFacts.copyCall.callee.defId HelperCompilerFacts.copyCall.callee.args) : MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) := by
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.functionKind _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  with_unfolding_all change (match CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions CopyFunctionFacts.functionLayout.ty with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) = _
  rw [CopyFunctionFacts.functionLayout_shape.1,CopyFunctionFacts.function_kind]
end
end DuplicatePrefix.CopyCalleeLeaves
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.CopyCalleeLeaves.signature, ``DuplicatePrefix.CopyCalleeLeaves.kind] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata callee leaves dependency {dependency}"
