import empty_function.CanonicalDictionaries

/-! Pure compiler evidence at the actual canonical call hooks. The hypotheses
are compiler table queries only; no runtime action's success is assumed. -/
namespace EmptyFunction.MetadataQueries
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open CanonicalDictionaries
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem caller_location {p options config} (fields : Fields p options config)
    (limits : ExecutionMachine.Limits) (fn : CallInstance)
    (inline : CompilerVirtualFacts.inlineAttribute p.lifecycle.calls.scopes fn = .ok none ∨
      CompilerVirtualFacts.inlineAttribute p.lifecycle.calls.scopes fn = .ok (some false))
    (query : CompilerRuntimeQueries.requiresCallerLocation p.lifecycle.calls.runtime fn = .ok false) :
    (ExecutionMachine.callHooks config limits).requiresCallerLocation fn = pure false := by
  change config.virtual.compiler.requiresCallerLocation fn = _
  rw [fields.virtualCompiler]
  simp only [CompilerVirtualLeaves.make, CompilerVirtualFacts.scopeHooks]
  rcases inline with inline | inline
  all_goals
    simp only [inline, query]
    with_unfolding_all rfl

theorem instance_abi {p options config} (fields : Fields p options config)
    (limits : ExecutionMachine.Limits) (fn : CallInstance) (abi : FnAbi TyId)
    (query : CompilerInstanceAbi.abiOfInstance p.lifecycle.instances fn #[] = .ok abi) :
    (ExecutionMachine.callHooks config limits).fnAbiOfInstance () fn #[] = pure abi := by
  change config.calls.compiler.fnAbiOfInstance () fn #[] = _
  rw [fields.callsCompiler]
  simp only [CompilerExecutionCallLeaves.make, query]
  with_unfolding_all rfl

theorem target_features {p options config} (fields : Fields p options config)
    (limits : ExecutionMachine.Limits) (fn : CallInstance)
    (query : CompilerTargetFeatures.required p.intrinsics fn = .ok #[]) :
    (ExecutionMachine.callHooks config limits).checkTargetFeatures () fn = pure () := by
  change ExecutionCallLeaves.checkTargetFeatures config.calls.compiler.targetFeatures fn = _
  rw [fields.callsCompiler]
  simp only [CompilerExecutionCallLeaves.make, ExecutionCallLeaves.checkTargetFeatures,
    CompilerTargetFeatures.dictionary]
  simp only [query]
  with_unfolding_all rfl

theorem not_closure {p options config} (fields : Fields p options config)
    (limits : ExecutionMachine.Limits) (definition : DefId) (args : Array GenericArg) (abi : FnAbi TyId)
    (query : CompilerCallFacts.isClosureLike p.intrinsics ⟨.Item definition,args⟩ = .ok false) :
    (ExecutionMachine.callHooks config limits).nonCapturingClosure () ⟨.Item definition,args⟩ abi = pure false := by
  change ExecutionCallLeaves.nonCapturingClosure config.calls.compiler ⟨.Item definition,args⟩ abi = _
  rw [fields.callsCompiler]
  simp only [CompilerExecutionCallLeaves.make, ExecutionCallLeaves.nonCapturingClosure]
  simp only [query]
  with_unfolding_all rfl

end EmptyFunction.MetadataQueries

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.MetadataQueries." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata query axiom {dependency} in {name}"
