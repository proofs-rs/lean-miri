import empty_function.CanonicalDictionaries

/-! Compiler evidence at the actual canonical call hooks. Live ABI and
instance queries read the selected World in the supplied state. ABI derivation
and cache attachment expose their resulting World rather than claiming a
state-independent success from an unrelated prepared table. -/
namespace EmptyFunction.MetadataQueries
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open CanonicalDictionaries
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem caller_location {p options config} (fields : Fields p options config)
    (limits : ExecutionMachine.Limits) (fn : CallInstance)
    (inline : CompilerVirtualFacts.inlineAttribute p.lifecycle.calls.scopes fn = none ∨
      CompilerVirtualFacts.inlineAttribute p.lifecycle.calls.scopes fn = (some false))
    (query : CompilerRuntimeQueries.requiresCallerLocation p.lifecycle.calls.runtime fn = .ok false) :
    (ExecutionMachine.callHooks config limits).requiresCallerLocation fn = pure false := by
  change config.virtual.compiler.requiresCallerLocation fn = _
  rw [fields.virtualCompiler]
  simp only [CompilerVirtualLeaves.make, CompilerVirtualFacts.scopeHooks]
  rcases inline with inline | inline
  all_goals
    simp only [inline, query] <;> with_unfolding_all rfl

/-- A cache hit is justified by the current World's exact key and ABI data.
The lookup reads that World and leaves the actual machine state unchanged. -/
theorem instance_abi {p options config} (fields : Fields p options config)
    (limits : ExecutionMachine.Limits) (fn : CallInstance) (abi : FnAbi TyId)
    (before : MachineHooks.State MiriMemoryKind Configuration.RootUser)
    (world : SourceCompilerWorld.World) (abiId : Nat)
    (present : EvalCoreMachine.sourceCompilerAccess.get before = some world)
    (cached : SourceCompilerWorld.existingInstanceAbi world fn #[] = .ok (some abiId))
    (query : SourceCompilerWorld.instanceAbi world fn #[] = .ok abi) :
    (ExecutionMachine.callHooks config limits).fnAbiOfInstance () fn #[] before = .ok abi before := by
  change config.calls.compiler.fnAbiOfInstance () fn #[] before = _
  rw [fields.callsCompiler]
  simp only [CompilerExecutionCallLeaves.make]
  with_unfolding_all
    simp [SourceCompilerWorld.demandInstanceAbi, present, cached, query,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
    rfl

/-- On a miss, source derivation and checked cache attachment extend the same
World. The theorem retains the real `put` result, including all new canonical
pools and the derived ABI memo; it does not replace the demand by `pure abi`. -/
theorem instance_abi_derived {p options config} (fields : Fields p options config)
    (limits : ExecutionMachine.Limits) (fn : CallInstance) (abi : FnAbi TyId)
    (before : MachineHooks.State MiriMemoryKind Configuration.RootUser)
    (world derived installed : SourceCompilerWorld.World) (raw : Input.FunctionAbi) (abiId : Nat)
    (present : EvalCoreMachine.sourceCompilerAccess.get before = some world)
    (missing : SourceCompilerWorld.existingInstanceAbi world fn #[] = .ok none)
    (derive : SourceAbi.derive world fn #[] = .ok (derived,raw))
    (attach : SourceCompilerWorld.attachInstanceAbi derived fn #[] raw = .ok (installed,abiId))
    (query : SourceCompilerWorld.instanceAbi installed fn #[] = .ok abi) :
    (ExecutionMachine.callHooks config limits).fnAbiOfInstance () fn #[] before =
      .ok abi (EvalCoreMachine.sourceCompilerAccess.put before installed) := by
  change config.calls.compiler.fnAbiOfInstance () fn #[] before = _
  rw [fields.callsCompiler]
  simp only [CompilerExecutionCallLeaves.make]
  with_unfolding_all
    simp [SourceCompilerWorld.demandInstanceAbi, present, missing, derive, attach, query,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, set, MonadStateOf.set, EStateM.set,
      pure, EStateM.pure]
    dsimp!
    simp [attach,query,bind,Bind.bind,EStateM.bind,set,getThe,MonadStateOf.set,EStateM.set,pure,Pure.pure,EStateM.pure]
    dsimp!
    simp [query,pure,Pure.pure,EStateM.pure,bind,Bind.bind,EStateM.bind]
    rfl

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
    (limits : ExecutionMachine.Limits) (fn : CallInstance) (definition : DefId) (abi : FnAbi TyId)
    (before : MachineHooks.State MiriMemoryKind Configuration.RootUser)
    (world : SourceCompilerWorld.World) (node : Input.InstanceNode)
    (present : EvalCoreMachine.sourceCompilerAccess.get before = some world)
    (lookup : SourceCompilerWorld.node world fn = .ok node)
    (kind : node.instanceKind = .Item definition)
    (query : CompilerCallFacts.isClosureLike p.intrinsics fn = .ok false) :
    (ExecutionMachine.callHooks config limits).nonCapturingClosure () fn abi before = .ok false before := by
  have currentKind : SourceCompilerInstances.instanceKind EvalCoreMachine.sourceCompilerAccess fn before =
      .ok (.Item definition) before := by
    rw [SourceCompilerInstances.instanceKind_at]
    simp [present,lookup,kind]
  change ExecutionCallLeaves.nonCapturingClosure config.calls.compiler fn abi before = _
  rw [fields.callsCompiler]
  simp only [CompilerExecutionCallLeaves.make, ExecutionCallLeaves.nonCapturingClosure]
  with_unfolding_all
    simp [currentKind, query, bind, EStateM.bind, pure, EStateM.pure]
    rfl

end EmptyFunction.MetadataQueries

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.MetadataQueries." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata query axiom {dependency} in {name}"
