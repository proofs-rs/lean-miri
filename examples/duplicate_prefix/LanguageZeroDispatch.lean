import duplicate_prefix.LanguageZeroCallCore
namespace DuplicatePrefix.LanguageZeroDispatch
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open DuplicatePrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem not_foreign : CompilerCallFacts.isForeignItem PreparedReflection.actual.compiler.intrinsics
    GuardCompilerFacts.languageCall.callee = .ok false := by with_unfolding_all rfl

theorem find_mir (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : CanonicalConfigFacts.RootState) (args : Array (FnArg Provenance))
    (destination : RuntimeStackPlace Provenance) (target : Option MIR.BasicBlockId)
    (unwind : MIR.UnwindAction)
    (backend : state.machine.user.payload.payload.user.backend = .none)
    (noRace : state.machine.dataRace = none) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).findMirOrEvalFn ()
      GuardCompilerFacts.languageCall.callee GuardCompilerFacts.languageAbi args destination target unwind state =
      .ok (some (CopyPreconditions.Bodies.checkLanguage.loaded,
        GuardCompilerFacts.languageCall.callee)) state := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  change CallDispatchMachine.findMirOrEvalFn cfg.calls.dispatch () _ _ _ _ _ _ state = _
  have foreign : cfg.calls.dispatch.isForeignItem GuardCompilerFacts.languageCall.callee =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    obtain ⟨foreign, handler, dynSym, constructed⟩ := fields.callsDispatchConstruction
    rw [constructed]
    with_unfolding_all change (match CompilerCallFacts.isForeignItem PreparedReflection.actual.compiler.intrinsics
      GuardCompilerFacts.languageCall.callee with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [not_foreign]
  have load : cfg.calls.dispatch.loadMir () GuardCompilerFacts.languageCall.callee state =
      .ok CopyPreconditions.Bodies.checkLanguage.loaded state := by
    rw [fields.dispatchLoadMir]
    exact GuardCompilerFacts.actual_language_load options () remaining span state
  have sourceBackend := fields.callsBackend
  unfold CallDispatchMachine.findMirOrEvalFn
  rw [foreign, sourceBackend]
  simp only [pure, Pure.pure, EStateM.pure, bind, EStateM.bind]
  simp [ EvalBackendMachine.handler, backend, noRace,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  simp only [Except.pure, Except.bind, bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [load]

#print axioms find_mir
end DuplicatePrefix.LanguageZeroDispatch
