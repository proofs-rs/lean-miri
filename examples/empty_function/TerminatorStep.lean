import empty_function.CanonicalInit
namespace EmptyFunction.TerminatorStep
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def hooks (prepared : EvalPreparation.Prepared) (options : EvalConfigurationCore.Options) :
    TerminatorMachine.Hooks MiriMemoryKind RootUser Unit :=
  EvalTerminatorMachine.genericHooks (Configuration.leaves prepared options.place.debugAssertions).control
    (EvalTerminatorMachine.ioGc (Configuration.leaves prepared options.place.debugAssertions).blockingSources)

theorem source_of_make (prepared : EvalPreparation.Prepared) (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (contract : Construction prepared.compiler)
    (config : WholeCall.Config)
    (built : EvalConfigurationCore.make prepared.compiler prepared.image bytes options
      (Configuration.leaves prepared options.place.debugAssertions) () (remaining+1) = .ok config) :
    config.terminators = hooks prepared options := by
  rw [EvalConfigurationCore.make_eq_context,EvalConfigurationCore.makeWithForeignContext] at built
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq,EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    contract.i32_eq,contract.bool_eq,contract.u8_eq,contract.unit_eq,CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  have same := Except.ok.inj built
  subst config
  with_unfolding_all rfl

def tick (clock : Clock.Monotonic Unit) : Clock.Monotonic Unit :=
  match clock with
  | .host epoch => .host epoch
  | .virtual time => .virtual (BitVec.ofNat 128 (time.toNat+5000))
def advanced (control : TerminatorMachine.Control Unit) : TerminatorMachine.Control Unit :=
  {control with
    basicBlockCount := control.basicBlockCount+1
    sinceGc := control.sinceGc+1
    monotonic := tick control.monotonic}
def setControl (user : RootUser) (control : TerminatorMachine.Control Unit) : RootUser :=
  {user with payload := {user.payload with payload := {user.payload.payload with user :=
    {user.payload.payload.user with host := {user.payload.payload.user.host with control}}}}}
def after (state : WholeCall.State) : WholeCall.State :=
  {state with machine := {state.machine with user := setControl state.machine.user (advanced state.machine.user.payload.payload.user.host.control)}}

 theorem before_fixed (prepared : EvalPreparation.Prepared) (options : EvalConfigurationCore.Options)
    (preempt : MachineHooks.M MiriMemoryKind RootUser Bool) (state : WholeCall.State)
    (fixed : state.machine.threads.fixedScheduling = true)
    (gc : state.machine.user.payload.payload.user.host.control.gcInterval = 0)
    (unchecked : state.machine.user.payload.payload.user.host.control.checkedArithmetic = false) :
    TerminatorMachine.beforeTerminatorWithChoice (hooks prepared options) preempt state = .ok () (after state) := by
  unfold TerminatorMachine.beforeTerminatorWithChoice
  simp only [hooks,EvalTerminatorMachine.genericHooks,Configuration.leaves,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  simp only [unchecked,Bool.false_and,Bool.false_eq_true,↓reduceIte]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  rw [TerminatorMachine.updateControl_eq]
  simp only
  simp only [bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  simp only [unchecked,Bool.false_and,Bool.false_eq_true,↓reduceIte]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  rw [TerminatorMachine.updateControl_eq]
  simp only
  simp only [bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  simp only [gc,UInt32.lt_irrefl,Bool.false_and,Bool.false_eq_true,↓reduceIte]
  simp only [TerminatorMachine.maybePreemptWithChoice,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,fixed,
    Bool.true_eq_false,↓reduceIte]
  cases clock : state.machine.user.payload.payload.user.host.control.monotonic <;>
    simp [Clock.Monotonic.tick,unchecked,fixed,gc,TerminatorMachine.updateControl_eq,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
      after,setControl,advanced,tick,clock,Except.pure,Except.bind,Bind.bind,Pure.pure]
  all_goals try rfl

 theorem canonical (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : WholeCall.State) (fixed : state.machine.threads.fixedScheduling = true)
    (gc : state.machine.user.payload.payload.user.host.control.gcInterval = 0)
    (unchecked : state.machine.user.payload.payload.user.host.control.checkedArithmetic = false) :
    (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator () state = (after state,.ok ()) := by
  obtain ⟨remaining,eq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have source := source_of_make s.prepared s.bytes s.options remaining metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,eq] using s.built)
  change MachineHooks.run (TerminatorMachine.beforeTerminatorWithChoice s.cfg.terminators
    (s.cfg.preemptionChoice ())) state = _
  rw [source]
  have result := before_fixed s.prepared s.options (s.cfg.preemptionChoice ()) state fixed gc unchecked
  simp only [MachineHooks.run,Call.run,result]
end EmptyFunction.TerminatorStep
