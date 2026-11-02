import empty_function.ConcreteProtection
namespace EmptyFunction.FactoryProjection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def action (pointers : Pointers) : Unit → MemPlace Provenance → Size → OffsetMode → MemPlaceMeta Provenance →
    MachineHooks.M MiriMemoryKind RootUser (MemPlace Provenance) :=
  fun _ place offset mode metadata state =>
    match EvalProjectionMachine.memoryOffset pointers state place offset mode metadata with
    | .ok value => .ok value state
    | .error error => .error (IntrinsicVectorMachine.projectionError error) state

structure Fields (config : WholeCall.Config) (pointers : Pointers) : Prop where
  memory : config.compiler.memoryOffset = action pointers
  projection : ∀ state : WholeCall.State, ∃ context : ProjectionCx Provenance,
    config.compiler.projection () state = .ok context state ∧
    context.memoryOffset = EvalProjectionMachine.memoryOffset pointers state
  validityMemory : config.validity.projection.place.memoryOffset = config.compiler.memoryOffset

theorem fields_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : WholeCall.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config) :
    Fields config (pointerSource p image leaves).pointers := by
  rw [EvalConfigurationCore.make_eq_context,EvalConfigurationCore.makeWithForeignContext] at built
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq,EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    contract.i32_eq,contract.bool_eq,contract.u8_eq,contract.unit_eq,contract.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  simp only [contract.maximum_eq,EvalConfigurationCore.pureQuery_eq,EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    contract.i32_eq,contract.bool_eq,contract.u8_eq,contract.unit_eq,contract.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  have same := Except.ok.inj built
  subst config
  constructor
  · funext choice place offset mode metadata state
    simp only [EvalPlaceConstruction.compiler,action,get,getThe,MonadStateOf.get,EStateM.get,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    cases computed : EvalProjectionMachine.memoryOffset (pointerSource p image leaves).pointers state place offset mode metadata
    all_goals simp only [computed]
    all_goals with_unfolding_all rfl
  · intro state
    refine ⟨EvalProjectionMachine.context p.lifecycle.calls.symbols.facts contract.maximum
      options.place.debugAssertions (pointerSource p image leaves).pointers state,?_,?_⟩
    · with_unfolding_all rfl
    · with_unfolding_all rfl
  · with_unfolding_all rfl

theorem fields (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    Fields s.cfg (ConcreteProtection.source s).pointers := by
  obtain ⟨remaining,eq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  exact fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    (Configuration.leaves s.prepared s.options.place.debugAssertions) remaining metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,eq] using s.built)
end EmptyFunction.FactoryProjection
