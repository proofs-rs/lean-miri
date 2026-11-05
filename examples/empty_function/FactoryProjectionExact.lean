import empty_function.FactoryProjection
namespace EmptyFunction.FactoryProjectionExact
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem projection (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : WholeCall.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (state : WholeCall.State) :
    config.compiler.projection () state = .ok
      (EvalProjectionMachine.context p.lifecycle.calls.symbols.facts contract.maximum options.place.debugAssertions
        (pointerSource p image leaves).pointers state) state := by
  rw [EvalConfigurationCore.make_eq_context,EvalConfigurationCore.makeWithForeignContext] at built
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq,EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    contract.i32_eq,contract.bool_eq,contract.u8_eq,contract.unit_eq,CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  simp only [contract.maximum_eq,EvalConfigurationCore.pureQuery_eq,EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    contract.i32_eq,contract.bool_eq,contract.u8_eq,contract.unit_eq,CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  have same := Except.ok.inj built
  subst config
  with_unfolding_all rfl
end EmptyFunction.FactoryProjectionExact
