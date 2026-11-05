import empty_function.BodyDictionaries

/-! The local-place fields used by the one unit assignment, extracted from the
canonical factory at its successful construction boundary. -/
namespace EmptyFunction.BodyPlaceDictionaries
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def validation (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) :
    Unit → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind RootUser Unit :=
  fun choice place => match EvalConfigurationCore.make p image bytes options leaves () remaining with
    | .error error => throw error
    | .ok inner => ValidityMachine.validateRuntime inner.validity choice options.limits.validation place true

structure Fields (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (config : Config) : Prop where
  projection : config.projection.place = ValidityMachine.placeHooks config.access config.allocation config.compiler
  compatible : config.copy.compatible = CompilerCovariance.compatible p options.place.debugAssertions
  padding : config.copy.hasPadding = CompilerCopy.hasPadding p.runtime options.place.debugAssertions
  checkPlace : config.compiler.checkPlaceType = CompilerPlaceTypes.place p options.place.debugAssertions
    (CompilerCovariance.hook p options.place.debugAssertions)
  enforce : config.compiler.enforceValidity = fun _ _ => ValidityMachine.enforceValidity
  localSpan : config.compiler.localSpan = CompilerFrameContext.localSpan p
  validate : config.compiler.validate = validation p image bytes options leaves remaining

 theorem fields_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config) :
    Fields p image bytes options leaves remaining config := by
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext] at built
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure] at built
  simp only [contract.maximum_eq, EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq, EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure] at built
  have same := Except.ok.inj built
  subst config
  constructor
  all_goals try with_unfolding_all rfl
  case validate =>
    funext choice place state
    simp only [EvalPlaceConstruction.compiler, validation, EvalConfigurationCore.make_eq_context, Except.map]
    cases result : EvalConfigurationCore.makeWithForeignContext (Assembly := Unit)
      p image bytes options leaves () none none remaining <;> rfl

end EmptyFunction.BodyPlaceDictionaries
