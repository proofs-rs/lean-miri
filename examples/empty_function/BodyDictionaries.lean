import empty_function.BodyConstantDictionary
import empty_function.BodyQueries

/-! Only the compiler-query projection of the canonical factory is expanded.
The actual runtime operations remain the production operations. -/
namespace EmptyFunction.BodyDictionaries
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

abbrev State := MachineHooks.State MiriMemoryKind RootUser
structure Queries where
  classify : Unit → TyId → MachineHooks.M MiriMemoryKind RootUser ValidityVisitor.TypeKind
  typeName : Unit → TyId → MachineHooks.M MiriMemoryKind RootUser String
  inhabited : Unit → TyId → MachineHooks.M MiriMemoryKind RootUser Bool
  debug : Bool
  ghost : {A : Type} → MachineHooks.M MiriMemoryKind RootUser A → MachineHooks.M MiriMemoryKind RootUser A

def queries (config : Config) : Queries :=
  ⟨config.validity.classify,config.validity.typeName,config.validity.opsemInhabited,config.validity.debugAssertions,
    @config.validity.withGhostValidation⟩

abbrev Visitor := ValidityVisitor.Hooks Provenance State Unit MachineHooks.FrameExtra
  (FnVal Unit) (FnAbi TyId) ValidityMemory.PaddingHandle

def source (p : CompilerProviders.Prepared) (options : EvalConfigurationCore.Options)
    (base : Visitor) : Queries :=
  let methods := CompilerFactAdapters.validityHooks p.lifecycle.calls.symbols.facts base
  ⟨methods.classify,methods.typeName,methods.opsemInhabited,options.place.debugAssertions,
    @ValidityMachine.withGhostValidation MiriMemoryKind (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost)⟩

 theorem projected (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p)
    (base : Visitor) :
    (EvalConfigurationCore.make p image bytes options leaves () (remaining+1)).map queries =
      .ok (source p options base) := by
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  simp only [contract.maximum_eq, EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq, EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  with_unfolding_all rfl

 theorem fields_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config) :
    queries config = source p options config.validity := by
  have law := projected p image bytes options leaves remaining contract config.validity
  rw [built] at law
  exact Except.ok.inj law

 theorem projected_read (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    (EvalConfigurationCore.make p image bytes options leaves () (remaining+1)).map
      (fun config => config.validity.toOp () (BodyStep.destination frames frame unit)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some unit)) machine)) =
      .ok (.ok ⟨.immediate .uninit,unit⟩
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some unit)) machine)) := by
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  simp only [contract.maximum_eq, EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq, EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  apply congrArg Except.ok
  cases flag : machine.user.payload.ghost <;> with_unfolding_all
    simp [EvalValidityMachine.hooks, TypedValidityProviders.visitor, ExecutionValidity.hooks,
      ValidityMachine.visitor, CompilerPaths.validityHooks, CompilerFactAdapters.validityHooks,
      PointerPlaceMachine.bindCompiler, placeToOp, placeToOpCore,
      ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
      PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
      EvalPlaceConstruction.compiler, ValidityMachine.validationInProgress,
      BodyStep.destination, sized, debugOff, noClocks, flag,
      MachineHooks.afterLocalRead, MachineHooks.currentFrame, BodyStep.current, LocalUnit.current,
      BodyStep.withUnit, LocalUnit.withUnit, Frame.getLocalOperand, Frame.getLocal, Stack.frameIndex,
      Stack.currentFrame?, LocalState.access, Except.mapError, Except.pure, Except.bind,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]

 theorem read_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    config.validity.toOp () (BodyStep.destination frames frame unit)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some unit)) machine) =
      .ok ⟨.immediate .uninit,unit⟩
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some unit)) machine) := by
  have law := projected_read p image bytes options leaves remaining contract frames frame machine unit
    debugOff sized noClocks
  rw [built] at law
  exact Except.ok.inj law

end EmptyFunction.BodyDictionaries
