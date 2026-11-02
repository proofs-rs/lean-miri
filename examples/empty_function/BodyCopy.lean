import empty_function.BodyPlaceDictionaries
import empty_function.BodyCanonicalValidation
import empty_function.Specification

/-! The actual unit assignment copy, including the nested validation factory.
Only initial numeric capacity and pure compiler metadata supply its checks. -/
namespace EmptyFunction.BodyCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

 theorem validate_unit (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    s.cfg.projection.place.validate () (BodyStep.destination frames frame s.abi.ret.layout)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .ok () (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  obtain ⟨inner, innerBuilt, _⟩ := CanonicalDictionaries.make_fields s.prepared.compiler s.prepared.image
    s.bytes s.options leaves remaining metadata.construction
  obtain ⟨node, nodeFound⟩ := metadata.unitNode
  have budget : s.options.limits.validation = (s.options.limits.validation-1)+1 := by omega
  have valid := BodyCanonicalValidation.unit s.prepared.compiler s.prepared.image s.bytes s.options
    leaves remaining metadata.construction inner innerBuilt frames frame machine s.abi.ret.layout
    (s.options.limits.validation-1) profile.debug metadata.unitSized noClocks noGhost
    metadata.unitKind node nodeFound metadata.unitInhabited metadata.unitFields metadata.unitVariants
  rw [fields.projection]
  simp only [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks]
  rw [fields.validate]
  simp only [BodyPlaceDictionaries.validation, innerBuilt]
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively, BodyStep.current, LocalUnit.current,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    shallow, show (ValidityMachine.ValidationMode.Shallow == .Deep) = false from by decide, beq_self_eq_true, pure, Pure.pure, EStateM.pure]
  rw [budget]
  simpa only [BodyStep.current, LocalUnit.current] using valid

 theorem unit (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (BodyStep.destination frames frame s.abi.ret.layout) false
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .ok () (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have source := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  have dictionaries := CanonicalDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [source.compatible]
    simp [CompilerCovariance.compatible, CompilerCovariance.relation, CompilerCovariance.relationWithIndex,
      profile.debug, Except.mapError, bind, Except.bind, pure, Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [source.padding]
    simp [CompilerCopy.hasPadding, metadata.unitBackend, pure, Except.pure]
  have written := BodyStep.copy_zero_no_validate s.cfg.access s.cfg.allocation s.cfg.compiler s.cfg.copy ()
    frames frame machine s.abi.ret.layout metadata.unitSized (dictionaries.debug.trans profile.debug)
    (dictionaries.debugAbi profile.debug) compatible padding noClocks
  have valid := validate_unit s metadata profile remaining capacity positive frames frame machine noClocks noGhost shallow
  rw [source.projection] at valid ⊢
  unfold copyRuntimePlace
  simp only [bind, Bind.bind, EStateM.bind, written]
  simp only [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
    ValidityMachine.enforceValidity, BodyStep.current, LocalUnit.current, BodyStep.destination,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    shallow, show (ValidityMachine.ValidationMode.Shallow != .No) = true from by decide,
    pure, Pure.pure, EStateM.pure, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simpa only [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
    BodyStep.current, LocalUnit.current, BodyStep.destination] using valid

end EmptyFunction.BodyCopy
