import empty_function.ProjectedMaterialize
import empty_function.LocalReturn
namespace EmptyFunction.ProjectedCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Internal composition edge: the materialization equation comes from raw
current resources, and the final local validation equation comes from the
shared projected-indirect validator. Neither is an initial-input assumption. -/
theorem from_force (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (state after : State) (index : Nat) (id : MIR.LocalId) (offset : Size) (identity : LocalsIdentity)
    (place : MPlaceTy Provenance) (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (forced : forceAllocation s.cfg.projection.place ()
      ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ state = .ok place after)
    (shallow : after.machine.user.payload.validation = .Shallow)
    (validated : s.cfg.projection.place.validate ()
      ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ after = .ok () after) :
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ true state = .ok () after := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have built : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg built
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [fields.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [fields.padding]
    simp [CompilerCopy.hasPadding,metadata.unitBackend,pure,Except.pure]
  have written := ReturnMemory.write s metadata profile remaining capacity after place layout noMeta aligned
  unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal at written
  simp only [layout,metadata.unitSized,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure] at written
  have copied : copyRuntimePlaceNoValidate s.cfg.projection.place s.cfg.copy ()
      ⟨.immediate .uninit,s.abi.ret.layout⟩ ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ true state =
      .ok () after := by
    simp only [copyRuntimePlaceNoValidate,compatible,placeLift_ok,padding,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,metadata.unitSized,
      Bool.not_true,Bool.false_and,Bool.false_or,Bool.false_eq_true,↓reduceIte,bne_self_eq_false]
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    simp only [metadata.unitSized,Bool.not_true,Bool.false_eq_true,↓reduceIte,
      Option.isSome_some,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,forced,written]
    simpa only [←layout] using written
  unfold copyRuntimePlace
  simp only [bind,Bind.bind,EStateM.bind,copied,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  rw [fields.projection] at validated ⊢
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    ValidityMachine.enforceValidity,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    shallow,pure,Pure.pure,EStateM.pure,
    show (ValidityMachine.ValidationMode.Shallow != .No) = true from by decide,↓reduceIte]
  simpa only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks] using validated

theorem control_from_force (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (state after : State) (index : Nat) (id : MIR.LocalId) (offset : Size) (identity : LocalsIdentity)
    (place : MPlaceTy Provenance) (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (forced : forceAllocation s.cfg.projection.place ()
      ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ state = .ok place after)
    (shallow : after.machine.user.payload.validation = .Shallow)
    (validated : s.cfg.projection.place.validate ()
      ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ after = .ok () after) :
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (.frameLocal index id (some offset) s.abi.ret.layout identity) state = (after,.ok ()) := by
  have copied := from_force s metadata profile remaining capacity state after index id offset identity place
    layout noMeta aligned forced shallow validated
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have built : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg built
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [fields.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [fields.padding]
    simp [CompilerCopy.hasPadding,metadata.unitBackend,pure,Except.pure]
  have boundCopy : copyRuntimePlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation s.cfg s.limits)).place
      (ExecutionMachine.withValidation s.cfg s.limits).copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ true =
      copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
        ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ true := by
    funext before
    simp [ExecutionMachine.withValidation,ExecutionMachine.projectionHooks,TypedMachineBindings.bindValidation,
      copyRuntimePlace,copyRuntimePlaceNoValidate,compatible,padding,metadata.unitSized,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  change MachineHooks.run (copyRuntimePlace _ _ () _ _ true) state = _
  simp only [RuntimeStackPlace.toRuntimePlace]
  rw [boundCopy]
  simp only [MachineHooks.run,Call.run,copied]

end EmptyFunction.ProjectedCopy
