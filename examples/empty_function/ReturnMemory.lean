import empty_function.BodyCopy
import empty_function.UnitProtection

/-! The zero-sized physical return write and its actual shallow validator. -/
namespace EmptyFunction.ReturnMemory
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure Fields (config : WholeCall.Config) : Prop where
  toMemory : ∀ (place : MPlaceTy Provenance) (state : WholeCall.State),
    config.validity.toOp () ⟨.memory place.mplace,place.layout⟩ state =
      .ok ⟨.indirect place.mplace,place.layout⟩ state
  dynamic : ∀ (place : MPlaceTy Provenance), place.layout.layout.isSized = true →
    config.validity.sizeAndAlign () place = pure (some (place.layout.layout.size,place.layout.layout.align.abi))
  afterPop : ∀ choice frame, config.lifecycle.afterPop choice frame false = pure .normal
  padding : config.validity.beginPadding = fun _ =>
    ValidityMemory.beginPadding (ValidityMachine.memoryEnvironment config.access)

 theorem fields_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : WholeCall.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config) :
    Fields config := by
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext] at built
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure] at built
  simp only [contract.maximum_eq, EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq, EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure] at built
  have same := Except.ok.inj built
  subst config
  constructor
  case toMemory => intro place state; with_unfolding_all rfl
  case dynamic =>
    intro place sized
    funext state
    with_unfolding_all
      change DynamicLayout.sizeAndAlignFromMeta _ _ _ _ place.layout state = _
      unfold DynamicLayout.sizeAndAlignFromMeta
      rw [sized]
      rfl
  case afterPop =>
    intro choice frame
    funext state
    simp only [CompilerCallConstruction.lifecycle,Unwind.afterStackPop,Bool.false_eq_true,↓reduceIte]
  case padding => with_unfolding_all rfl

 theorem padding_zero (access : ValidityMachine.Access MiriMemoryKind CanonicalDictionaries.Stored)
    (place : MPlaceTy Provenance) (state : WholeCall.State)
    (retain : ∀ machine, access.retainTouched machine none = machine) :
    ValidityMemory.beginPadding (ValidityMachine.memoryEnvironment access) place Size.ZERO state = .ok none state := by
  apply ValidityMemory.beginPadding_zero
  simp only [ValidityMachine.memoryEnvironment,retain, PlaceMachine.AccessState.mk.injEq]

 theorem shallow_unit
    (h : BodyDictionaries.Visitor) (fuel : Nat) (state : WholeCall.State)
    (place : MPlaceTy Provenance) (name : String)
    (noGhost : state.machine.user.payload.ghost = false)
    (ghost : @h.withGhostValidation = @ValidityMachine.withGhostValidation MiriMemoryKind CanonicalDictionaries.Stored)
    (nameQuery : h.typeName () place.layout.ty state = .ok name state)
    (readQuery : h.toOp () ⟨.memory place.mplace,place.layout⟩ (BodyValidation.active state) =
      .ok ⟨.indirect place.mplace,place.layout⟩ (BodyValidation.active state))
    (classify : h.classify () place.layout.ty (BodyValidation.active state) =
      .ok (.aggregate false false false) (BodyValidation.active state))
    (inhabited : h.opsemInhabited () place.layout.ty (BodyValidation.active state) = .ok true (BodyValidation.active state))
    (size : place.layout.layout.size = Size.ZERO)
    (dynamic : h.sizeAndAlign () place (BodyValidation.active state) =
      .ok (some (Size.ZERO,place.layout.layout.align.abi)) (BodyValidation.active state))
    (padding : h.beginPadding () place Size.ZERO (BodyValidation.active state) = .ok none (BodyValidation.active state))
    (fields : place.layout.layout.fields = .Arbitrary #[] #[])
    (variants : place.layout.layout.variants = .Single 0) (debugOff : h.debugAssertions = false) :
    ValidityVisitor.validatePlace h () (fuel+1) ⟨.memory place.mplace,place.layout⟩ false true state = .ok () state := by
  let session := {BodyValidation.session name with dataBytes := some .empty}
  have visited := ValidityVisitor.visit_fieldless h () fuel session ⟨.memory place.mplace,place.layout⟩
    (BodyValidation.active state) 0 classify inhabited fields variants rfl debugOff
  have reset := ValidityVisitor.resetPadding_memory_zero h () session place
    (BodyValidation.active state) rfl size dynamic padding
  unfold ValidityVisitor.validatePlace
  simp only [ghost,bind,Bind.bind,EStateM.bind,nameQuery,ValidityMachine.withGhostValidation,
    noGhost,Bool.false_eq_true,↓reduceIte]
  simp only [BodyValidation.active,session,BodyValidation.session] at readQuery visited reset
  simp only [readQuery,pure,Pure.pure,EStateM.pure,visited,reset,bind,Bind.bind,EStateM.bind]
  cases state
  simp_all
  rename_i stack machine
  rw [←noGhost]

 theorem canonical_unit (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (config : WholeCall.Config)
    (built : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
      (Configuration.leaves s.prepared s.options.place.debugAssertions) () (remaining+1) = .ok config)
    (state : WholeCall.State) (place : MPlaceTy Provenance)
    (layout : place.layout = s.abi.ret.layout) (noGhost : state.machine.user.payload.ghost = false)
    (fuel : Nat) :
    ValidityVisitor.validatePlace config.validity () (fuel+1) ⟨.memory place.mplace,place.layout⟩ false true state =
      .ok () state := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have methods := BodyDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    leaves remaining metadata.construction config built
  have memory := fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    leaves remaining metadata.construction config built
  have dictionaries := CanonicalDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    leaves remaining metadata.construction config built
  have classifyEq : config.validity.classify =
      (CompilerFactAdapters.validityHooks s.prepared.compiler.lifecycle.calls.symbols.facts config.validity).classify :=
    congrArg BodyDictionaries.Queries.classify methods
  have nameEq : config.validity.typeName =
      (CompilerFactAdapters.validityHooks s.prepared.compiler.lifecycle.calls.symbols.facts config.validity).typeName :=
    congrArg BodyDictionaries.Queries.typeName methods
  have inhabitedEq : config.validity.opsemInhabited =
      (CompilerFactAdapters.validityHooks s.prepared.compiler.lifecycle.calls.symbols.facts config.validity).opsemInhabited :=
    congrArg BodyDictionaries.Queries.inhabited methods
  have ghostEq : @config.validity.withGhostValidation =
      @ValidityMachine.withGhostValidation MiriMemoryKind CanonicalDictionaries.Stored :=
    congrArg (fun q => @q.ghost) methods
  have debugEq : config.validity.debugAssertions = s.options.place.debugAssertions :=
    congrArg BodyDictionaries.Queries.debug methods
  obtain ⟨node, nodeFound⟩ := metadata.unitNode
  have sized : place.layout.layout.isSized = true := by rw [layout]; exact metadata.unitSized
  apply shallow_unit config.validity fuel state place node.display noGhost ghostEq
  · rw [nameEq,layout]
    exact BodyQueries.adapter_name _ _ () _ _ node nodeFound
  · exact memory.toMemory place _
  · rw [classifyEq,layout]
    exact BodyQueries.adapter_classifier _ _ () _ _ metadata.unitKind
  · rw [inhabitedEq,layout]
    exact BodyQueries.adapter_inhabited _ _ () _ _ metadata.unitInhabited
  · rw [layout]; exact metadata.unitSize
  · rw [memory.dynamic place sized]
    simp only [layout,metadata.unitSize,pure,Pure.pure,EStateM.pure]
  · rw [memory.padding]
    apply padding_zero
    intro machine
    rw [dictionaries.retainTouched]
  · rw [layout]; exact metadata.unitFields
  · rw [layout]; exact metadata.unitVariants
  · exact debugEq.trans profile.debug

 theorem validate (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (state : WholeCall.State) (place : MPlaceTy Provenance)
    (layout : place.layout = s.abi.ret.layout)
    (noGhost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow) :
    s.cfg.projection.place.validate () ⟨.memory place.mplace,place.layout⟩ state = .ok () state := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options) leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    leaves (remaining+1) metadata.construction s.cfg outer
  obtain ⟨inner,innerBuilt,_⟩ := CanonicalDictionaries.make_fields s.prepared.compiler s.prepared.image
    s.bytes (EmptyFunction.Configuration.proofOptions s.options) leaves remaining metadata.construction
  have valid := canonical_unit s metadata profile remaining inner innerBuilt state place layout noGhost
    (s.options.limits.validation-1)
  have budget : s.options.limits.validation = (s.options.limits.validation-1)+1 := by omega
  rw [fields.projection]
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks]
  rw [fields.validate]
  simp only [BodyPlaceDictionaries.validation,innerBuilt]
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,shallow,pure,Pure.pure,EStateM.pure,
    show (ValidityMachine.ValidationMode.Shallow == .Deep) = false from by decide]
  rw [budget]
  exact valid

 theorem write (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (state : WholeCall.State) (place : MPlaceTy Provenance)
    (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none) :
    writePlaceImmediateNoValidate s.cfg.projection.place () .uninit ⟨.memory place.mplace,place.layout⟩ state =
      .ok () state := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options) leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    leaves (remaining+1) metadata.construction s.cfg outer
  have dictionaries := CanonicalDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    leaves (remaining+1) metadata.construction s.cfg outer
  have sized : place.layout.layout.isSized = true := by rw [layout]; exact metadata.unitSized
  have unitLayout : localMemoryLayout place.layout =
      ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩ := by
    simp [localMemoryLayout,layout,metadata.unitSize,metadata.unitAlign,metadata.unitBackend]
  have encoding : place.mplace = ⟨place.mplace.ptr,.none,none⟩ := by
    cases found : place.mplace
    simp_all
  have target : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace =
      .ok s.cfg.access.runtime.pointerSize := by
    simp [RuntimeTargetDataLayout.pointerSizeIn,RuntimeTargetDataLayout.pointerSpecIn,
      RuntimeTargetDataLayout.pointerSize,Except.pure]
    rfl
  have written := PlaceMachine.writeMemory_zero_uninit
    {s.cfg.access with ghostMode := state.machine.user.payload.ghost}
    (fun _ => state.machine.user.payload.validation != .No) place place.mplace.ptr (some place.layout.ty)
    s.cfg.access.runtime.pointerSize unitLayout encoding target
    (fun machine => by rw [dictionaries.retainTouched]) state
  rw [fields.projection]
  unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
  simp only [sized,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  simpa only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    ValidityMachine.scopedAccess,ValidityMachine.validationInProgress,ValidityMachine.enforceValidity,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure] using written

 theorem copy (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (state : WholeCall.State) (place : MPlaceTy Provenance)
    (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (noGhost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow) :
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      ⟨.memory place.mplace,place.layout⟩ true state = .ok () state := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options) leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    leaves (remaining+1) metadata.construction s.cfg outer
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [fields.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [fields.padding]
    simp [CompilerCopy.hasPadding,metadata.unitBackend,pure,Except.pure]
  have written := write s metadata profile remaining capacity state place layout noMeta aligned
  have copied : copyRuntimePlaceNoValidate s.cfg.projection.place s.cfg.copy ()
      ⟨.immediate .uninit,s.abi.ret.layout⟩ ⟨.memory place.mplace,place.layout⟩ true state = .ok () state := by
    simp only [copyRuntimePlaceNoValidate,layout,compatible,placeLift_ok,padding,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,metadata.unitSized,
      Bool.not_true,Bool.false_and,Bool.false_or,Bool.false_eq_true,↓reduceIte,bne_self_eq_false]
    simpa only [layout] using written
  have valid := validate s metadata profile remaining capacity positive state place layout noGhost shallow
  unfold copyRuntimePlace
  simp only [bind,Bind.bind,EStateM.bind,copied]
  simp only [layout,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  rw [fields.projection] at valid ⊢
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    ValidityMachine.enforceValidity,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    shallow,pure,Pure.pure,EStateM.pure,
    show (ValidityMachine.ValidationMode.Shallow != .No) = true from by decide,↓reduceIte]
  simpa only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,layout] using valid

end EmptyFunction.ReturnMemory
