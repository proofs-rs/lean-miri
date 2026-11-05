import empty_function.LocalIndirectRead
import empty_function.ReturnMemory
import empty_function.MetadataBinding
namespace EmptyFunction.LocalIndirectReturnCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
variable {K U C : Type}
abbrev F := LocalUnit.F

def destination (frames : Array F) (frame : F) (id : MIR.LocalId) (layout : LocalLayout) : RuntimePlace Provenance :=
  ⟨.local frames.size id none frame.localsIdentity,layout⟩

theorem write_as_memory [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance)
    (unit : LocalLayout) (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.indirect memory))
    (sized : unit.layout.isSized = true) (debugOff : compiler.debugAssertions = false) :
    writePlaceImmediateNoValidate (ValidityMachine.placeHooks access allocation compiler) choice .uninit
      (destination frames frame id unit) (LocalUnit.current frames frame machine) =
    writePlaceImmediateNoValidate (ValidityMachine.placeHooks access allocation compiler) choice .uninit
      ⟨.memory memory,unit⟩ (LocalUnit.current frames frame machine) := by
  have got := LocalIndirectRead.get_operand frame id slot atSlot memory live
  with_unfolding_all
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    simp [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
      requireCurrent_eq,checkLocalIdentity_debugOff,destination,sized,debugOff,got,
      MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,Stack.frameIndex,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,Except.pure,Except.bind,Except.mapError]
 theorem projected_read (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (cache : slot.layout=some unit)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    (EvalConfigurationCore.make p image bytes options leaves () (remaining+1)).map
      (fun config => config.validity.toOp () (destination frames frame id unit)
        (LocalUnit.current frames frame machine)) =
      .ok (.ok ⟨.indirect memory,unit⟩
        (LocalUnit.current frames frame machine)) := by
  have got := LocalImmediate.get_local frame id slot atSlot
  have operand := LocalIndirectRead.get_operand frame id slot atSlot memory live
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  simp only [contract.maximum_eq, EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq, EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  apply congrArg Except.ok
  cases flag : machine.user.payload.ghost <;> with_unfolding_all
    simp [EvalValidityMachine.hooks, TypedValidityProviders.visitor, ExecutionValidity.hooks,
      ValidityMachine.visitor, CompilerPaths.validityHooks, CompilerFactAdapters.validityHooks,
      PointerPlaceMachine.bindCompiler, placeToOp, placeToOpCore,
      ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
      PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
      EvalPlaceConstruction.compiler, ValidityMachine.validationInProgress,
      destination, got,operand,cache,sized, debugOff, noClocks, flag,
      MachineHooks.afterLocalRead, MachineHooks.currentFrame, BodyStep.current, LocalUnit.current,
      Stack.frameIndex,
      Stack.currentFrame?, LocalState.access, Except.mapError, Except.pure, Except.bind,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]

 theorem read_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : CanonicalDictionaries.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (cache : slot.layout=some unit)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    config.validity.toOp () (destination frames frame id unit)
      (LocalUnit.current frames frame machine) =
      .ok ⟨.indirect memory,unit⟩
        (LocalUnit.current frames frame machine) := by
  have law := projected_read p image bytes options leaves remaining contract frames frame machine unit id slot memory atSlot live cache
    debugOff sized noClocks
  rw [built] at law
  exact Except.ok.inj law

 theorem projected_force (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (cache : slot.layout=some unit)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    (EvalConfigurationCore.make p image bytes options leaves () (remaining+1)).map
      (fun config => forceAllocation config.validity.projection.place () (destination frames frame id unit)
        (LocalUnit.current frames frame machine)) =
      .ok (.ok (⟨memory,unit⟩ : MPlaceTy Provenance)
        (LocalUnit.current frames frame machine)) := by
  have got := LocalImmediate.get_local frame id slot atSlot
  have operand := LocalIndirectRead.get_operand frame id slot atSlot memory live
  rw [EvalConfigurationCore.make_eq_context, EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq,
    EvalConfigurationCore.pureQuery_eq, EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  simp only [contract.maximum_eq, EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq, EvalMathMachine.hooks, CompilerCallConstruction.helpers,
    contract.i32_eq, contract.bool_eq, contract.u8_eq, contract.unit_eq, CompilerProviders.Prepared.rootSpan_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  apply congrArg Except.ok
  cases flag : machine.user.payload.ghost <;> with_unfolding_all
    simp [EvalValidityMachine.hooks, TypedValidityProviders.visitor, ExecutionValidity.hooks,
      ValidityMachine.visitor, CompilerPaths.validityHooks, CompilerFactAdapters.validityHooks,
      PointerPlaceMachine.bindCompiler, forceAllocation, requireCurrent_eq, checkLocalIdentity_debugOff,
      ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
      PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
      EvalPlaceConstruction.compiler, ValidityMachine.validationInProgress,
      destination, got,operand,cache,sized, debugOff, noClocks, flag,
      MachineHooks.afterLocalRead, MachineHooks.currentFrame, BodyStep.current, LocalUnit.current,
      Stack.frameIndex,
      Stack.currentFrame?, LocalState.access, Except.mapError, Except.pure, Except.bind,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]

 theorem force_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : CanonicalDictionaries.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (cache : slot.layout=some unit)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    forceAllocation config.validity.projection.place () (destination frames frame id unit)
      (LocalUnit.current frames frame machine) =
      .ok (⟨memory,unit⟩ : MPlaceTy Provenance)
        (LocalUnit.current frames frame machine) := by
  have law := projected_force p image bytes options leaves remaining contract frames frame machine unit id slot memory atSlot live cache
    debugOff sized noClocks
  rw [built] at law
  exact Except.ok.inj law

theorem shallow_indirect
    (h : BodyDictionaries.Visitor) (fuel : Nat) (state : WholeCall.State)
    (reference : RuntimePlaceRef Provenance) (place : MPlaceTy Provenance) (name : String)
    (noGhost : state.machine.user.payload.ghost = false)
    (ghost : @h.withGhostValidation = @ValidityMachine.withGhostValidation MiriMemoryKind CanonicalDictionaries.Stored)
    (nameQuery : h.typeName () place.layout.ty state = .ok name state)
    (readQuery : h.toOp () ⟨reference,place.layout⟩ (BodyValidation.active state) =
      .ok ⟨.indirect place.mplace,place.layout⟩ (BodyValidation.active state))
    (forced : forceAllocation h.projection.place () ⟨reference,place.layout⟩ (BodyValidation.active state) =
      .ok place (BodyValidation.active state))
    (classify : h.classify () place.layout.ty (BodyValidation.active state) =
      .ok (.aggregate false false false) (BodyValidation.active state))
    (inhabited : h.opsemInhabited () place.layout.ty (BodyValidation.active state) = .ok true (BodyValidation.active state))
    (size : place.layout.layout.size = Size.ZERO)
    (dynamic : h.sizeAndAlign () place (BodyValidation.active state) =
      .ok (some (Size.ZERO,place.layout.layout.align.abi)) (BodyValidation.active state))
    (padding : h.beginPadding () place Size.ZERO (BodyValidation.active state) = .ok none (BodyValidation.active state))
    (fields : place.layout.layout.fields = .Arbitrary #[] #[])
    (variants : place.layout.layout.variants = .Single 0) (debugOff : h.debugAssertions = false) :
    ValidityVisitor.validatePlace h () (fuel+1) ⟨reference,place.layout⟩ false true state = .ok () state := by
  let session := {BodyValidation.session name with dataBytes := some .empty}
  have visited := ValidityVisitor.visit_fieldless h () fuel session ⟨reference,place.layout⟩
    (BodyValidation.active state) 0 classify inhabited fields variants rfl debugOff
  have reset := ValidityVisitor.resetPadding_forced_zero h () session ⟨reference,place.layout⟩ place
    (BodyValidation.active state) rfl forced size dynamic padding
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
    (built : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options
      (Configuration.leaves s.prepared s.options.place.debugAssertions) () (remaining+1) = .ok config)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (place : MPlaceTy Provenance)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.indirect place.mplace))
    (cache : slot.layout = some place.layout) (noClocks : frame.extra.dataRace = none)
    (layout : place.layout = s.abi.ret.layout) (noGhost : machine.user.payload.ghost = false)
    (fuel : Nat) :
    ValidityVisitor.validatePlace config.validity () (fuel+1) (destination frames frame id place.layout) false true (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame machine) := by
  let state := LocalUnit.current frames frame machine
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have methods := BodyDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves remaining metadata.construction config built
  have memory := ReturnMemory.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves remaining metadata.construction config built
  have dictionaries := CanonicalDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
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
  apply shallow_indirect config.validity fuel state (destination frames frame id place.layout).ref place node.display noGhost ghostEq
  · rw [nameEq,layout]
    exact BodyQueries.adapter_name _ _ () _ _ node nodeFound
  · have read := read_of_make s.prepared.compiler s.prepared.image s.bytes s.options
      leaves remaining metadata.construction config built frames frame
      {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
      place.layout id slot place.mplace atSlot live cache profile.debug sized noClocks
    simpa only [state,BodyValidation.active,LocalUnit.current,destination] using read
  · have forced := force_of_make s.prepared.compiler s.prepared.image s.bytes s.options
      leaves remaining metadata.construction config built frames frame
      {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
      place.layout id slot place.mplace atSlot live cache profile.debug sized noClocks
    simpa only [state,BodyValidation.active,LocalUnit.current,destination] using forced
  · rw [classifyEq,layout]
    exact BodyQueries.adapter_classifier _ _ () _ _ metadata.unitKind
  · rw [inhabitedEq,layout]
    exact BodyQueries.adapter_inhabited _ _ () _ _ metadata.unitInhabited
  · rw [layout]; exact metadata.unitSize
  · rw [memory.dynamic place sized]
    simp only [layout,metadata.unitSize,pure,Pure.pure,EStateM.pure]
  · rw [memory.padding]
    apply ReturnMemory.padding_zero
    intro machine
    rw [dictionaries.retainTouched]
  · rw [layout]; exact metadata.unitFields
  · rw [layout]; exact metadata.unitVariants
  · exact debugEq.trans profile.debug

 theorem validate_unit (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (cache : slot.layout=some s.abi.ret.layout)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    s.cfg.projection.place.validate () (destination frames frame id s.abi.ret.layout)
      (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame machine) := by
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
  have valid := canonical_unit s metadata profile remaining inner innerBuilt frames frame machine id slot ⟨memory,s.abi.ret.layout⟩ atSlot live cache noClocks rfl noGhost
    (s.options.limits.validation-1)
  rw [fields.projection]
  simp only [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks]
  rw [fields.validate]
  simp only [BodyPlaceDictionaries.validation, innerBuilt]
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively, LocalUnit.current,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    shallow, show (ValidityMachine.ValidationMode.Shallow == .Deep) = false from by decide, beq_self_eq_true, pure, Pure.pure, EStateM.pure]
  rw [budget]
  simpa only [LocalUnit.current] using valid

theorem write (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.indirect memory))
    (noMeta : memory.metadata = .none) (aligned : memory.misaligned = none) :
    writePlaceImmediateNoValidate s.cfg.projection.place () .uninit (destination frames frame id s.abi.ret.layout)
      (LocalUnit.current frames frame machine) = .ok () (LocalUnit.current frames frame machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg outer
  have dictionaries := MetadataBinding.fields s metadata (by omega)
  have physical := ReturnMemory.write s metadata profile remaining capacity (LocalUnit.current frames frame machine)
    ⟨memory,s.abi.ret.layout⟩ rfl noMeta aligned
  rw [fields.projection] at physical ⊢
  rw [write_as_memory s.cfg.access s.cfg.allocation s.cfg.compiler () frames frame machine id slot memory
    s.abi.ret.layout atSlot live metadata.unitSized (dictionaries.debug.trans profile.debug)]
  exact physical

theorem unit (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory : MemPlace Provenance)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.indirect memory))
    (cache : slot.layout = some s.abi.ret.layout) (noClocks : frame.extra.dataRace = none)
    (noMeta : memory.metadata = .none) (aligned : memory.misaligned = none)
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (destination frames frame id s.abi.ret.layout) true (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg outer
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [fields.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [fields.padding]
    simp [CompilerCopy.hasPadding,metadata.unitBackend,pure,Except.pure]
  have written := write s metadata profile remaining capacity frames frame machine id slot memory atSlot live noMeta aligned
  have copied : copyRuntimePlaceNoValidate s.cfg.projection.place s.cfg.copy ()
      ⟨.immediate .uninit,s.abi.ret.layout⟩ (destination frames frame id s.abi.ret.layout) true
      (LocalUnit.current frames frame machine) = .ok () (LocalUnit.current frames frame machine) := by
    simp only [copyRuntimePlaceNoValidate,destination,compatible,placeLift_ok,padding,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,metadata.unitSized,
      Bool.not_true,Bool.false_and,Bool.false_or,Bool.false_eq_true,↓reduceIte,bne_self_eq_false]
    exact written
  have valid := validate_unit s metadata profile remaining capacity positive frames frame machine id slot memory
    atSlot live cache noClocks noGhost shallow
  unfold copyRuntimePlace
  simp only [bind,Bind.bind,EStateM.bind]
  rw [copied]
  simp only [destination,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  rw [fields.projection] at valid ⊢
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    ValidityMachine.enforceValidity,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    LocalUnit.current,shallow,pure,Pure.pure,EStateM.pure,
    show (ValidityMachine.ValidationMode.Shallow != .No) = true from by decide,↓reduceIte]
  simpa only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,destination,LocalUnit.current] using valid
end EmptyFunction.LocalIndirectReturnCopy
