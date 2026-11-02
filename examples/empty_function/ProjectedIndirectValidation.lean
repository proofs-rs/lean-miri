import empty_function.LocalIndirectReturnCopy
import empty_function.ProjectedIndirectPreflight
namespace EmptyFunction.ProjectedIndirectValidation
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
 theorem projected_read (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (base unit : LocalLayout) (amount : Size)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory shifted : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (cache : slot.layout=some base)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (offsetQuery : EvalProjectionMachine.memoryOffset (CanonicalDictionaries.pointerSource p image leaves).pointers
      (LocalUnit.current frames frame machine) memory amount .inbounds .none = .ok shifted) :
    (EvalConfigurationCore.make p image bytes options leaves () (remaining+1)).map
      (fun config => config.validity.toOp () (⟨.local frames.size id (some amount) frame.localsIdentity,unit⟩ : RuntimePlace Provenance)
        (LocalUnit.current frames frame machine)) =
      .ok (.ok ⟨.indirect shifted,unit⟩
        (LocalUnit.current frames frame machine)) := by
  have got := LocalImmediate.get_local frame id slot atSlot
  have operand := LocalIndirectRead.get_operand frame id slot atSlot memory live
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
      got,operand,cache,sized, debugOff, noClocks, flag,
      EvalProjectionMachine.context,OpTy.offset,OpTy.offsetWithMeta, offsetQuery,
      MachineHooks.afterLocalRead, MachineHooks.currentFrame, BodyStep.current, LocalUnit.current,
      Stack.frameIndex,
      Stack.currentFrame?, LocalState.access, Except.mapError, Except.pure, Except.bind,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]

  all_goals
    simp only [CanonicalDictionaries.pointerSource,LocalUnit.current] at offsetQuery
    rw [offsetQuery]
    rfl
 theorem read_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : WholeCall.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (base unit : LocalLayout) (amount : Size)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory shifted : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (cache : slot.layout=some base)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (offsetQuery : EvalProjectionMachine.memoryOffset (CanonicalDictionaries.pointerSource p image leaves).pointers
      (LocalUnit.current frames frame machine) memory amount .inbounds .none = .ok shifted) :
    config.validity.toOp ()
      (⟨.local frames.size id (some amount) frame.localsIdentity,unit⟩ : RuntimePlace Provenance)
      (LocalUnit.current frames frame machine) =
      .ok ⟨.indirect shifted,unit⟩ (LocalUnit.current frames frame machine) := by
  have law := projected_read p image bytes options leaves remaining contract frames frame machine base unit amount
    id slot memory shifted atSlot live cache debugOff sized noClocks offsetQuery
  rw [built] at law
  exact Except.ok.inj law

 theorem projected_force (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout) (amount : Size)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory shifted : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (offsetQuery : EvalProjectionMachine.memoryOffset (CanonicalDictionaries.pointerSource p image leaves).pointers
      (LocalUnit.current frames frame machine) memory amount .wrapping .none = .ok shifted) :
    (EvalConfigurationCore.make p image bytes options leaves () (remaining+1)).map
      (fun config => forceAllocation config.validity.projection.place () (⟨.local frames.size id (some amount) frame.localsIdentity,unit⟩ : RuntimePlace Provenance)
        (LocalUnit.current frames frame machine)) =
      .ok (.ok (⟨shifted,unit⟩ : MPlaceTy Provenance)
        (LocalUnit.current frames frame machine)) := by
  have got := LocalImmediate.get_local frame id slot atSlot
  have operand := LocalIndirectRead.get_operand frame id slot atSlot memory live
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
      PointerPlaceMachine.bindCompiler, forceAllocation, requireCurrent_eq, checkLocalIdentity_debugOff,
      ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
      PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
      EvalPlaceConstruction.compiler, ValidityMachine.validationInProgress,
      got,operand,sized, debugOff, noClocks, flag, offsetQuery,
      MachineHooks.afterLocalRead, MachineHooks.currentFrame, BodyStep.current, LocalUnit.current,
      Stack.frameIndex,
      Stack.currentFrame?, LocalState.access, Except.mapError, Except.pure, Except.bind,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]

  all_goals
    simp only [CanonicalDictionaries.pointerSource,LocalUnit.current] at offsetQuery
    rw [offsetQuery]
    rfl

 theorem force_of_make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : WholeCall.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout) (amount : Size)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (memory shifted : MemPlace Provenance)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.indirect memory))
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (offsetQuery : EvalProjectionMachine.memoryOffset (CanonicalDictionaries.pointerSource p image leaves).pointers
      (LocalUnit.current frames frame machine) memory amount .wrapping .none = .ok shifted) :
    forceAllocation config.validity.projection.place ()
      (⟨.local frames.size id (some amount) frame.localsIdentity,unit⟩ : RuntimePlace Provenance)
      (LocalUnit.current frames frame machine) =
      .ok (⟨shifted,unit⟩ : MPlaceTy Provenance) (LocalUnit.current frames frame machine) := by
  have law := projected_force p image bytes options leaves remaining contract frames frame machine unit amount
    id slot memory shifted atSlot live debugOff sized noClocks offsetQuery
  rw [built] at law
  exact Except.ok.inj law

theorem canonical_unit (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (config : WholeCall.Config)
    (built : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options
      (Configuration.leaves s.prepared s.options.place.debugAssertions) () (remaining+1) = .ok config)
    (state : WholeCall.State) (reference : RuntimePlaceRef Provenance) (place : MPlaceTy Provenance)
    (readQuery : config.validity.toOp () ⟨reference,place.layout⟩ (BodyValidation.active state) =
      .ok ⟨.indirect place.mplace,place.layout⟩ (BodyValidation.active state))
    (forceQuery : forceAllocation config.validity.projection.place () ⟨reference,place.layout⟩ (BodyValidation.active state) =
      .ok place (BodyValidation.active state))
    (layout : place.layout = s.abi.ret.layout) (noGhost : state.machine.user.payload.ghost = false)
    (fuel : Nat) :
    ValidityVisitor.validatePlace config.validity () (fuel+1) (⟨reference,place.layout⟩ : RuntimePlace Provenance) false true state =
      .ok () state := by
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
  apply LocalIndirectReturnCopy.shallow_indirect config.validity fuel state reference place node.display noGhost ghostEq
  · rw [nameEq,layout]
    exact BodyQueries.adapter_name _ _ () _ _ node nodeFound
  · exact readQuery
  · exact forceQuery
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

 theorem validate_from_queries (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (state : WholeCall.State) (reference : RuntimePlaceRef Provenance) (memory : MemPlace Provenance)
    (inner : WholeCall.Config)
    (innerBuilt : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options
      (Configuration.leaves s.prepared s.options.place.debugAssertions) () (remaining+1) = .ok inner)
    (readQuery : inner.validity.toOp () ⟨reference,s.abi.ret.layout⟩ (BodyValidation.active state) =
      .ok ⟨.indirect memory,s.abi.ret.layout⟩ (BodyValidation.active state))
    (forceQuery : forceAllocation inner.validity.projection.place () ⟨reference,s.abi.ret.layout⟩ (BodyValidation.active state) =
      .ok ⟨memory,s.abi.ret.layout⟩ (BodyValidation.active state))
    (noGhost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow) :
    s.cfg.projection.place.validate () (⟨reference,s.abi.ret.layout⟩ : RuntimePlace Provenance)
      state =
      .ok () state := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  obtain ⟨node, nodeFound⟩ := metadata.unitNode
  have budget : s.options.limits.validation = (s.options.limits.validation-1)+1 := by omega
  have valid := canonical_unit s metadata profile remaining inner innerBuilt state reference ⟨memory,s.abi.ret.layout⟩
    readQuery forceQuery rfl noGhost (s.options.limits.validation-1)
  rw [fields.projection]
  simp only [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks]
  rw [fields.validate]
  simp only [BodyPlaceDictionaries.validation, innerBuilt]
  unfold ValidityMachine.validateRuntime
  simp only [leaves,innerBuilt]
  simp only [ValidityMachine.enforceValidityRecursively,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    shallow, show (ValidityMachine.ValidationMode.Shallow == .Deep) = false from by decide, beq_self_eq_true, pure, Pure.pure, EStateM.pure]
  rw [budget]
  exact valid


theorem validate_projected (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (base : LocalLayout)
    (memory shifted : MemPlace Provenance) (amount : Size)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.indirect memory))
    (cache : slot.layout = some base) (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (inbounds : EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
      (BodyValidation.active (LocalUnit.current frames frame machine)) memory amount .inbounds .none = .ok shifted)
    (wrapping : EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
      (BodyValidation.active (LocalUnit.current frames frame machine)) memory amount .wrapping .none = .ok shifted) :
    s.cfg.projection.place.validate () ⟨.local frames.size id (some amount) frame.localsIdentity,s.abi.ret.layout⟩
      (LocalUnit.current frames frame machine) = .ok () (LocalUnit.current frames frame machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  obtain ⟨inner,built,_⟩ := CanonicalDictionaries.make_fields s.prepared.compiler s.prepared.image
    s.bytes s.options leaves remaining metadata.construction
  let active := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  have read := read_of_make s.prepared.compiler s.prepared.image s.bytes s.options leaves remaining metadata.construction
    inner built frames frame active base s.abi.ret.layout amount id slot memory shifted atSlot live cache profile.debug
    metadata.unitSized noClocks inbounds
  have forced := force_of_make s.prepared.compiler s.prepared.image s.bytes s.options leaves remaining metadata.construction
    inner built frames frame active s.abi.ret.layout amount id slot memory shifted atSlot live profile.debug
    metadata.unitSized noClocks wrapping
  exact validate_from_queries s metadata profile remaining capacity positive (LocalUnit.current frames frame machine)
    (.local frames.size id (some amount) frame.localsIdentity) shifted inner built read forced noGhost shallow

end EmptyFunction.ProjectedIndirectValidation
