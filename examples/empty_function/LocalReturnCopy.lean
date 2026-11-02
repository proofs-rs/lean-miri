import empty_function.LocalImmediate

/-! Actual unit return copy into an arbitrary cached immediate caller slot.
The caller's other locals, lower frames and complete machine are preserved. -/
namespace EmptyFunction.LocalReturnCopy
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

private theorem replace_same (frame : F) (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit)) :
    frame.setLocalOperand id (.immediate .uninit) = .ok frame := by
  have got := LocalImmediate.get_operand frame id slot atSlot live
  have bound := (Array.getElem?_eq_some_iff.mp atSlot).1
  have value := (Array.getElem?_eq_some_iff.mp atSlot).2
  unfold Frame.setLocalOperand
  rw [got]
  simp only [bind,Except.bind,pure,Except.pure]
  unfold Frame.replaceLocalValue
  simp only [Frame.getLocal, bound, ↓reduceDIte]
  have same : {slot with value := .live (.immediate .uninit)} = slot := by rw [←live]
  simp only [value,pure,Except.pure,bind,Except.bind,same]
  rw [←value]
  simp only [Array.set_getElem_self]

private theorem write_optimized (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (id : MIR.LocalId)
    (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
    (sized : layout.layout.isSized=true) (noClocks : frame.extra.dataRace=none)
    (validation : MachineHooks.M K U Bool)
    (validationPure : ∀ state, ∃ flag, validation state=.ok flag state) :
    placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
      validation MachineHooks.afterLocalWrite (fun _ _ => pure ()) id layout .uninit
      (LocalUnit.current frames frame machine) = .ok () (LocalUnit.current frames frame machine) := by
  obtain ⟨flag,flagEq⟩ := validationPure (LocalUnit.current frames frame machine)
  have got := LocalImmediate.get_operand frame id slot atSlot live
  have put := replace_same frame id slot atSlot live
  unfold placeWriteLocalImmediate
  simp [sized, MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,got,put,
    stackLift_ok,MachineHooks.setCurrentFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,set,EStateM.set]
  change ((do unless ← validation do MachineHooks.afterLocalWrite id false;pure ()) : MachineHooks.M K U Unit)
    (LocalUnit.current frames frame machine) = _
  simp only [bind,EStateM.bind,flagEq,pure,EStateM.pure]
  cases flag <;> simp [MachineHooks.afterLocalWrite,MachineHooks.currentFrame,LocalUnit.current,
    Stack.currentFrame?,noClocks,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
    pure,EStateM.pure]

 theorem write_cached [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
    (sized : layout.layout.isSized=true) (debugOff : compiler.debugAssertions=false)
    (abiOff : compiler.debugAbiCheck=fun _ _ => pure ()) (noClocks : frame.extra.dataRace=none) :
    writePlaceImmediateNoValidate (ValidityMachine.placeHooks access allocation compiler) choice .uninit
      (destination frames frame id layout) (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame machine) := by
  have got := LocalImmediate.get_operand frame id slot atSlot live
  have write := write_optimized frames frame machine id slot layout atSlot live sized noClocks
    ValidityMachine.validationInProgress (fun state => ⟨_,rfl⟩)
  with_unfolding_all
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    simp [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
      requireCurrent_eq,checkLocalIdentity_debugOff,destination,sized,debugOff,abiOff,got,
      MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,Stack.frameIndex,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,Except.pure,Except.bind,Except.mapError]
    exact write

 theorem projected_read (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (unit : LocalLayout)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
    (cache : slot.layout=some unit)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    (EvalConfigurationCore.make p image bytes options leaves () (remaining+1)).map
      (fun config => config.validity.toOp () (destination frames frame id unit)
        (LocalUnit.current frames frame machine)) =
      .ok (.ok ⟨.immediate .uninit,unit⟩
        (LocalUnit.current frames frame machine)) := by
  have got := LocalImmediate.get_local frame id slot atSlot
  have operand := LocalImmediate.get_operand frame id slot atSlot live
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
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
    (cache : slot.layout=some unit)
    (debugOff : options.place.debugAssertions = false) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    config.validity.toOp () (destination frames frame id unit)
      (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate .uninit,unit⟩
        (LocalUnit.current frames frame machine) := by
  have law := projected_read p image bytes options leaves remaining contract frames frame machine unit id slot atSlot live cache
    debugOff sized noClocks
  rw [built] at law
  exact Except.ok.inj law

 theorem canonical_unit (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : CanonicalDictionaries.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (layout : LocalLayout)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
    (cache : slot.layout=some layout)
    (fuel : Nat) (debugOff : options.place.debugAssertions = false)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (kind : CompilerFactAdapters.validityKind p.lifecycle.calls.symbols.facts layout.ty =
      .ok (.aggregate false false false))
    (node : TypeNode) (nodeFound : p.lifecycle.calls.symbols.facts.context.runtime.node layout.ty = .ok node)
    (inhabited : CompilerFacts.boolean p.lifecycle.calls.symbols.facts.context layout.ty "opsem_inhabited" = .ok true)
    (fields : layout.layout.fields = .Arbitrary #[] #[])
    (variants : layout.layout.variants = .Single 0) :
    ValidityVisitor.validatePlace config.validity () (fuel+1) (destination frames frame id layout) false true
      (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame machine) := by
  have methods := BodyDictionaries.fields_of_make p image bytes options leaves remaining contract config built
  have classifyEq : config.validity.classify =
      (CompilerFactAdapters.validityHooks p.lifecycle.calls.symbols.facts config.validity).classify :=
    congrArg BodyDictionaries.Queries.classify methods
  have nameEq : config.validity.typeName =
      (CompilerFactAdapters.validityHooks p.lifecycle.calls.symbols.facts config.validity).typeName :=
    congrArg BodyDictionaries.Queries.typeName methods
  have inhabitedEq : config.validity.opsemInhabited =
      (CompilerFactAdapters.validityHooks p.lifecycle.calls.symbols.facts config.validity).opsemInhabited :=
    congrArg BodyDictionaries.Queries.inhabited methods
  have ghostEq : @config.validity.withGhostValidation =
      @ValidityMachine.withGhostValidation MiriMemoryKind
        (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost) :=
    congrArg (fun q => @q.ghost) methods
  have debugEq : config.validity.debugAssertions = options.place.debugAssertions :=
    congrArg BodyDictionaries.Queries.debug methods
  apply BodyValidation.shallow_fieldless config.validity () fuel _ _ node.display noGhost ghostEq
  · rw [nameEq]
    exact BodyQueries.adapter_name _ _ () _ _ node nodeFound
  · have read := read_of_make p image bytes options leaves remaining contract config built
      frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
      layout id slot atSlot live cache debugOff sized noClocks
    simpa only [BodyValidation.active, LocalUnit.current, destination] using read
  · rw [classifyEq]
    exact BodyQueries.adapter_classifier _ _ () _ _ kind
  · rw [inhabitedEq]
    exact BodyQueries.adapter_inhabited _ _ () _ _ inhabited
  · exact fields
  · exact variants
  · exact debugEq.trans debugOff

theorem copy_no_validate [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (copy : PlaceCopyHooks Provenance (ValidityMachine.State K U) C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
    (unit : LocalLayout) (sized : unit.layout.isSized = true)
    (debugOff : compiler.debugAssertions = false)
    (abiOff : compiler.debugAbiCheck = fun _ _ => pure ())
    (compatible : copy.compatible unit unit = .ok true)
    (padding : copy.hasPadding unit = .ok true)
    (noClocks : frame.extra.dataRace = none) :
    copyRuntimePlaceNoValidate (ValidityMachine.placeHooks access allocation compiler) copy choice
      ⟨.immediate .uninit,unit⟩ (destination frames frame id unit) false
      (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame machine) := by
  simp only [copyRuntimePlaceNoValidate, destination, compatible, placeLift_ok,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Bool.not_true,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, padding, Bool.not_false,
    sized, Bool.false_or, bne_self_eq_false]
  exact write_cached access allocation compiler choice frames frame machine id slot unit atSlot live sized
    debugOff abiOff noClocks

 theorem validate_unit (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
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
  have valid := canonical_unit s.prepared.compiler s.prepared.image s.bytes s.options
    leaves remaining metadata.construction inner innerBuilt frames frame machine s.abi.ret.layout id slot atSlot live cache
    (s.options.limits.validation-1) profile.debug metadata.unitSized noClocks noGhost
    metadata.unitKind node nodeFound metadata.unitInhabited metadata.unitFields metadata.unitVariants
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

 theorem unit (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
    (cache : slot.layout=some s.abi.ret.layout)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (destination frames frame id s.abi.ret.layout) false
      (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame machine) := by
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
  have written := copy_no_validate s.cfg.access s.cfg.allocation s.cfg.compiler s.cfg.copy ()
    frames frame machine id slot atSlot live s.abi.ret.layout metadata.unitSized (dictionaries.debug.trans profile.debug)
    (dictionaries.debugAbi profile.debug) compatible padding noClocks
  have valid := validate_unit s metadata profile remaining capacity positive frames frame machine id slot atSlot live cache noClocks noGhost shallow
  rw [source.projection] at valid ⊢
  unfold copyRuntimePlace
  simp only [bind, Bind.bind, EStateM.bind, written]
  simp only [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
    ValidityMachine.enforceValidity, LocalUnit.current, destination,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    shallow, show (ValidityMachine.ValidationMode.Shallow != .No) = true from by decide,
    pure, Pure.pure, EStateM.pure, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simpa only [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
    LocalUnit.current, destination] using valid

 theorem unit_allow (s : Static) (metadata : Metadata s) (profile : Profile s)
    (allowTransmute : Bool) (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]?=some slot) (live : slot.value=.live (.immediate .uninit))
    (cache : slot.layout=some s.abi.ret.layout)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (destination frames frame id s.abi.ret.layout) allowTransmute
      (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame machine) := by
  have base := unit s metadata profile remaining capacity positive frames frame machine id slot atSlot live cache noClocks noGhost shallow
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have source := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [source.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have identical : copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (destination frames frame id s.abi.ret.layout) allowTransmute =
      copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
        (destination frames frame id s.abi.ret.layout) false := by
    funext currentState
    unfold copyRuntimePlace copyRuntimePlaceNoValidate
    simp only [destination,compatible,placeLift_ok,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      Bool.not_true,Bool.false_and,Bool.false_eq_true,↓reduceIte]
  rw [identical]
  exact base

end EmptyFunction.LocalReturnCopy

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.LocalReturnCopy.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved local-return-copy axiom: {name}: {dependency}"
  logInfo m!"Audited {count} local-return-copy declarations"
