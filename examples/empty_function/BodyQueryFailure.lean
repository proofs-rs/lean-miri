import empty_function.BodyFailures
namespace EmptyFunction.BodyQueryFailure
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def queryError (message : String) : StepError := .unsupported s!"constant compiler query: {message}"

 theorem constant_error (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+1)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (message : String)
    (query : CompilerConstantQueries.lookup s.prepared.compiler.constants
      ⟨s.loaded.identity.index,metadata.literalId⟩ = .error message) :
    s.cfg.operands.constant () metadata.literalId
      metadata.literal (some s.abi.ret.layout)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .error (queryError message)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      (remaining+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have source := BodyConstantDictionary.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves remaining metadata.construction s.cfg outer
  obtain ⟨functions, arithmetic, external, callback⟩ := source.constants
  let site : CompilerConstantQueries.Site := ⟨s.loaded.identity.index,metadata.literalId⟩
  have literal := Literal.eval_query_error s.prepared.compiler.constants site functions arithmetic external
    MemoryErrors.constant metadata.literal s.abi.ret.layout
    (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) frames machine
    (by simp [BodyStep.withUnit, LocalUnit.withUnit, bodyIdentity, site]) message query
  rw [callback profile.debug]
  simp only [CompilerOperandSites.current, MachineHooks.currentFrame,
    BodyStep.current, LocalUnit.current, Stack.currentFrame?, Array.back?_push,
    BodyStep.withUnit, LocalUnit.withUnit, location, bodyIdentity,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]
  simpa [site, BodyStep.current, LocalUnit.current, BodyStep.withUnit, LocalUnit.withUnit,
    Array.map_push, bodyIdentity, location, queryError, MemoryErrors.constant] using literal

private theorem bound_copy_eq (s : Static) (layout : LocalLayout)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (compatible : s.cfg.copy.compatible layout layout = .ok true)
    (padding : s.cfg.copy.hasPadding layout = .ok true)
    (sized : layout.layout.isSized = true) :
    (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits).copyOp ()
      ⟨.immediate .uninit,layout⟩ (BodyStep.destination frames frame layout) =
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,layout⟩
      (BodyStep.destination frames frame layout) false := by
  funext state
  simp [ExecutionMachine.rvalueHooks, ExecutionMachine.withValidation,
    ExecutionMachine.projectionHooks, TypedMachineBindings.bindValidation,
    copyRuntimePlace, copyRuntimePlaceNoValidate, BodyStep.destination,
    compatible, padding, sized, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]


 theorem rvalue (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+1)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : Meaning.FrameMatches frame s.loaded)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (message : String)
    (query : CompilerConstantQueries.lookup s.prepared.compiler.constants
      ⟨s.loaded.identity.index,metadata.literalId⟩ = .error message) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits)
      () ((.Use metadata.entry.operand .Yes) : RvalueNode) metadata.entry.destination
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      .error (queryError message) (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      (remaining+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have source := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves remaining metadata.construction s.cfg outer
  have dictionaries := CanonicalDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves remaining metadata.construction s.cfg outer
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [source.compatible]
    simp [CompilerCovariance.compatible, CompilerCovariance.relation, CompilerCovariance.relationWithIndex,
      profile.debug, Except.mapError, bind, Except.bind, pure, Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [source.padding]
    simp [CompilerCopy.hasPadding, metadata.unitBackend, pure, Except.pure]
  have check : s.cfg.compiler.checkPlaceType = fun _ _ _ => pure () := by
    rw [source.checkPlace]
    funext choice place value state
    simp [CompilerPlaceTypes.dynamicPlace, profile.debug,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  have computed : s.cfg.compiler.layout () 0
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      .ok s.abi.ret.layout (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) := by
    rw [dictionaries.layout]
    apply BodyQueries.local_layout s.prepared.compiler s.abi.ret.layout frames frame machine
    · apply metadata.normalizedLocal
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit] using bodyIdentity
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit, Meaning.FrameMatches] using body
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit] using function
    · exact metadata.unitLookup
  let h := ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits
  let hc := ExecutionMachine.withValidation (ExecutionMachine.withValidation s.cfg s.limits) s.limits
  obtain ⟨placeNode, placeAt, localId, projections⟩ := Meaning.place_empty
    s.loaded.tables metadata.entry.destination 0 metadata.entry_observations.1
  have destination : h.evalPlace () metadata.entry.destination true
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      .ok (BodyStep.destination frames frame s.abi.ret.layout)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
    change ExecutionMachine.evalPlace hc () metadata.entry.destination true _ = _
    rw [BodyStep.evalPlace_current]
    have selected : (BodyStep.withUnit frame .uninit none).mirTables.places.lookup
        metadata.entry.destination.index = .ok placeNode := by
      simpa only [BodyStep.withUnit, LocalUnit.withUnit, body.2.2] using placeAt
    have projectionAt : (BodyStep.withUnit frame .uninit none).mirTables.projectionLists.lookup
        placeNode.projection.index = .ok #[] := by
      simpa only [BodyStep.withUnit, LocalUnit.withUnit, body.2.2] using projections
    rw [PlaceTable.eval_empty _ _ _ () _ placeNode selected projectionAt
      (by intro place; simp [hc, ExecutionMachine.operandHooks, ExecutionMachine.withValidation,
        TypedMachineBindings.bindValidation, dictionaries.debug, profile.debug])
      (by intro place; simp only [ExecutionMachine.projectionHooks, hc,
        ExecutionMachine.withValidation, source.projection, ValidityMachine.placeHooks,
        PlaceMachine.placeHooks, ValidityMachine.compilerPolicy, check])]
    rw [localId]
    apply BodyStep.evaluate_zero s.cfg.access s.cfg.allocation s.cfg.compiler
      (ExecutionMachine.projectionHooks hc) () frames frame machine
      s.abi.ret.layout metadata.unitSized
    · exact source.projection
    · exact check
    · exact computed
  obtain ⟨constantNode, constantAt, constantValue⟩ := Meaning.constant_node s.loaded.tables
    metadata.entry.constant metadata.literal metadata.entry_observations.2.2
  have literal : h.evalOperandAt () (OperandPath.rvalue "operand") metadata.entry.operand
      (some s.abi.ret.layout)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .error (queryError message)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
    change OperandTable.evalOperandAt (ExecutionMachine.operandHooks hc) () _ _ _ _ = _
    rw [BodyStep.evalOperandAt_current]
    rw [OperandTable.eval_constant _ _ _ () _ metadata.entry.constant constantNode _ _
      (by simpa only [BodyStep.withUnit,LocalUnit.withUnit,body.2.2] using metadata.entry_references.operand)
      (by simpa only [BodyStep.withUnit,LocalUnit.withUnit,body.2.2] using constantAt)]
    change s.cfg.operands.constant () metadata.entry.constant constantNode.operand _ _ = _
    rw [metadata.entry_constant, constantValue]
    exact constant_error s metadata profile remaining capacity frames frame machine bodyIdentity function location message query
  change evalRvalueIntoPlace h () _ _ _ = _
  unfold evalRvalueIntoPlace
  simp only [bind, Bind.bind, EStateM.bind, destination]
  change (h.evalOperandAt () (OperandPath.rvalue "operand") metadata.entry.operand
      (some s.abi.ret.layout) >>= fun op => MachineHooks.withRetagMode .Default
        (h.copyOp () op (BodyStep.destination frames frame s.abi.ret.layout))) _ = _
  simp only [bind, Bind.bind, EStateM.bind, literal]

 theorem statement (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+1)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : Meaning.FrameMatches frame s.loaded)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (message : String)
    (query : CompilerConstantQueries.lookup s.prepared.compiler.constants
      ⟨s.loaded.identity.index,metadata.literalId⟩ = .error message) :
    (ExecutionMachine.stepHooks s.cfg s.limits).assign () metadata.entry.destination
      metadata.entry.rvalue
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,.error (queryError message)) := by
  have assigned := rvalue s metadata profile remaining capacity frames frame machine
    bodyIdentity body function location noClocks noGhost shallow message query
  change MachineHooks.run (do
    let frame ← MachineHooks.currentFrame
    RvalueTable.eval frame.mirTables
      (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits)
      () metadata.entry.rvalue metadata.entry.destination) _ = _
  simp only [MachineHooks.run, Call.run, MachineHooks.currentFrame, BodyStep.current, LocalUnit.current, Stack.currentFrame?,
    Array.back?_push, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [RvalueTable.eval_known _ _ () _ _ ((.Use metadata.entry.operand .Yes) : RvalueNode)
    (by simpa only [BodyStep.withUnit,LocalUnit.withUnit,body.2.2,
      metadata.entry_observations.2.1] using metadata.entry_references.rvalue)]
  simp only [BodyStep.current, LocalUnit.current] at assigned
  rw [assigned]


 theorem step (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+1)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : Meaning.FrameMatches frame s.loaded)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (message : String)
    (query : CompilerConstantQueries.lookup s.prepared.compiler.constants
      ⟨s.loaded.identity.index,metadata.literalId⟩ = .error message) :
    ExecutionMachine.step s.cfg s.limits ()
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,.error (queryError message)) := by
  have assigned := statement s metadata profile remaining capacity frames frame machine
    bodyIdentity body function location noClocks noGhost shallow message query
  have evaluated : Step.evalStatement (ExecutionMachine.stepHooks s.cfg s.limits) () metadata.entry.statement
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,.error (queryError message)) := by
    simpa only [Step.evalStatement, metadata.entry_references.kind] using assigned
  have beforeLoc : (BodyStep.withUnit frame .uninit none).location = .mir ⟨0,0⟩ := location
  have beforeFound : (BodyStep.withUnit frame .uninit none).body.basicBlocks[0]? =
      some metadata.entry.blockId := by
    simpa only [BodyStep.withUnit,LocalUnit.withUnit,body.1] using metadata.entry_references.block
  have blockAt : (BodyStep.withUnit frame .uninit none).mirTables.blocks.lookup
      metadata.entry.blockId.index = .ok metadata.entry.block := by
    simpa only [BodyStep.withUnit,LocalUnit.withUnit,body.2.2] using metadata.entry_references.blockNode
  have statementAt : (BodyStep.withUnit frame .uninit none).mirTables.statements.lookup
      metadata.entry.statementId.index = .ok metadata.entry.statement := by
    simpa only [BodyStep.withUnit,LocalUnit.withUnit,body.2.2] using metadata.entry_references.statement
  change Step.step (ExecutionMachine.stepHooks s.cfg s.limits) () _ = _
  unfold Step.step
  simp only [Stack.currentFrame?,BodyStep.current,LocalUnit.current,Array.back?_push,
    beforeLoc,beforeFound,blockAt,metadata.entry_references.first,statementAt]
  simp only [BodyStep.current,LocalUnit.current] at evaluated
  erw [evaluated]
  rfl


end EmptyFunction.BodyQueryFailure
