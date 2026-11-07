import empty_function.BodyAssignment
import empty_function.ResourceFailures

namespace EmptyFunction.BodyFailures
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- At construction capacity one, the actual nested validation factory reports
resource exhaustion before accessing any place. -/
theorem validate_capacity_one (s : Static) (metadata : Metadata s)
    (capacity : s.capacity = 1) (choice : Unit) (place : RuntimePlace Provenance) (state : State) :
    s.cfg.projection.place.validate choice place state =
      .error (.resourceExhaustion "execution callback construction capacity") state := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      (0+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves 0 metadata.construction s.cfg outer
  rw [fields.projection]
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks]
  rw [fields.validate]
  have zero : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves () 0 =
      .error (.resourceExhaustion "execution callback construction capacity") := by
    rw [EvalConfigurationCore.make_eq_context,EvalConfigurationCore.makeWithForeignContext]
    rfl
  simp only [BodyPlaceDictionaries.validation,zero]
  rfl

 theorem validate_visit_zero
    (h : BodyDictionaries.Visitor) (state : State) (place : RuntimePlace Provenance) (name : String)
    (noGhost : state.machine.user.payload.ghost = false)
    (ghost : @h.withGhostValidation = @ValidityMachine.withGhostValidation MiriMemoryKind
      (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost))
    (nameQuery : h.typeName () place.layout.ty state = .ok name state)
    (readQuery : h.toOp () place (BodyValidation.active state) =
      .ok ⟨.immediate .uninit,place.layout⟩ (BodyValidation.active state)) :
    ValidityVisitor.validatePlace h () 0 place false true state =
      .error (.resourceExhaustion "validity traversal fuel") state := by
  unfold ValidityVisitor.validatePlace
  simp only [ghost,bind,Bind.bind,EStateM.bind,nameQuery,
    ValidityMachine.withGhostValidation,noGhost,Bool.false_eq_true,↓reduceIte]
  simp only [BodyValidation.active] at readQuery
  simp only [readQuery,pure,Pure.pure,EStateM.pure,ValidityVisitor.visit,
    throw,throwThe,MonadExceptOf.throw,EStateM.throw,bind,Bind.bind,EStateM.bind]
  cases state
  simp_all
  rename_i stack machine
  rw [←noGhost]

 theorem canonical_validation_zero (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : CanonicalDictionaries.Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (layout : LocalLayout)
    (debugOff : options.place.debugAssertions = false)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (node : TypeNode) (nodeFound : p.lifecycle.calls.symbols.facts.context.runtime.node layout.ty = .ok node) :
    ValidityVisitor.validatePlace config.validity () 0 (BodyStep.destination frames frame layout) false true
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some layout)) machine) =
      .error (.resourceExhaustion "validity traversal fuel")
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some layout)) machine) := by
  have methods := BodyDictionaries.fields_of_make p image bytes options leaves remaining contract config built
  have nameEq : config.validity.typeName =
      (CompilerFactAdapters.validityHooks p.lifecycle.calls.symbols.facts config.validity).typeName :=
    congrArg BodyDictionaries.Queries.typeName methods
  have ghostEq : @config.validity.withGhostValidation =
      @ValidityMachine.withGhostValidation MiriMemoryKind
        (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost) :=
    congrArg (fun q => @q.ghost) methods
  apply validate_visit_zero config.validity _ _ node.display noGhost ghostEq
  · rw [nameEq]
    exact BodyQueries.adapter_name _ _ () _ _ node nodeFound
  · have read := BodyDictionaries.read_of_make p image bytes options leaves remaining contract config built
      frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
      layout debugOff sized noClocks
    simpa only [BodyValidation.active,BodyStep.current,LocalUnit.current,BodyStep.destination] using read

 theorem validate_budget_zero (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (zeroBudget : s.options.limits.validation = 0)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    s.cfg.projection.place.validate () (BodyStep.destination frames frame s.abi.ret.layout)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .error (.resourceExhaustion "validity traversal fuel")
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  obtain ⟨inner,innerBuilt,_⟩ := CanonicalDictionaries.make_fields s.prepared.compiler s.prepared.image
    s.bytes s.options leaves remaining metadata.construction
  obtain ⟨node,nodeFound⟩ := metadata.unitNode
  have valid := canonical_validation_zero s.prepared.compiler s.prepared.image s.bytes s.options
    leaves remaining metadata.construction inner innerBuilt frames frame machine s.abi.ret.layout
    profile.debug metadata.unitSized noClocks noGhost node nodeFound
  rw [fields.projection]
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks]
  rw [fields.validate]
  simp only [BodyPlaceDictionaries.validation,innerBuilt]
  unfold ValidityMachine.validateRuntime
  simp only [ValidityMachine.enforceValidityRecursively,BodyStep.current,LocalUnit.current,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    shallow,show (ValidityMachine.ValidationMode.Shallow == .Deep) = false from by decide,
    beq_self_eq_true,pure,Pure.pure,EStateM.pure,zeroBudget]
  simpa only [BodyStep.current,LocalUnit.current] using valid


 theorem constant_positive (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+1)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩) :
    s.cfg.operands.constant () metadata.literalId
      metadata.literal (some s.abi.ret.layout)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .ok ⟨.immediate .uninit,s.abi.ret.layout⟩
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      (remaining+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have source := BodyConstantDictionary.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves remaining metadata.construction s.cfg outer
  obtain ⟨functions, arithmetic, external, callback⟩ := source.constants
  let site : CompilerConstantQueries.Site := ⟨s.loaded.identity.index,metadata.literalId⟩
  have literal := Literal.eval_unit s.prepared.compiler.constants site functions arithmetic external
    MemoryErrors.constant metadata.literal s.abi.ret.layout
    (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) frames machine
    metadata.literalEvidence
    (by simp [BodyStep.withUnit, LocalUnit.withUnit, bodyIdentity, site])
    metadata.literalQuery metadata.literalShape
    (by simpa only [BodyStep.withUnit, LocalUnit.withUnit, function, site] using metadata.literalNormalization)
  rw [callback profile.debug]
  simp only [CompilerOperandSites.current, MachineHooks.currentFrame,
    BodyStep.current, LocalUnit.current, Stack.currentFrame?, Array.back?_push,
    BodyStep.withUnit, LocalUnit.withUnit, location, bodyIdentity,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]
  simpa [site, BodyStep.current, LocalUnit.current, BodyStep.withUnit, LocalUnit.withUnit,
    Array.map_push, bodyIdentity, location] using literal

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

 theorem copy_error (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+1)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (error : StepError)
    (failed : s.cfg.projection.place.validate () (BodyStep.destination frames frame s.abi.ret.layout)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .error error (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine)) :
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (BodyStep.destination frames frame s.abi.ret.layout) false
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .error error (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
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
  have written := BodyStep.copy_zero_no_validate s.cfg.access s.cfg.allocation s.cfg.compiler s.cfg.copy ()
    frames frame machine s.abi.ret.layout metadata.unitSized (dictionaries.debug.trans profile.debug)
    (dictionaries.debugAbi profile.debug) compatible padding noClocks
  have valid := failed
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

 theorem scoped_copy_error (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+1)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (error : StepError)
    (failed : ∀ machine : MachineHooks.MachineState MiriMemoryKind RootUser,
      machine.user.payload.ghost = false → machine.user.payload.validation = .Shallow →
      s.cfg.projection.place.validate () (BodyStep.destination frames frame s.abi.ret.layout)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
        .error error (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine)) :
    MachineHooks.withRetagMode .Default
      (copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
        (BodyStep.destination frames frame s.abi.ret.layout) false)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .error error (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  cases trackerEq : machine.borrowTracker with
  | none =>
    simpa only [MachineHooks.withRetagMode, BodyStep.current, LocalUnit.current, trackerEq] using
      copy_error s metadata profile remaining capacity frames frame machine noClocks noGhost shallow error (failed machine noGhost shallow)
  | some tracker =>
    let entered := {machine with borrowTracker := some {tracker with retagMode := .Default}}
    have copied := copy_error s metadata profile remaining capacity frames frame entered
      noClocks noGhost shallow error (failed entered noGhost shallow)
    simp only [BodyStep.current, LocalUnit.current, entered] at copied
    unfold MachineHooks.withRetagMode
    simp only [BodyStep.current, LocalUnit.current, trackerEq]
    rw [copied]
    simp only []
    have restored : {machine with borrowTracker := some tracker} = machine := by
      rw [←trackerEq]
    simpa only [restored]

 theorem rvalue_error (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
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
    (error : StepError)
    (failed : ∀ machine : MachineHooks.MachineState MiriMemoryKind RootUser,
      machine.user.payload.ghost = false → machine.user.payload.validation = .Shallow →
      s.cfg.projection.place.validate () (BodyStep.destination frames frame s.abi.ret.layout)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
        .error error (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine)) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits)
      () ((.Use metadata.entry.operand .Yes) : RvalueNode) metadata.entry.destination
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      .error error (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
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
      .ok ⟨.immediate .uninit,s.abi.ret.layout⟩
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
    change OperandTable.evalOperandAt (ExecutionMachine.operandHooks hc) () _ _ _ _ = _
    rw [BodyStep.evalOperandAt_current]
    rw [OperandTable.eval_constant _ _ _ () _ metadata.entry.constant constantNode _ _
      (by simpa only [BodyStep.withUnit,LocalUnit.withUnit,body.2.2] using metadata.entry_references.operand)
      (by simpa only [BodyStep.withUnit,LocalUnit.withUnit,body.2.2] using constantAt)]
    change s.cfg.operands.constant () metadata.entry.constant constantNode.operand _ _ = _
    rw [metadata.entry_constant, constantValue]
    exact constant_positive s metadata profile remaining capacity frames frame machine bodyIdentity function location
  have transfer := bound_copy_eq s s.abi.ret.layout frames frame compatible padding metadata.unitSized
  change evalRvalueIntoPlace h () _ _ _ = _
  unfold evalRvalueIntoPlace
  simp only [bind, Bind.bind, EStateM.bind, destination]
  change (h.evalOperandAt () (OperandPath.rvalue "operand") metadata.entry.operand
      (some s.abi.ret.layout) >>= fun op => MachineHooks.withRetagMode .Default
        (h.copyOp () op (BodyStep.destination frames frame s.abi.ret.layout))) _ = _
  simp only [bind, Bind.bind, EStateM.bind, literal]
  rw [transfer]
  exact scoped_copy_error s metadata profile remaining capacity frames frame machine noClocks noGhost shallow error failed

 theorem statement_error (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
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
    (error : StepError)
    (failed : ∀ machine : MachineHooks.MachineState MiriMemoryKind RootUser,
      machine.user.payload.ghost = false → machine.user.payload.validation = .Shallow →
      s.cfg.projection.place.validate () (BodyStep.destination frames frame s.abi.ret.layout)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
        .error error (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine)) :
    (ExecutionMachine.stepHooks s.cfg s.limits).assign () metadata.entry.destination
      metadata.entry.rvalue
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,.error error) := by
  have assigned := rvalue_error s metadata profile remaining capacity frames frame machine
    bodyIdentity body function location noClocks noGhost shallow error failed
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

 theorem step_error (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
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
    (error : StepError)
    (failed : ∀ machine : MachineHooks.MachineState MiriMemoryKind RootUser,
      machine.user.payload.ghost = false → machine.user.payload.validation = .Shallow →
      s.cfg.projection.place.validate () (BodyStep.destination frames frame s.abi.ret.layout)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
        .error error (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine)) :
    ExecutionMachine.step s.cfg s.limits ()
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,.error error) := by
  have assigned := statement_error s metadata profile remaining capacity frames frame machine
    bodyIdentity body function location noClocks noGhost shallow error failed
  have evaluated : Step.evalStatement (ExecutionMachine.stepHooks s.cfg s.limits) () metadata.entry.statement
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,.error error) := by
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

 theorem step_capacity_one (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (capacity : s.capacity = 1)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : Meaning.FrameMatches frame s.loaded)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
 :
    ExecutionMachine.step s.cfg s.limits ()
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,
        .error (.resourceExhaustion "execution callback construction capacity")) := by
  apply step_error s metadata profile 0 capacity frames frame machine bodyIdentity body function location
    noClocks noGhost shallow
  intro machine _ _
  exact validate_capacity_one s metadata capacity () _ _

 theorem step_validation_zero (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (zeroBudget : s.options.limits.validation = 0)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : Meaning.FrameMatches frame s.loaded)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
 :
    ExecutionMachine.step s.cfg s.limits ()
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,
        .error (.resourceExhaustion "validity traversal fuel")) := by
  apply step_error s metadata profile (remaining+1) (by omega) frames frame machine bodyIdentity body function location
    noClocks noGhost shallow
  intro machine ghost validation
  exact validate_budget_zero s metadata profile remaining capacity zeroBudget frames frame machine noClocks ghost validation

open Lean Elab Command in
run_cmd do
  let mut total : Nat := 0
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.BodyFailures." ||
        (name.toString.startsWith "_private." && name.toString.contains "BodyFailures") then
      total := total+1
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved body failure axiom {dependency} in {name}"
  logInfo m!"Audited {total} body failure declarations"
#print axioms step_capacity_one
#print axioms step_validation_zero
end EmptyFunction.BodyFailures
