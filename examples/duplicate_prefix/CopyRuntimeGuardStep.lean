import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.RootScalarQueries
import duplicate_prefix.SourceSteps
import duplicate_prefix.PrimitiveCallReturn
import duplicate_prefix.GenericPopFrame
import duplicate_prefix.SourceControl
import duplicate_prefix.DestinationCache

/-! The first statement in the production language-runtime guard: its actual
`!true` MIR assignment writes false to the return local. -/

namespace DuplicatePrefix.CopyRuntimeGuardStep
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def postFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid : (0 : Miri.MIR.LocalId) < frame.locals.size) :=
  {frame with locals := (frame.locals.set 0
    {value := .live (.immediate (.scalar (Scalar.fromBool false))),
     layout := some RootCompilerFacts.boolLayout} valid)}

theorem runtime_source_statement :
    ∃ block statement,
      CopyPreconditions.Bodies.languageRuntime.loaded.body.basicBlocks[0]? = some block ∧
      block.statements[0]? = some statement ∧
      statement.kind = .Assign ⟨0,#[]⟩
        (.UnaryOp .Not (.Constant CopyPreconditions.Bodies.languageTrueConstant)) := by
  have shape := CopyPreconditions.Bodies.language_runtime_literal.1
  cases blockEq : CopyPreconditions.Bodies.languageRuntime.loaded.body.basicBlocks[0]? with
  | none => simp [CopyPreconditions.Bodies.statementKindAt, blockEq] at shape
  | some block =>
    cases statementEq : block.statements[0]? with
    | none => simp [CopyPreconditions.Bodies.statementKindAt, blockEq, statementEq] at shape
    | some statement =>
      refine ⟨block, statement, rfl, statementEq, ?_⟩
      simpa [CopyPreconditions.Bodies.statementKindAt, blockEq, statementEq] using shape

theorem runtime_return_block :
    ∃ block,
      CopyPreconditions.Bodies.languageRuntime.loaded.body.basicBlocks[0]? = some block ∧
      block.statements[1]? = none ∧ block.terminator.kind = .Return ∧ block.cleanup = false := by
  have shape := CopyPreconditions.Bodies.language_runtime_literal.2.2
  cases blockEq : CopyPreconditions.Bodies.languageRuntime.loaded.body.basicBlocks[0]? with
  | none => simp [CopyPreconditions.Bodies.terminatorKindAt, blockEq] at shape
  | some block =>
    refine ⟨block, rfl, ?_, ?_, ?_⟩
    · have reflectedNoStatement :
        CopyPreconditions.Bodies.languageRuntime.loaded.body.basicBlocks[0]?.bind
          (fun bb => bb.statements[1]?) = none := by with_unfolding_all rfl
      rw [blockEq] at reflectedNoStatement
      exact reflectedNoStatement
    · simpa [CopyPreconditions.Bodies.terminatorKindAt, blockEq] using shape
    · have reflectedNormal :
        (CopyPreconditions.Bodies.languageRuntime.loaded.body.basicBlocks[0]?).map (·.cleanup) = some false := by
        with_unfolding_all rfl
      rw [blockEq] at reflectedNormal
      simpa using reflectedNormal

theorem parent_dead2_shape :
    CopyPreconditions.Bodies.statementKindAt CopyPreconditions.Bodies.checkLanguage.loaded.body 1 0 =
      some (.StorageDead 2) := by with_unfolding_all rfl

theorem parent_dead2_source_statement :
    ∃ block statement,
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[1]? = some block ∧
      block.statements[0]? = some statement ∧ statement.kind = .StorageDead 2 := by
  have shape := parent_dead2_shape
  cases blockEq : CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[1]? with
  | none => simp [CopyPreconditions.Bodies.statementKindAt, blockEq] at shape
  | some block =>
    cases statementEq : block.statements[0]? with
    | none => simp [CopyPreconditions.Bodies.statementKindAt, blockEq, statementEq] at shape
    | some statement =>
      refine ⟨block, statement, rfl, statementEq, ?_⟩
      simpa [CopyPreconditions.Bodies.statementKindAt, blockEq, statementEq] using shape

theorem runtime_local0_normalized (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 0 = .ok 0 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem runtime_compute_local0
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 0
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.boolLayout (Storage.withCurrent framesBefore frame machine) := by
  have normalized := runtime_local0_normalized frame body identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 0 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent framesBefore frame machine)
    | .error error => EStateM.Result.error
        (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent framesBefore frame machine)) = _
  rw [RootCompilerFacts.bool_layout_eq]
  rfl

theorem runtime_destination_local0_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (uncached0 : (frame.locals[0]'valid0).layout = none)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨0,#[]⟩ true (Storage.withCurrent framesBefore frame machine) =
      .ok (LocalPlaces.localRuntimePlace framesBefore.size
        (LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.boolLayout valid0) 0
        RootCompilerFacts.boolLayout)
        (Storage.withCurrent framesBefore
          (LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.boolLayout valid0) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.boolLayout valid0
  let updated := Storage.withCurrent framesBefore updatedFrame machine
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let hooks := projection.place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : hooks.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  have frameIndex : hooks.frameIndex state = .ok framesBefore.size state := by
    change config.projection.place.frameIndex state = .ok framesBefore.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, Except.pure, Except.bind]
  have resolve : hooks.resolveLayout () 0 state = .ok RootCompilerFacts.boolLayout state := by
    change config.projection.place.resolveLayout () 0 state = .ok RootCompilerFacts.boolLayout state
    rw [fields.projectionResolveLayout, fields.layout]
    exact runtime_compute_local0 framesBefore frame machine body identity callee
  have setCached : hooks.setFrame updatedFrame state = .ok () updated := by
    change config.projection.place.setFrame updatedFrame state = .ok () updated
    rw [fields.projectionSetFrame]
    exact Storage.set_current_frame framesBefore frame updatedFrame machine
  have getCached : hooks.getFrame updated = .ok updatedFrame updated := by
    change config.projection.place.getFrame updated = .ok updatedFrame updated
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore updatedFrame machine
  have indexCached : hooks.frameIndex updated = .ok framesBefore.size updated := by
    change config.projection.place.frameIndex updated = .ok framesBefore.size updated
    rw [fields.projectionFrameIndex]
    simp [updated, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, Except.pure, Except.bind]
  have sized : RootCompilerFacts.boolLayout.layout.isSized = true := by decide +kernel
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine 0
    framesBefore.size RootCompilerFacts.boolLayout valid0 uncached0 sized
    resolve getFrame frameIndex setCached getCached indexCached
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨0,#[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 0 RootCompilerFacts.boolLayout) updated
  exact LocalPlaces.evalPlace_local_empty_uncached projection () 0 framesBefore frame machine
    framesBefore.size RootCompilerFacts.boolLayout valid0
    (state := state) (updated := updated) localPlace check

theorem runtime_destination_local0_cached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (cached0 : (frame.locals[0]'valid0).layout = some RootCompilerFacts.boolLayout) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨0,#[]⟩ true (Storage.withCurrent framesBefore frame machine) =
      .ok (LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.boolLayout)
        (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let hooks := projection.place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : hooks.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  have frameIndex : hooks.frameIndex state = .ok framesBefore.size state := by
    change config.projection.place.frameIndex state = .ok framesBefore.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, Except.pure, Except.bind]
  have sized : RootCompilerFacts.boolLayout.layout.isSized = true := by decide +kernel
  have localPlace := LocalPlaces.localToPlace_cached hooks () frame 0 framesBefore.size
    RootCompilerFacts.boolLayout state valid0 getFrame frameIndex cached0 sized
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨0,#[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.boolLayout) state
  exact LocalPlaces.evalPlace_local_empty projection () 0 frame framesBefore.size
    RootCompilerFacts.boolLayout state localPlace check

theorem actual_runtime_not_true_assignment_effect
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (uninit0 : (frame.locals[0]'valid0).value = .live (.immediate .uninit))
    (cached0 : (frame.locals[0]'valid0).layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (location : frame.location = .mir ⟨0,0⟩)
    (fnInstance : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      (.UnaryOp .Not (.Constant CopyPreconditions.Bodies.languageTrueConstant)) ⟨0,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (postFrame frame valid0) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  have sized := RootGenericBoolWrite.bool_sized
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.boolLayout RootGenericBoolWrite.bool_initialized
  have readable : ∃ primitive range, RootCompilerFacts.boolLayout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range)) :=
    ⟨primitive, range, repr⟩
  have classification := RootScalarQueries.bool_classification options (remaining + 1) span limits
  have boolQuery := RootScalarQueries.bool_layout options (remaining + 1) span limits
  have bodyIndex : frame.bodyIdentity.index =
      CopyPreconditions.Bodies.languageRuntime.loaded.identity.index :=
    congrArg (fun id : BodyIdentity => id.index) identity
  have rvalue := CopyLanguageGuard.canonical_runtime_not_true_to_write
    options limits (remaining + 1) span source debugOff framesBefore frame machine valid0 cached0
    sized readable bodyIndex location fnInstance classification boolQuery
  have write := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff
    fuel fuelEq framesBefore frame machine 0 .uninit false valid0 uninit0 cached0
    noClocks ghostFalse shallow
  have write' : hooks.writeImmediate () (.scalar (.fromBool false))
      (LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.boolLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (postFrame frame valid0) machine) := by
    have outFrameEq :
        {frame with locals := (frame.locals.set 0
          {value := .live (.immediate (.scalar (Scalar.fromBool false))),
           layout := frame.locals[0].layout} valid0)} = postFrame frame valid0 := by
      simp [postFrame, cached0]
    rw [← outFrameEq]
    exact write
  rw [rvalue]
  exact write'

theorem actual_runtime_not_true_assignment_uncached_effect
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (uninit0 : (frame.locals[0]'valid0).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'valid0).layout = none)
    (noClocks : frame.extra.dataRace = none)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (location : frame.location = .mir ⟨0,0⟩)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      (.UnaryOp .Not (.Constant CopyPreconditions.Bodies.languageTrueConstant)) ⟨0,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (postFrame frame valid0) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let updatedFrame := LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.boolLayout valid0
  let state := Storage.withCurrent framesBefore frame machine
  let updated := Storage.withCurrent framesBefore updatedFrame machine
  have validUpdated : (0 : Miri.MIR.LocalId) < updatedFrame.locals.size := by
    simpa [updatedFrame, LocalPlaces.cachePlaceLayout, Array.size_set] using valid0
  have uninitUpdated : (updatedFrame.locals[0]'validUpdated).value = .live (.immediate .uninit) := by
    simp [updatedFrame, LocalPlaces.cachePlaceLayout, uninit0]
  have cachedUpdated : (updatedFrame.locals[0]'validUpdated).layout = some RootCompilerFacts.boolLayout := by
    simp [updatedFrame, LocalPlaces.cachePlaceLayout, valid0]
  have noClocksUpdated : updatedFrame.extra.dataRace = none := by
    simpa [updatedFrame, LocalPlaces.cachePlaceLayout] using noClocks
  have bodyUpdated : updatedFrame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body := by
    simpa [updatedFrame, LocalPlaces.cachePlaceLayout] using body
  have identityUpdated : updatedFrame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity := by
    simpa [updatedFrame, LocalPlaces.cachePlaceLayout] using identity
  have locationUpdated : updatedFrame.location = .mir ⟨0,0⟩ := by
    simpa [updatedFrame, LocalPlaces.cachePlaceLayout] using location
  have calleeUpdated : updatedFrame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance := by
    simpa [updatedFrame, LocalPlaces.cachePlaceLayout] using callee
  have bodyIndexUpdated : updatedFrame.bodyIdentity.index = CopyPreconditions.Bodies.languageRuntime.loaded.identity.index :=
    congrArg (fun id : BodyIdentity => id.index) identityUpdated
  have destinationFirst := runtime_destination_local0_uncached options limits (remaining + 1) span
    debugOff framesBefore frame machine valid0 uncached0 body identity callee
  have destinationAgain := runtime_destination_local0_cached options limits (remaining + 1) span
    debugOff framesBefore updatedFrame machine validUpdated cachedUpdated
  let dest := LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 0 RootCompilerFacts.boolLayout
  have first : hooks.evalPlace () ⟨0,#[]⟩ true state = .ok dest updated := by
    simpa [hooks, config, dest, updated, updatedFrame] using destinationFirst
  have again : hooks.evalPlace () ⟨0,#[]⟩ true updated = .ok dest updated := by
    simpa [hooks, config, dest, updated] using destinationAgain
  have cacheIrrelevance := DestinationCache.evaluate_from_cached hooks ()
    (.UnaryOp .Not (.Constant CopyPreconditions.Bodies.languageTrueConstant)) ⟨0,#[]⟩ dest
    state updated first again
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.boolLayout RootGenericBoolWrite.bool_initialized
  have readable : ∃ primitive range, RootCompilerFacts.boolLayout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range)) := ⟨primitive,range,repr⟩
  have sized := RootGenericBoolWrite.bool_sized
  have classification := RootScalarQueries.bool_classification options (remaining + 1) span limits
  have boolQuery := RootScalarQueries.bool_layout options (remaining + 1) span limits
  have rvalue := CopyLanguageGuard.canonical_runtime_not_true_to_write options limits
    (remaining + 1) span source debugOff framesBefore updatedFrame machine validUpdated cachedUpdated
    sized readable bodyIndexUpdated locationUpdated calleeUpdated classification boolQuery
  have write := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff
    fuel fuelEq framesBefore updatedFrame machine 0 .uninit false validUpdated uninitUpdated cachedUpdated
    noClocksUpdated ghostFalse shallow
  have outFrameEq : postFrame updatedFrame validUpdated = postFrame frame valid0 := by
    simp [postFrame, updatedFrame, LocalPlaces.cachePlaceLayout, valid0]
  have write' : hooks.writeImmediate () (.scalar (.fromBool false)) dest updated =
      .ok () (Storage.withCurrent framesBefore (postFrame frame valid0) machine) := by
    have writeFrameEq :
        {updatedFrame with locals := (updatedFrame.locals.set 0
          {value := .live (.immediate (.scalar (Scalar.fromBool false))),
           layout := updatedFrame.locals[0].layout} validUpdated)} = postFrame updatedFrame validUpdated := by
      simp [postFrame, cachedUpdated]
    rw [← outFrameEq]
    rw [← writeFrameEq]
    exact write
  have cachedEffect : evalRvalueIntoPlace hooks ()
      (.UnaryOp .Not (.Constant CopyPreconditions.Bodies.languageTrueConstant)) ⟨0,#[]⟩ updated =
      .ok () (Storage.withCurrent framesBefore (postFrame frame valid0) machine) := by
    rw [rvalue]
    exact write'
  rw [cacheIrrelevance]
  exact cachedEffect

#print axioms actual_runtime_not_true_assignment_uncached_effect

#print axioms actual_runtime_not_true_assignment_effect

theorem actual_runtime_not_true_assignment_step
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (block : Miri.MIR.BasicBlock) (statement : Miri.MIR.Statement)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (uninit0 : (frame.locals[0]'valid0).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'valid0).layout = none)
    (noClocks : frame.extra.dataRace = none)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (location : frame.location = .mir ⟨0,0⟩)
    (fnInstance : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (blockAt : frame.body.basicBlocks[0]? = some block)
    (statementAt : block.statements[0]? = some statement)
    (kind : statement.kind = .Assign ⟨0,#[]⟩
      (.UnaryOp .Not (.Constant CopyPreconditions.Bodies.languageTrueConstant))) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {postFrame frame valid0 with location := .mir ⟨0,1⟩} machine, .ok true) := by
  have effect := actual_runtime_not_true_assignment_uncached_effect options limits remaining span source
    debugOff fuel fuelEq framesBefore frame machine valid0 uninit0 uncached0 noClocks body identity
    location fnInstance ghostFalse shallow
  have step := SourceSteps.assign_exact
    (PreparedContracts.actualConfig options () (remaining + 1) span) limits () framesBefore frame
    (postFrame frame valid0) machine machine ⟨0,0⟩ block statement ⟨0,#[]⟩
    (.UnaryOp .Not (.Constant CopyPreconditions.Bodies.languageTrueConstant)) location blockAt
    statementAt kind effect (by simp [postFrame, location])
  simpa [ExecutionMachine.step, postFrame, Array.set_push] using step

#print axioms actual_runtime_not_true_assignment_step

theorem actual_runtime_not_true_source_step
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (uninit0 : (frame.locals[0]'valid0).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'valid0).layout = none)
    (noClocks : frame.extra.dataRace = none)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (location : frame.location = .mir ⟨0,0⟩)
    (fnInstance : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {postFrame frame valid0 with location := .mir ⟨0,1⟩} machine, .ok true) := by
  obtain ⟨block, statement, reflectedBlockAt, reflectedStatementAt, kind⟩ := runtime_source_statement
  have blockAt : frame.body.basicBlocks[0]? = some block := by rw [body]; exact reflectedBlockAt
  have statementAt : block.statements[0]? = some statement := reflectedStatementAt
  exact actual_runtime_not_true_assignment_step options limits remaining span source debugOff fuel fuelEq
    framesBefore frame machine block statement valid0 uninit0 uncached0 noClocks body identity location
    fnInstance ghostFalse shallow blockAt statementAt kind

#print axioms actual_runtime_not_true_source_step

def returnedCallerFrame (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid1 : (1 : Miri.MIR.LocalId) < caller.locals.size)
    (target : BasicBlockId) :=
  {caller with
    locals := caller.locals.set 1
      {value := .live (.immediate (.scalar (Scalar.fromBool false))),
       layout := (caller.locals[1]'valid1).layout} valid1,
    location := .mir ⟨target,0⟩}

def runtimeAfterAssign (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size) :=
  {(postFrame frame valid0) with location := .mir ⟨0,1⟩}

def returnedRuntimeMachine (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (index : Nat) :=
  GenericPopFrame.afterRelevanceAt (frames.push caller) frame machine index

theorem returnedRuntimeMachine_user
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (index : Nat) :
    (returnedRuntimeMachine frames caller frame machine index).user = machine.user := by
  unfold returnedRuntimeMachine GenericPopFrame.afterRelevanceAt
  split <;> rfl

theorem runtime_return_driver
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance)
    (location : frame.location = .mir ⟨0,1⟩)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : (frame.locals[0]'valid0).value = .live (.immediate (.scalar (.fromBool false))))
    (cached0 : (frame.locals[0]'valid0).layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (callerValid1 : (1 : Miri.MIR.LocalId) < caller.locals.size)
    (callerUninit1 : (caller.locals[1]'callerValid1).value = .live (.immediate .uninit))
    (callerCached1 : (caller.locals[1]'callerValid1).layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining + 1) span
    ControlFlow.returnFromCurrentFrame (GenericCallReturn.sourceControl config limits) () false
      (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames
        (returnedCallerFrame caller callerValid1 target)
        (returnedRuntimeMachine frames caller frame machine
          (thread.topUserRelevantFrame.getD (frames.push caller).size)), .ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let control := GenericCallReturn.sourceControl config limits
  let before := Storage.withCurrent (frames.push caller) frame machine
  let index := thread.topUserRelevantFrame.getD (frames.push caller).size
  let poppedMachine := returnedRuntimeMachine frames caller frame machine index
  let afterPop := Storage.withCurrent frames caller poppedMachine
  let writtenCaller := {caller with locals := (caller.locals.set 1
    {value := .live (.immediate (.scalar (Scalar.fromBool false))),
     layout := (caller.locals[1]'callerValid1).layout} callerValid1)}
  let afterCopy := Storage.withCurrent frames writtenCaller poppedMachine
  let result : OpTy Provenance := ⟨.immediate (.scalar (.fromBool false)),RootCompilerFacts.boolLayout⟩
  obtain ⟨block, reflectedBlockAt, noStatement, returnKind, normal⟩ := runtime_return_block
  have blockAt : frame.body.basicBlocks[0]? = some block := by rw [body]; exact reflectedBlockAt
  have read' : control.returnOperand () before = (before,.ok result) := by
    exact PrimitiveCallReturn.read_current_return options limits (remaining + 1) span
      (frames.push caller) frame machine RootCompilerFacts.boolLayout
      (.scalar (.fromBool false)) valid0 live0 cached0 RootGenericBoolWrite.bool_sized noClocks ghost
  have top := GenericPopFrame.top_nonempty (frames.push caller) frame thread.topUserRelevantFrame
  have pop : control.popFrame () before = (afterPop,.ok frame) := by
    change MachineHooks.run (TypedMachineBindings.popRaw
      (TypedMachineBindings.retagHooks config.access config.retag)) before = _
    unfold MachineHooks.run Call.run
    rw [GenericPopFrame.pop_empty_active (TypedMachineBindings.retagHooks config.access config.retag)
      (frames.push caller) frame machine tracker borrowFrame tracked frameTracked empty thread active]
    rfl
  have copy : control.copyReturn () result frame.returnPlace afterPop = (afterCopy,.ok ()) := by
    have copied := PrimitiveCallReturn.copy_bool_return options limits remaining span debugOff fuel
      validationFuel frames caller poppedMachine 1 .uninit false callerValid1 callerUninit1
      callerCached1 callerNoClocks (by rw [returnedRuntimeMachine_user]; exact ghost)
      (by rw [returnedRuntimeMachine_user]; exact shallow)
      frame.returnPlace destination
    exact copied
  have noGc' := noGc
  have unchecked' := unchecked
  have fixed' := fixed
  have accounting := SourceControl.before_terminator config limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining + 1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining + 1) span)
    unchecked' noGc' fixed'
  have accounting' : (ExecutionMachine.stepHooks config limits).beforeTerminator () before =
      (SourceControl.accounted config.terminators before, .ok ()) := accounting
  have cleanup := PrimitiveCallReturn.cleanup_immediate_return options limits (remaining + 1) span ()
    afterCopy frame (some target) unwindAction continuation immediateLocals varargs
  have returned := GenericCallReturn.normal_goto control () before before afterPop afterCopy afterCopy
    frame frame ⟨0,1⟩ block result target unwindAction
    (by simp [before, Storage.withCurrent, Stack.currentFrame?]) location blockAt normal read' pop copy cleanup continuation
  change ControlFlow.returnFromCurrentFrame control () false before = _
  rw [returned]
  exact GenericCallReturn.goto_current frames writtenCaller poppedMachine target

#print axioms runtime_return_driver

theorem actual_runtime_return_step
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance)
    (location : frame.location = .mir ⟨0,1⟩)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : (frame.locals[0]'valid0).value = .live (.immediate (.scalar (.fromBool false))))
    (cached0 : (frame.locals[0]'valid0).layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (callerValid1 : (1 : Miri.MIR.LocalId) < caller.locals.size)
    (callerUninit1 : (caller.locals[1]'callerValid1).value = .live (.immediate .uninit))
    (callerCached1 : (caller.locals[1]'callerValid1).layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining + 1) span
    ExecutionMachine.step config limits ()
      (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames
        (returnedCallerFrame caller callerValid1 target)
        (returnedRuntimeMachine frames caller frame
          (SourceControl.accounted config.terminators
            (Storage.withCurrent (frames.push caller) frame machine)).machine
          (thread.topUserRelevantFrame.getD (frames.push caller).size)), .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let before := Storage.withCurrent (frames.push caller) frame machine
  let accounted := SourceControl.accounted config.terminators before
  let accountedMachine := accounted.machine
  let afterAccounted := Storage.withCurrent (frames.push caller) frame accountedMachine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have getSet : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control := by
    rw [fields.terminators]
    intro control user
    rfl
  have setSet : ∀ first second user,
      config.terminators.setControl second (config.terminators.setControl first user) =
        config.terminators.setControl second user := by
    rw [fields.terminators]
    intro first second user
    rfl
  have accountedEq : accounted = SourceControl.accounted config.terminators before := rfl
  have accountedMachineEq : accountedMachine =
      {machine with user := (config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user)} := by
    change (SourceControl.accounted config.terminators before).machine = _
    simp [SourceControl.accounted, before, Storage.withCurrent]
  have accountedControl : accountedMachine.user =
      config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user := by
    change (SourceControl.accounted config.terminators before).machine.user = _
    rw [fields.terminators]
    rfl
  have accountedGhost : accountedMachine.user.payload.ghost = false := by
    have unchanged : (config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user).payload.ghost =
        machine.user.payload.ghost := by rw [fields.terminators]; rfl
    rw [accountedControl, unchanged, ghost]
  have accountedShallow : accountedMachine.user.payload.validation = .Shallow := by
    have unchanged : (config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user).payload.validation =
        machine.user.payload.validation := by rw [fields.terminators]; rfl
    rw [accountedControl, unchanged, shallow]
  have accountedTracked : accountedMachine.borrowTracker = some tracker := by
    simpa [accountedMachineEq] using tracked
  have accountedActive : accountedMachine.threads.activeThread? = some thread := by
    simpa [accountedMachineEq] using active
  have accountedUnchecked : (config.terminators.getControl accountedMachine.user).checkedArithmetic = false := by
    rw [accountedControl, getSet]
    simpa [TerminatorClock.advance] using unchecked
  have accountedNoGc : (config.terminators.getControl accountedMachine.user).gcInterval = 0 := by
    rw [accountedControl, getSet]
    simpa [TerminatorClock.advance] using noGc
  have accounting := SourceControl.before_terminator config limits () before getSet setSet unchecked noGc fixed
  have driver := runtime_return_driver options limits remaining span debugOff fuel validationFuel
    frames caller frame accountedMachine body identity callee location valid0 live0 cached0 noClocks
    callerValid1 callerUninit1 callerCached1 callerNoClocks destination target unwindAction continuation
    immediateLocals varargs tracker borrowFrame accountedTracked frameTracked empty thread accountedActive
    accountedUnchecked accountedNoGc fixed accountedGhost accountedShallow
  obtain ⟨block, blockAtReflected, noStatement, returnKind, _normal⟩ := runtime_return_block
  have blockAt : frame.body.basicBlocks[0]? = some block := by rw [body]; exact blockAtReflected
  have current : before.stack.currentFrame? = some frame := by
    simp [before, Storage.withCurrent, Stack.currentFrame?]
  have returned : ControlFlow.returnFromCurrentFrame (GenericCallReturn.sourceControl config limits) () false
      afterAccounted = (Storage.withCurrent frames
        (returnedCallerFrame caller callerValid1 target)
        (returnedRuntimeMachine frames caller frame accountedMachine
          (thread.topUserRelevantFrame.getD (frames.push caller).size)), .ok ()) := by
    simpa [afterAccounted, accountedMachine] using driver
  exact GenericCallReturn.return_step_exact config limits () before accounted
    (Storage.withCurrent frames
      (returnedCallerFrame caller callerValid1 target)
      (returnedRuntimeMachine frames caller frame accountedMachine
        (thread.topUserRelevantFrame.getD (frames.push caller).size)))
    frame ⟨0,1⟩ block current location blockAt noStatement returnKind accounting returned

#print axioms actual_runtime_return_step

theorem actual_runtime_body_returns_false
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (uninit0 : (frame.locals[0]'valid0).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'valid0).layout = none)
    (noClocks : frame.extra.dataRace = none)
    (callerValid1 : (1 : Miri.MIR.LocalId) < caller.locals.size)
    (callerUninit1 : (caller.locals[1]'callerValid1).value = .live (.immediate .uninit))
    (callerCached1 : (caller.locals[1]'callerValid1).layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (frameSize : frame.locals.size = 1)
    (callerSize : caller.locals.size > 1)
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ∃ afterAssign,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        (Storage.withCurrent (frames.push caller) frame machine) = (afterAssign,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits () afterAssign =
        (Storage.withCurrent frames (returnedCallerFrame caller callerValid1 target)
          (returnedRuntimeMachine frames caller (runtimeAfterAssign frame valid0)
            (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining + 1) span).terminators
              (Storage.withCurrent (frames.push caller) (runtimeAfterAssign frame valid0) machine)).machine
            (thread.topUserRelevantFrame.getD (frames.push caller).size)), .ok true) := by
  let afterFrame := runtimeAfterAssign frame valid0
  have frameIdentityAfter : afterFrame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity := by
    simpa [afterFrame, runtimeAfterAssign, postFrame] using identity
  have frameCalleeAfter : afterFrame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance := by
    simpa [afterFrame, runtimeAfterAssign, postFrame] using callee
  have frameBodyAfter : afterFrame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body := by
    simpa [afterFrame, runtimeAfterAssign, postFrame] using body
  have frameLocationAfter : afterFrame.location = .mir ⟨0,1⟩ := by
    simp [afterFrame, runtimeAfterAssign, postFrame]
  have validAfter : (0 : Miri.MIR.LocalId) < afterFrame.locals.size := by
    simpa [afterFrame, runtimeAfterAssign, postFrame] using valid0
  have liveAfter : (afterFrame.locals[0]'validAfter).value = .live
      (.immediate (.scalar (.fromBool false))) := by
    simp [afterFrame, runtimeAfterAssign, postFrame, valid0]
  have cachedAfter : (afterFrame.locals[0]'validAfter).layout = some RootCompilerFacts.boolLayout := by
    simp [afterFrame, runtimeAfterAssign, postFrame, valid0]
  have noClocksAfter : afterFrame.extra.dataRace = none := by
    simpa [afterFrame, runtimeAfterAssign, postFrame] using noClocks
  have immediateAfter : ∀ slot ∈ afterFrame.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
    intro slot member memory indirect
    rcases Array.mem_iff_getElem.mp member with ⟨index, validIndex, equal⟩
    have indexZero : index = 0 := by
      simp [afterFrame, runtimeAfterAssign, postFrame, frameSize] at validIndex
      omega
    subst index
    have value := liveAfter
    rw [equal] at value
    rw [indirect] at value
    cases value
  have callStep := actual_runtime_not_true_source_step options limits remaining span source debugOff
    fuel validationFuel (frames.push caller) frame machine valid0 uninit0 uncached0 noClocks body identity
    location callee ghost shallow
  have returnStep := actual_runtime_return_step options limits remaining span debugOff fuel validationFuel
    frames caller afterFrame machine frameBodyAfter frameIdentityAfter frameCalleeAfter frameLocationAfter
    validAfter liveAfter cachedAfter noClocksAfter callerValid1 callerUninit1 callerCached1 callerNoClocks
    destination target unwindAction (by simpa [afterFrame, runtimeAfterAssign, postFrame] using continuation) immediateAfter varargs
    tracker borrowFrame tracked (by simpa [afterFrame, runtimeAfterAssign, postFrame] using frameTracked)
    empty thread active unchecked noGc fixed ghost shallow
  refine ⟨_, callStep, ?_⟩
  simpa [afterFrame, runtimeAfterAssign, postFrame] using returnStep

#print axioms actual_runtime_body_returns_false

theorem actual_parent_false_switch
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨1,1⟩)
    (valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (live1 : (frame.locals[1]'valid1).value = .live (.immediate (.scalar (.fromBool false))))
    (cached1 : (frame.locals[1]'valid1).layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    ∃ after,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        (Storage.withCurrent frames frame machine) = (after,.ok true) ∧
      after.stack.currentFrame?.map (·.location) = some (.mir ⟨3,0⟩) ∧
      after.machine.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      after = Storage.withCurrent frames {frame with location := .mir ⟨3,0⟩}
        (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining+1) span).terminators
          (Storage.withCurrent frames frame machine)).machine := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let before := Storage.withCurrent frames frame machine
  let accounted := SourceControl.accounted config.terminators before
  let accountedMachine := accounted.machine
  have accountedFrame : accounted = Storage.withCurrent frames frame accountedMachine := rfl
  let afterFrame := {frame with location := .mir ⟨3,0⟩}
  let after := Storage.withCurrent frames afterFrame accountedMachine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have getSet : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control := by
    rw [fields.terminators]
    intro control user
    rfl
  have setSet : ∀ first second user,
      config.terminators.setControl second (config.terminators.setControl first user) =
        config.terminators.setControl second user := by
    rw [fields.terminators]
    intro first second user
    rfl
  have accounting := SourceControl.before_terminator config limits () before getSet setSet unchecked noGc fixed
  have accountedControl : accountedMachine.user = config.terminators.setControl
      (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user := by
    change (SourceControl.accounted config.terminators before).machine.user = _
    rw [fields.terminators]
    rfl
  have accountedMachineEq : accountedMachine = {machine with user :=
      (config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user)} := by
    change (SourceControl.accounted config.terminators before).machine = _
    simp [SourceControl.accounted, before, Storage.withCurrent]
  have accountedGhost : accountedMachine.user.payload.ghost = false := by
    have unchanged : (config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user).payload.ghost =
        machine.user.payload.ghost := by rw [fields.terminators]; rfl
    rw [accountedControl, unchanged, ghost]
  have validGetter : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)).compiler.validationInProgress
      (Storage.withCurrent frames frame accountedMachine) =
      .ok false (Storage.withCurrent frames frame accountedMachine) := by
    change config.compiler.validationInProgress
      (Storage.withCurrent frames frame accountedMachine) = _
    rw [fields.compilerValidationInProgress]
    simp [ValidityMachine.validationInProgress, accountedGhost, Storage.withCurrent,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have blockShape := CopyPreconditions.Bodies.language_guard_branches.1
  have blockExists : ∃ block,
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[1]? = some block ∧
      block.terminator.kind = .SwitchInt (.Move ⟨1,#[]⟩) ⟨#[.Case 0 3],2⟩ := by
    cases h : CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[1]? with
    | none => simp [CopyPreconditions.Bodies.terminatorKindAt, h] at blockShape
    | some block =>
      refine ⟨block, rfl, ?_⟩
      simpa [CopyPreconditions.Bodies.terminatorKindAt, h] using blockShape
  obtain ⟨block, reflectedBlockAt, kind⟩ := blockExists
  have blockAt : frame.body.basicBlocks[1]? = some block := by rw [body]; exact reflectedBlockAt
  have reflectedNoStatement :
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[1]?.bind
        (fun bb => bb.statements[1]?) = none := by with_unfolding_all rfl
  have noStatement : block.statements[1]? = none := by
    rw [reflectedBlockAt] at reflectedNoStatement
    exact reflectedNoStatement
  have current : before.stack.currentFrame? = some frame := by
    simp [before, Storage.withCurrent, Stack.currentFrame?]
  have sized : RootCompilerFacts.boolLayout.layout.backendRepr.isUnsized = false := by decide +kernel
  obtain ⟨primitive, range, readable⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.boolLayout RootGenericBoolWrite.bool_initialized
  have classification := RootScalarQueries.bool_classification options (remaining + 1) span limits
  have boolQuery := RootScalarQueries.bool_layout options (remaining + 1) span limits
  have width : RootCompilerFacts.boolLayout.layout.size = Size.ofBytes 1 := by decide +kernel
  have termEffect : (ExecutionMachine.stepHooks config limits).terminator () block.terminator accounted =
      ControlFlow.goToBlock 3 accounted := by
    have getterAt : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)).compiler.validationInProgress
        (Storage.withCurrent frames frame accountedMachine) =
        .ok false (Storage.withCurrent frames frame accountedMachine) := validGetter
    have actual := CopyLanguageGuard.canonical_false_local_switch options limits (remaining + 1) span
      debugOff frames frame accountedMachine 1 3 2 block.terminator valid1 live1 cached1 sized
      ⟨primitive,range,readable⟩ noClocks getterAt kind classification boolQuery width
    rw [accountedFrame]
    exact actual
  have goToBlockEq : ControlFlow.goToBlock 3 accounted = (after,.ok ()) := by
    simp [ControlFlow.goToBlock, ControlFlow.setLocation, after, afterFrame, accounted,
      SourceControl.accounted, before, Storage.withCurrent, Stack.currentFrame?, accountedMachineEq]
  have termEffect' : (ExecutionMachine.stepHooks config limits).terminator () block.terminator accounted =
      (after,.ok ()) := by rw [termEffect, goToBlockEq]
  have step := StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) () before accounted after
    frame ⟨1,1⟩ block current location blockAt noStatement accounting termEffect'
  refine ⟨after, ?_, ?_, ?_, rfl⟩
  · simpa [ExecutionMachine.step] using step
  · simp [after, afterFrame, Storage.withCurrent, Stack.currentFrame?]
  · change before.machine.threads.fixedScheduling = machine.threads.fixedScheduling
    rfl

#print axioms actual_parent_false_switch

theorem actual_parent_false_dispatch
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨1,0⟩)
    (valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (live1 : (frame.locals[1]'valid1).value = .live (.immediate (.scalar (.fromBool false))))
    (cached1 : (frame.locals[1]'valid1).layout = some RootCompilerFacts.boolLayout)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live2 : (frame.locals[2]'valid2).value = .live (.immediate .uninit))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    ∃ deadState branchState,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        (Storage.withCurrent frames frame machine) = (deadState,.ok true) ∧
      deadState.stack.currentFrame?.map (·.location) = some (.mir ⟨1,1⟩) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits () deadState =
        (branchState,.ok true) ∧
      branchState.stack.currentFrame?.map (·.location) = some (.mir ⟨3,0⟩) ∧
      branchState = Storage.withCurrent frames
        {SourceSteps.deadFrame frame ⟨1,0⟩ 2 (by omega) with location := .mir ⟨3,0⟩}
        (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining+1) span).terminators
          (Storage.withCurrent frames
            (SourceSteps.deadFrame frame ⟨1,0⟩ 2 (by omega)) machine)).machine := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  obtain ⟨block, statement, blockReflected, statementReflected, statementKind⟩ := parent_dead2_source_statement
  have blockAt : frame.body.basicBlocks[1]? = some block := by rw [body]; exact blockReflected
  have statementAt : block.statements[0]? = some statement := statementReflected
  have deadStep := SourceSteps.storage_dead_exact config limits () frames frame machine ⟨1,0⟩ block statement
    2 .uninit location blockAt statementAt statementKind valid2 (by decide) live2
  let deadFrame := SourceSteps.deadFrame frame ⟨1,0⟩ 2 valid2
  let deadState := Storage.withCurrent frames deadFrame machine
  have valid1Dead : (1 : Miri.MIR.LocalId) < deadFrame.locals.size := by
    simpa [deadFrame, SourceSteps.deadFrame, Array.size_set] using valid1
  have live1Dead : (deadFrame.locals[1]'valid1Dead).value = .live
      (.immediate (.scalar (.fromBool false))) := by
    simpa [deadFrame, SourceSteps.deadFrame, Array.getElem_set] using live1
  have cached1Dead : (deadFrame.locals[1]'valid1Dead).layout = some RootCompilerFacts.boolLayout := by
    simpa [deadFrame, SourceSteps.deadFrame, Array.getElem_set] using cached1
  have noClocksDead : deadFrame.extra.dataRace = none := by simpa [deadFrame, SourceSteps.deadFrame] using noClocks
  have bodyDead : deadFrame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body := by
    simpa [deadFrame, SourceSteps.deadFrame] using body
  have identityDead : deadFrame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity := by
    simpa [deadFrame, SourceSteps.deadFrame] using identity
  have calleeDead : deadFrame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance := by
    simpa [deadFrame, SourceSteps.deadFrame] using callee
  have locationDead : deadFrame.location = .mir ⟨1,1⟩ := by
    simp [deadFrame, SourceSteps.deadFrame]
  have deadStateEq : deadState = Storage.withCurrent frames deadFrame machine := rfl
  have switch := actual_parent_false_switch options limits remaining span debugOff frames deadFrame machine
    bodyDead identityDead calleeDead locationDead valid1Dead live1Dead cached1Dead noClocksDead ghost
    unchecked noGc fixed
  rcases switch with ⟨branchState, switchStep, branchLocation, _, branchStateEq⟩
  refine ⟨deadState, branchState, ?_, ?_, ?_, branchLocation, ?_⟩
  · simpa [deadState, deadFrame] using deadStep
  · simp [deadState, deadFrame, SourceSteps.deadFrame, Storage.withCurrent, Stack.currentFrame?]
  · simpa [deadState] using switchStep
  · simpa [deadState,deadFrame,SourceSteps.deadFrame] using branchStateEq

#print axioms actual_parent_false_dispatch

end DuplicatePrefix.CopyRuntimeGuardStep
