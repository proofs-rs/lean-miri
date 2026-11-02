import duplicate_prefix.CopyPreconditions
import duplicate_prefix.RootConstantStage
import duplicate_prefix.RootLocalStages
import duplicate_prefix.BoolSwitch

/-! Production constant, rvalue and branch stages of the pinned Miri language
UB-check guard. No standard-library helper result is assumed: the true/false
literals are evaluated through actual compiler evidence; runtime `!true` is
reduced to the real false write, and the parent false literal to the real copy.
Call entry/return and completion of these final write/copy actions are composed
by the caller's operational trace. -/

namespace DuplicatePrefix.CopyLanguageGuard
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open CopyPreconditions
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def runtimeSite : CompilerConstantQueries.Site :=
  ⟨Bodies.languageRuntime.loaded.identity.index, ⟨0,0⟩,
    #[.field "kind", .field "rvalue", .field "operand", .field "constant"]⟩
def parentFalseSite : CompilerConstantQueries.Site :=
  ⟨Bodies.checkLanguage.loaded.identity.index, ⟨3,0⟩,
    #[.field "kind", .field "rvalue", .field "operand", .field "constant"]⟩

def runtimeEvidence : Array CompilerConstantEvidence :=
  (PreparedReflection.actual.compiler.constants.evidence.filter (·.site == runtimeSite)).map (·.query)
def parentFalseEvidence : Array CompilerConstantEvidence :=
  (PreparedReflection.actual.compiler.constants.evidence.filter (·.site == parentFalseSite)).map (·.query)

theorem runtime_normalization : normalizationFromEvidence runtimeEvidence Bodies.languageRuntime.fnInstance
    (.Val (.Scalar (.Int 1 1)) 0) = .ok (.Val (.Scalar (.Int 1 1)) 0) := by with_unfolding_all rfl

theorem parent_false_normalization : normalizationFromEvidence parentFalseEvidence Bodies.checkLanguage.fnInstance
    (.Val (.Scalar (.Int 0 1)) 0) = .ok (.Val (.Scalar (.Int 0 1)) 0) := by with_unfolding_all rfl

theorem scalar_bool (runtime : RuntimeMetadata)
    (queries : ConstantValueQueries Provenance BorrowTree K H)
    (state : ConstantState Provenance BorrowTree K H) (layout : LocalLayout) (value : Bool) :
    valueToOpWithLayout runtime queries (.Scalar (.Int (if value then 1 else 0) 1)) 0 (some layout) none state =
      .ok ⟨.immediate (.scalar (Scalar.fromBool value)),layout⟩ state := by
  cases value <;> with_unfolding_all rfl

theorem scalar_true (runtime : RuntimeMetadata)
    (queries : ConstantValueQueries Provenance BorrowTree K H)
    (state : ConstantState Provenance BorrowTree K H) (layout : LocalLayout) :
    valueToOpWithLayout runtime queries (.Scalar (.Int 1 1)) 0 (some layout) none state =
      .ok ⟨.immediate (.scalar (Scalar.fromBool true)),layout⟩ state :=
  scalar_bool runtime queries state layout true

theorem scalar_false (runtime : RuntimeMetadata)
    (queries : ConstantValueQueries Provenance BorrowTree K H)
    (state : ConstantState Provenance BorrowTree K H) (layout : LocalLayout) :
    valueToOpWithLayout runtime queries (.Scalar (.Int 0 1)) 0 (some layout) none state =
      .ok ⟨.immediate (.scalar (Scalar.fromBool false)),layout⟩ state :=
  scalar_bool runtime queries state layout false

open Lean Elab Tactic in
elab "simp_language_constant" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith "Miri.Interpreter.constantType" then some (mkIdent name) else none
  let names := names.toArray
  evalTactic (← `(tactic| simp_all (config := {maxSteps := 1000000}) [
    CompilerConstantMachine.evalAtBound, ConstantMachine.fromCompiler,
    ConstantMachine.evalOperandWithLayout, evalConstOperandWithLayout,
    evalMirConstantWithLayout, constValueToOpWithLayout,
    ConstantQueries.valueQueries, MachineHooks.currentFrame,
    Storage.withCurrent, Stack.currentFrame?, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Except.bind, Except.pure, runtimeSite, parentFalseSite, scalar_true, scalar_false, $[$names:ident],*]))

theorem runtime_true_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = Bodies.languageRuntime.loaded.identity.index)
    (location : frame.location = .mir ⟨0,0⟩)
    (fnInstance : frame.functionInstance = Bodies.languageRuntime.fnInstance) :
    CompilerConstantMachine.evalAtBound PreparedReflection.actual.compiler.constantBinding
      runtimeSite functions arithmetic externStatic MemoryErrors.constant
      Bodies.languageTrueConstant (some RootCompilerFacts.boolLayout) none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (Scalar.fromBool true)),RootCompilerFacts.boolLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  have compatible := RootCompilerFacts.constant_binding_compatible source
  have norm : normalizationFromEvidence
      ((PreparedReflection.actual.compiler.constants.evidence.filter (·.site == runtimeSite)).map (·.query))
      Bodies.languageRuntime.fnInstance Bodies.languageTrueConstant.value =
      .ok Bodies.languageTrueConstant.value := by
    rw [Bodies.language_runtime_literal.2.1]
    exact runtime_normalization
  have literal := Bodies.language_runtime_literal.2.1
  simp_language_constant

theorem parent_false_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = Bodies.checkLanguage.loaded.identity.index)
    (location : frame.location = .mir ⟨3,0⟩)
    (fnInstance : frame.functionInstance = Bodies.checkLanguage.fnInstance) :
    CompilerConstantMachine.evalAtBound PreparedReflection.actual.compiler.constantBinding
      parentFalseSite functions arithmetic externStatic MemoryErrors.constant
      Bodies.languageFalseConstant (some RootCompilerFacts.boolLayout) none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (Scalar.fromBool false)),RootCompilerFacts.boolLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  have compatible := RootCompilerFacts.constant_binding_compatible source
  have norm : normalizationFromEvidence
      ((PreparedReflection.actual.compiler.constants.evidence.filter (·.site == parentFalseSite)).map (·.query))
      Bodies.checkLanguage.fnInstance Bodies.languageFalseConstant.value =
      .ok Bodies.languageFalseConstant.value := by
    rw [Bodies.language_parent_false_literal.2]
    exact parent_false_normalization
  have literal := Bodies.language_parent_false_literal.2
  simp_language_constant

theorem canonical_runtime_true_operand
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = Bodies.languageRuntime.loaded.identity.index)
    (location : frame.location = .mir ⟨0,0⟩)
    (fnInstance : frame.functionInstance = Bodies.languageRuntime.fnInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.rvalue "operand") (.Constant Bodies.languageTrueConstant)
      (some RootCompilerFacts.boolLayout) (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (.fromBool true)),RootCompilerFacts.boolLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  have site : CompilerOperandSites.current
      ((OperandPath.rvalue "operand").push (.field "constant")) state = .ok runtimeSite state := by
    simp [CompilerOperandSites.current, MachineHooks.currentFrame,
      state, Storage.withCurrent, Stack.currentFrame?, runtimeSite, bodyIndex, location,
      Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure,
      OperandPath.rvalue]
  have siteLit : CompilerOperandSites.current
      #[.field "kind", .field "rvalue", .field "operand", .field "constant"]
      (Storage.withCurrent framesBefore frame machine) =
      .ok runtimeSite (Storage.withCurrent framesBefore frame machine) := by
    simpa [OperandPath.rvalue, state] using site
  have result := runtime_true_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance
  change config.operands.constantAt ()
    ((OperandPath.rvalue "operand").push (.field "constant")) Bodies.languageTrueConstant
    (some RootCompilerFacts.boolLayout) state = _
  rw [constantAt]
  simpa [siteLit, state, config, OperandPath.rvalue, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using result

theorem canonical_parent_false_operand
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = Bodies.checkLanguage.loaded.identity.index)
    (location : frame.location = .mir ⟨3,0⟩)
    (fnInstance : frame.functionInstance = Bodies.checkLanguage.fnInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.rvalue "operand") (.Constant Bodies.languageFalseConstant)
      (some RootCompilerFacts.boolLayout) (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (.fromBool false)),RootCompilerFacts.boolLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  have site : CompilerOperandSites.current
      ((OperandPath.rvalue "operand").push (.field "constant")) state = .ok parentFalseSite state := by
    simp [CompilerOperandSites.current, MachineHooks.currentFrame,
      state, Storage.withCurrent, Stack.currentFrame?, parentFalseSite, bodyIndex, location,
      Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure,
      OperandPath.rvalue]
  have siteLit : CompilerOperandSites.current
      #[.field "kind", .field "rvalue", .field "operand", .field "constant"]
      (Storage.withCurrent framesBefore frame machine) =
      .ok parentFalseSite (Storage.withCurrent framesBefore frame machine) := by
    simpa [OperandPath.rvalue, state] using site
  have result := parent_false_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance
  change config.operands.constantAt ()
    ((OperandPath.rvalue "operand").push (.field "constant")) Bodies.languageFalseConstant
    (some RootCompilerFacts.boolLayout) state = _
  rw [constantAt]
  simpa [siteLit, state, config, OperandPath.rvalue, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using result

theorem canonical_return_place
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (layout : LocalLayout) (valid : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (cached : (frame.locals[0]'(by omega)).layout = some layout)
    (sized : layout.layout.isSized = true) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨0,#[]⟩ true (Storage.withCurrent framesBefore frame machine) =
      .ok (LocalPlaces.localRuntimePlace framesBefore.size frame 0 layout)
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
    simp [state, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push, Bind.bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure, Except.pure, Except.bind]
  have localPlace := LocalPlaces.localToPlace_cached hooks () frame 0 framesBefore.size layout state
    valid getFrame frameIndex cached sized
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨0,#[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size frame 0 layout) state
  have evaluated := LocalPlaces.evalPlace_local_empty projection () 0 frame framesBefore.size layout state localPlace check
  change PlaceDynamic.evalPlace projection () ⟨0,#[]⟩ true state = _
  exact evaluated

theorem unary_to_write
    (hooks : RvalueHooks Provenance (MachineHooks.State K User) Choice (RuntimePlace Provenance))
    (choice : Choice) (operator : UnOp) (operand : Operand) (dest : Place)
    (destValue : RuntimePlace Provenance) (source : OpTy Provenance)
    (input result : RvalueImmTy Provenance) (state : MachineHooks.State K User)
    (evalDest : hooks.evalPlace choice dest true state = .ok destValue state)
    (evalSource : hooks.evalOperandAt choice (OperandPath.rvalue "operand") operand
      (if operator.homogeneous then some (hooks.placeLayout destValue) else none) state = .ok source state)
    (readSource : hooks.readImmediate choice source state = .ok input state)
    (unary : hooks.unaryOp choice operator input state = .ok result state)
    (resultLayout : result.layout = hooks.placeLayout destValue) :
    evalRvalueIntoPlace hooks choice (.UnaryOp operator operand) dest state =
      hooks.writeImmediate choice result.imm destValue state := by
  simp_all [evalRvalueIntoPlace, Bind.bind, EStateM.bind, OperandPath.rvalue]
  simp_rvalue_assert
  simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem canonical_runtime_not_true_to_write
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (cached0 : (frame.locals[0]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (sized : RootCompilerFacts.boolLayout.layout.isSized = true)
    (readable : ∃ primitive range, RootCompilerFacts.boolLayout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range)))
    (bodyIndex : frame.bodyIdentity.index = Bodies.languageRuntime.loaded.identity.index)
    (location : frame.location = .mir ⟨0,0⟩)
    (fnInstance : frame.functionInstance = Bodies.languageRuntime.fnInstance)
    (classification : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).classify
      () RootCompilerFacts.boolLayout.ty = pure .boolean)
    (boolQuery : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).boolLayout
      () = pure RootCompilerFacts.boolLayout) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      (.UnaryOp .Not (.Constant Bodies.languageTrueConstant)) ⟨0,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).writeImmediate
      () (.scalar (.fromBool false)) (LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.boolLayout)
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let hooks := ExecutionMachine.rvalueHooks config limits
  let dest := LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.boolLayout
  let sourceOp : OpTy Provenance := ⟨.immediate (.scalar (.fromBool true)), RootCompilerFacts.boolLayout⟩
  let input : RvalueImmTy Provenance := ⟨.scalar (.fromBool true),RootCompilerFacts.boolLayout⟩
  let result : RvalueImmTy Provenance := ⟨.scalar (.fromBool false),RootCompilerFacts.boolLayout⟩
  have destination := canonical_return_place options limits remaining span debugOff framesBefore frame machine
    RootCompilerFacts.boolLayout valid0 cached0 sized
  have operand := canonical_runtime_true_operand options limits remaining span source debugOff framesBefore frame machine bodyIndex location fnInstance
  have read := RootLocalStages.canonical_read_scalar options limits remaining span state (.fromBool true) RootCompilerFacts.boolLayout readable
  have operation := CopyPreconditions.scalar_bool_not
    (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)) ()
    RootCompilerFacts.boolLayout RootCompilerFacts.boolLayout true classification boolQuery
  have unary : hooks.unaryOp () .Not input state = .ok result state := by
    change ScalarOps.unary (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
      () .Not (ScalarOperations.boolImmediate true RootCompilerFacts.boolLayout) state = _
    exact congrFun operation state
  apply unary_to_write hooks () .Not (.Constant Bodies.languageTrueConstant) ⟨0,#[]⟩ dest sourceOp input result state
  · exact destination
  · simpa [sourceOp, hooks, config, dest, ExecutionMachine.rvalueHooks,
      ExecutionMachine.operandHooks, ExecutionMachine.withValidation, UnOp.homogeneous, LocalPlaces.localRuntimePlace] using operand
  · exact read
  · exact unary
  · rfl

theorem use_to_copy
    (hooks : RvalueHooks Provenance (MachineHooks.State K User) Choice (RuntimePlace Provenance))
    (choice : Choice) (operand : MIR.Operand) (dest : Place) (destValue : RuntimePlace Provenance)
    (sourceOp : OpTy Provenance) (state : MachineHooks.State K User)
    (evalDest : hooks.evalPlace choice dest true state = .ok destValue state)
    (evalSource : hooks.evalOperandAt choice (OperandPath.rvalue "operand") operand
      (some (hooks.placeLayout destValue)) state = .ok sourceOp state) :
    evalRvalueIntoPlace hooks choice (.Use operand .Yes) dest state =
      hooks.withRetagMode choice .Default (hooks.copyOp choice sourceOp destValue) state := by
  simp_all [evalRvalueIntoPlace, Bind.bind, EStateM.bind]

theorem canonical_parent_false_to_copy
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (cached0 : (frame.locals[0]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (sized : RootCompilerFacts.boolLayout.layout.isSized = true)
    (bodyIndex : frame.bodyIdentity.index = Bodies.checkLanguage.loaded.identity.index)
    (location : frame.location = .mir ⟨3,0⟩)
    (fnInstance : frame.functionInstance = Bodies.checkLanguage.fnInstance) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      (.Use (.Constant Bodies.languageFalseConstant) .Yes) ⟨0,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).withRetagMode
      () .Default ((ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).copyOp ()
        ⟨.immediate (.scalar (.fromBool false)),RootCompilerFacts.boolLayout⟩
        (LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.boolLayout))
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let hooks := ExecutionMachine.rvalueHooks config limits
  let dest := LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.boolLayout
  let sourceOp : OpTy Provenance := ⟨.immediate (.scalar (.fromBool false)),RootCompilerFacts.boolLayout⟩
  have destination := canonical_return_place options limits remaining span debugOff framesBefore frame machine
    RootCompilerFacts.boolLayout valid0 cached0 sized
  have operand := canonical_parent_false_operand options limits remaining span source debugOff framesBefore frame machine bodyIndex location fnInstance
  have evalDest : hooks.evalPlace () ⟨0,#[]⟩ true state = .ok dest state := destination
  have evalSource : hooks.evalOperandAt () (OperandPath.rvalue "operand") (.Constant Bodies.languageFalseConstant)
      (some (hooks.placeLayout dest)) state = .ok sourceOp state := by
    simpa [sourceOp, hooks, config, dest, ExecutionMachine.rvalueHooks,
      ExecutionMachine.operandHooks, ExecutionMachine.withValidation, LocalPlaces.localRuntimePlace] using operand
  exact use_to_copy hooks () (.Constant Bodies.languageFalseConstant) ⟨0,#[]⟩ dest sourceOp state evalDest evalSource

theorem canonical_false_local_switch
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId matched otherwise : Nat) (terminator : Terminator)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (.fromBool false))))
    (cached : frame.locals[localId].layout = some RootCompilerFacts.boolLayout)
    (sized : RootCompilerFacts.boolLayout.layout.backendRepr.isUnsized = false)
    (readable : ∃ primitive range, RootCompilerFacts.boolLayout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range)))
    (noClocks : frame.extra.dataRace = none)
    (validationGetter : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).compiler.validationInProgress
        (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine))
    (kind : terminator.kind = .SwitchInt (.Move ⟨localId,#[]⟩) ⟨#[.Case 0 matched],otherwise⟩)
    (classification : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).classify
      () RootCompilerFacts.boolLayout.ty = pure .boolean)
    (boolQuery : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).boolLayout
      () = pure RootCompilerFacts.boolLayout)
    (width : RootCompilerFacts.boolLayout.layout.size = Size.ofBytes 1) :
    (ExecutionMachine.stepHooks (PreparedContracts.actualConfig options () remaining span) limits).terminator
      () terminator (Storage.withCurrent framesBefore frame machine) =
    ControlFlow.goToBlock matched (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
  let op : OpTy Provenance := ⟨.immediate (.scalar (.fromBool false)),RootCompilerFacts.boolLayout⟩
  have localRead := LocalOperands.cached_immediate hooks () framesBefore frame machine localId
    (.scalar (.fromBool false)) RootCompilerFacts.boolLayout none valid live cached sized noClocks false validationGetter
  have typeCheck := RootLocalStages.operand_check_skipped options limits () remaining span debugOff
    (OperandDispatch.wholeLocal localId) op state
  have operand := OperandDispatch.evalOperandAt_move_wholeLocal hooks ()
    (OperandPath.instruction "discriminant") localId none state state op localRead typeCheck
  have operand' : OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
      (.Move ⟨localId,#[]⟩) none state = .ok op state := by
    simpa only [OperandDispatch.wholeLocal] using operand
  have scalarRead := RootLocalStages.canonical_read_scalar options limits remaining span state
    (.fromBool false) RootCompilerFacts.boolLayout readable
  have read : MachineHooks.run (do
      PlaceMachine.readImmediate (ExecutionMachine.withValidation config limits).access
        (← OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant") (.Move ⟨localId,#[]⟩) none)) state =
      (state,.ok (ScalarOperations.boolImmediate false RootCompilerFacts.boolLayout)) := by
    change MachineHooks.run (do
      let value ← OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant") (.Move ⟨localId,#[]⟩) none
      (ExecutionMachine.rvalueHooks config limits).readImmediate () value) state = _
    simp only [MachineHooks.run, Call.run, Bind.bind, EStateM.bind]
    rw [operand']
    exact congrArg (fun result => match result with
      | .ok value after => (after,Except.ok value)
      | .error error after => (after,Except.error error)) scalarRead
  have effect := BoolSwitch.dispatch config limits () terminator (.Move ⟨localId,#[]⟩) matched otherwise
    state state RootCompilerFacts.boolLayout false kind read classification boolQuery width
  exact effect

#print axioms canonical_parent_false_to_copy
#print axioms canonical_false_local_switch
#print axioms canonical_runtime_not_true_to_write
#print axioms canonical_runtime_true_operand
#print axioms runtime_true_eval_at_bound
#print axioms parent_false_eval_at_bound
end
end DuplicatePrefix.CopyLanguageGuard
