import duplicate_prefix.RootBlock0
import duplicate_prefix.BoolSwitch
import duplicate_prefix.RootScalarQueries
import duplicate_prefix.SourceControl
import duplicate_prefix.RootLocalStages
import duplicate_prefix.LocalOperands
import duplicate_prefix.OperandDispatch
import duplicate_prefix.StepFacts
import duplicate_prefix.Storage
import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.ActualScalarCopy
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.RvalueDispatch

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootZeroSwitch
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter

def terminatorKindAt (body : MIR.Body) (block : Nat) : Option TerminatorKind :=
  (body.basicBlocks[block]?).map (fun bb => bb.terminator.kind)

theorem root_zero_switch_shape :
    terminatorKindAt RootBody.reflected.body.body 0 =
      some (.SwitchInt (.Move ⟨4, #[]⟩) ⟨#[.Case 0 2], 1⟩) := by
  rfl

def trueConstant : ConstOperand := ⟨⟨4⟩, none, .Val (.Scalar (.Int 1 1)) 0⟩

noncomputable def trueConstantSite : CompilerConstantQueries.Site :=
  ⟨RootBody.reflected.body.identity.index, ⟨1, 1⟩,
    #[.field "kind", .field "rvalue", .field "operand", .field "constant"]⟩

noncomputable def trueConstantEvidence : Array CompilerConstantEvidence :=
  (PreparedReflection.actual.compiler.constants.evidence.filter
    (·.site == trueConstantSite)).map (·.query)

theorem true_constant_normalization :
    normalizationFromEvidence trueConstantEvidence RootBody.reflected.functionInstance
      (.Val (.Scalar (.Int 1 1)) 0) = .ok (.Val (.Scalar (.Int 1 1)) 0) := by
  with_unfolding_all rfl

theorem true_constant_evaluation :
    evaluationFromEvidence trueConstantEvidence RootBody.reflected.functionInstance
      (.Val (.Scalar (.Int 1 1)) 0) ⟨4⟩ = .ok (.Scalar (.Int 1 1)) := by
  with_unfolding_all rfl

open Lean Elab Tactic in
elab "simp_root_true_constant" : tactic => do
  let env ← getEnv
  let found := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith "Miri.Interpreter.constantType"
    then some (mkIdent name) else none
  let names := found.toArray
  evalTactic (← `(tactic| simp_all (config := {maxSteps := 1000000}) [
    CompilerConstantMachine.evalAtBound, ConstantMachine.fromCompiler,
    ConstantMachine.evalOperandWithLayout, evalConstOperandWithLayout,
    evalMirConstantWithLayout, constValueToOpWithLayout,
    ConstantQueries.valueQueries, MachineHooks.currentFrame,
    Storage.withCurrent, Stack.currentFrame?, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Except.bind, Except.pure, trueConstant, trueConstantSite, trueConstantEvidence,
    true_constant_normalization, true_constant_evaluation,
    CopyLanguageGuard.scalar_true, $[$names:ident],*]))

theorem true_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨1,1⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerConstantMachine.evalAtBound PreparedReflection.actual.compiler.constantBinding
      trueConstantSite functions arithmetic externStatic MemoryErrors.constant
      trueConstant (some RootCompilerFacts.boolLayout) none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (Scalar.fromBool true)), RootCompilerFacts.boolLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  have compatible := RootCompilerFacts.constant_binding_compatible source
  have norm : normalizationFromEvidence trueConstantEvidence
      RootBody.reflected.functionInstance (.Val (.Scalar (.Int 1 1)) 0) =
      .ok (.Val (.Scalar (.Int 1 1)) 0) := true_constant_normalization
  simp_root_true_constant

theorem canonical_true_operand
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨1,1⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.rvalue "operand") (.Constant trueConstant)
      (some RootCompilerFacts.boolLayout) (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (Scalar.fromBool true)), RootCompilerFacts.boolLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  have site : CompilerOperandSites.current
      ((OperandPath.rvalue "operand").push (.field "constant")) state =
      .ok trueConstantSite state := by
    simp [CompilerOperandSites.current, MachineHooks.currentFrame,
      state, Storage.withCurrent, Stack.currentFrame?, Array.back?_push, trueConstantSite,
      bodyIndex, location, bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, pure, EStateM.pure,
      OperandPath.rvalue]
  have siteLit : CompilerOperandSites.current
      #[.field "kind", .field "rvalue", .field "operand", .field "constant"] state =
      .ok trueConstantSite state := by
    simpa [OperandPath.rvalue] using site
  have result := true_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance
  change config.operands.constantAt ()
      ((OperandPath.rvalue "operand").push (.field "constant"))
      trueConstant (some RootCompilerFacts.boolLayout) state = _
  rw [constantAt]
  simpa [siteLit, state, config, trueConstant, OperandPath.rvalue,
    bind, EStateM.bind, pure, EStateM.pure] using result

def cacheReturnLayout (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.boolLayout valid0

def trueReturnFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size) :=
  let cached := cacheReturnLayout frame valid0
  let newSlot : LocalState Provenance LocalLayout :=
    {value := .live (.immediate (.scalar (.fromBool true))),
      layout := some RootCompilerFacts.boolLayout}
  let validCached : (0 : MIR.LocalId) < cached.locals.size := by
    simpa [cached, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using valid0
  let updatedLocals := cached.locals.set 0 newSlot validCached
  {cached with locals := updatedLocals}

theorem canonical_return_place_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨0, #[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size
      (cacheReturnLayout frame valid0) 0 RootCompilerFacts.boolLayout)
      (Storage.withCurrent framesBefore (cacheReturnLayout frame valid0) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := cacheReturnLayout frame valid0
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
    exact CallEntryFacts.root_compute_local0 framesBefore frame machine body identity callee
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
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine
    0 framesBefore.size RootCompilerFacts.boolLayout valid0 uncached0 sized
    resolve getFrame frameIndex setCached getCached indexCached
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨0, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 0
      RootCompilerFacts.boolLayout) updated
  have evaluated := LocalPlaces.evalPlace_local_empty_uncached projection () 0 framesBefore
    frame machine framesBefore.size RootCompilerFacts.boolLayout valid0
    (state := state) (updated := updated) localPlace check
  change PlaceDynamic.evalPlace projection () ⟨0, #[]⟩ true state = _
  exact evaluated

theorem actual_true_return_assignment
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨1,1⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (uninit0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = TreeBorrows.RetagPolicy.RetagMode.Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks
        (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Constant trueConstant) .Yes) ⟨0,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore (trueReturnFrame frame valid0) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := cacheReturnLayout frame valid0
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 0 RootCompilerFacts.boolLayout
  let sourceOp : OpTy Provenance := ⟨.immediate (.scalar (.fromBool true)), RootCompilerFacts.boolLayout⟩
  have evalDest := canonical_return_place_uncached options limits (remaining+1) span debugOff
    framesBefore frame machine valid0 uncached0 body identity callee
  have valid0Cached : (0 : MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using valid0
  have cached0 : (cachedFrame.locals[0]'(by omega)).layout = some RootCompilerFacts.boolLayout := by
    simp [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout]
  have uninit0Cached : (cachedFrame.locals[0]'(by omega)).value = .live (.immediate .uninit) := by
    have setBound : 0 < (frame.locals.set 0
        {value := frame.locals[0].value, layout := some RootCompilerFacts.boolLayout} valid0).size := by
      simpa only [Array.size_set] using valid0
    change ((frame.locals.set 0
      {value := frame.locals[0].value, layout := some RootCompilerFacts.boolLayout} valid0)[0]'setBound).value = _
    rw [Array.getElem_set_self]
    exact uninit0
  have noClocksCached : cachedFrame.extra.dataRace = none := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using noClocks
  have cachedIdentity : cachedFrame.bodyIdentity = RootBody.reflected.body.identity := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using identity
  have cachedBodyIndex : cachedFrame.bodyIdentity.index = RootBody.reflected.body.identity.index := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using
      congrArg (fun value : BodyIdentity => value.index) identity
  have cachedLocation : cachedFrame.location = .mir ⟨1,1⟩ := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using location
  have operand := canonical_true_operand options limits (remaining+1) span source debugOff
    framesBefore cachedFrame machine cachedBodyIndex cachedLocation callee
  have evalSource : hooks.evalOperandAt () (OperandPath.rvalue "operand")
      (.Constant trueConstant) (some (hooks.placeLayout dest)) state1 = .ok sourceOp state1 := by
    change OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)) ()
      (OperandPath.rvalue "operand") (.Constant trueConstant)
      (some RootCompilerFacts.boolLayout) state1 = .ok sourceOp state1
    simpa [sourceOp, dest, LocalPlaces.localRuntimePlace] using operand
  have writer := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff fuel fuelEq
    framesBefore cachedFrame machine 0 .uninit true valid0Cached uninit0Cached cached0
    noClocksCached ghostFalse shallow
  let afterFrame := trueReturnFrame frame valid0
  let after := Storage.withCurrent framesBefore afterFrame machine
  have outputFrameEq : trueReturnFrame frame valid0 =
      {cachedFrame with locals := (cachedFrame.locals.set 0
        {value := .live (.immediate (.scalar (.fromBool true))),
         layout := cachedFrame.locals[0].layout} valid0Cached)} := by
    simp [trueReturnFrame, cacheReturnLayout, cachedFrame, LocalPlaces.cachePlaceLayout,
      Array.set_set]
  have copyBody : hooks.copyOp () sourceOp dest state1 = .ok () after := by
    obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists
      RootCompilerFacts.boolLayout RootGenericBoolWrite.bool_initialized
    have actualCopy := ActualScalarCopy.actual_copy_scalar options limits (remaining+1) span debugOff
      RootCompilerFacts.boolLayout (.scalar (.fromBool true)) dest rfl
      (.Initialized (value := primitive) (validRange := range)) repr RootGenericBoolWrite.bool_sized
    have actualCopyFunction : hooks.copyOp () sourceOp dest =
        hooks.writeImmediate () (.scalar (.fromBool true)) dest := by
      change (ExecutionMachine.rvalueHooks config limits).copyOp ()
          ⟨.immediate (.scalar (.fromBool true)), RootCompilerFacts.boolLayout⟩ dest =
        (ExecutionMachine.rvalueHooks config limits).writeImmediate () (.scalar (.fromBool true)) dest
      exact actualCopy
    have actualCopy' : hooks.copyOp () sourceOp dest state1 =
        hooks.writeImmediate () (.scalar (.fromBool true)) dest state1 :=
      congrArg (fun action => action state1) actualCopyFunction
    have writer' : hooks.writeImmediate () (.scalar (.fromBool true)) dest state1 = .ok () after := by
      change hooks.writeImmediate () (.scalar (.fromBool true))
        (LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 0 RootCompilerFacts.boolLayout)
        (Storage.withCurrent framesBefore cachedFrame machine) =
        .ok () (Storage.withCurrent framesBefore (trueReturnFrame frame valid0) machine)
      rw [outputFrameEq]
      exact writer
    exact actualCopy'.trans writer'
  have trackerAt : state1.machine.borrowTracker = some tracker := by
    simpa [state1, Storage.withCurrent] using tracked
  have trackerAfter : after.machine.borrowTracker = some tracker := by
    simpa [after, afterFrame, trueReturnFrame, cachedFrame, cacheReturnLayout,
      LocalPlaces.cachePlaceLayout, Storage.withCurrent] using tracked
  have scopedCopy : hooks.withRetagMode () TreeBorrows.RetagPolicy.RetagMode.Default
      (hooks.copyOp () sourceOp dest) state1 = .ok () after := by
    change MachineHooks.withRetagMode TreeBorrows.RetagPolicy.RetagMode.Default
      (hooks.copyOp () sourceOp dest) state1 = .ok () after
    exact ScalarCopyStage.with_retag_mode_existing TreeBorrows.RetagPolicy.RetagMode.Default
      (hooks.copyOp () sourceOp dest) state1 after tracker () trackerAt defaultMode
      trackerAfter copyBody
  have effect := RvalueDispatch.use_operand hooks () (.Constant trueConstant) .Yes ⟨0,#[]⟩
    dest sourceOp state0 state1 state1 after evalDest evalSource scopedCopy
  exact effect

#print axioms actual_true_return_assignment

theorem root_zero_return_prep_shape :
    RootBody.statementKindAt RootBody.reflected.body.body 1 0 = some (.StorageDead 5) ∧
    RootBody.statementKindAt RootBody.reflected.body.body 1 1 =
      some (.Assign ⟨0,#[]⟩ (.Use (.Constant trueConstant) .Yes)) ∧
    RootBody.statementKindAt RootBody.reflected.body.body 1 2 = some (.StorageDead 4) ∧
    RootBody.statementKindAt RootBody.reflected.body.body 1 3 = some (.StorageDead 3) ∧
    terminatorKindAt RootBody.reflected.body.body 1 = some (.Goto 10 #[]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

#print axioms root_zero_return_prep_shape
#print axioms true_constant_normalization
#print axioms true_constant_evaluation
#print axioms true_eval_at_bound
#print axioms canonical_true_operand

theorem actual_root_zero_switch_step
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (n : UInt64)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨0,5⟩)
    (size : frame.locals.size = 25)
    (valid4 : (4 : MIR.LocalId) < frame.locals.size)
    (live4 : (frame.locals[4]'(by omega)).value = .live
      (.immediate (.scalar (.fromBool (n == 0)))))
    (cached4 : (frame.locals[4]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (checkedArithmetic : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (gcDisabled : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixedScheduling : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ after,
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
        (after, .ok true) ∧
      after.stack.currentFrame?.map (·.location) = some
        (.mir ⟨if n == 0 then 1 else 2, 0⟩) ∧
      after.machine.threads.fixedScheduling = machine.threads.fixedScheduling := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent framesBefore frame machine
  let accounted := SourceControl.accounted config.terminators before
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
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
  have noGc := gcDisabled
  have fixed := fixedScheduling
  have unchecked := checkedArithmetic
  have accounting := SourceControl.before_terminator config limits () before getSet setSet unchecked noGc fixed
  have accountedGhost : accounted.machine.user.payload.ghost = false := by
    have ghostEq : (config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user).payload.ghost =
        machine.user.payload.ghost := by
      rw [fields.terminators]
      rfl
    change (config.terminators.setControl
      (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user).payload.ghost = false
    rw [ghostEq, ghostFalse]
  have validGetter : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)).compiler.validationInProgress accounted =
      .ok false accounted := by
    change config.compiler.validationInProgress accounted = _
    rw [fields.compilerValidationInProgress]
    simp [ValidityMachine.validationInProgress, accountedGhost,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have blockExists : ∃ block, RootBody.reflected.body.body.basicBlocks[0]? = some block ∧
      block.terminator.kind = .SwitchInt (.Move ⟨4,#[]⟩) ⟨#[.Case 0 2],1⟩ := by
    have shape := root_zero_switch_shape
    cases h : RootBody.reflected.body.body.basicBlocks[0]? with
    | none => simp [terminatorKindAt, h] at shape
    | some block =>
      refine ⟨block, rfl, ?_⟩
      simpa [terminatorKindAt, h] using shape
  obtain ⟨block, blockEq, reflectedKind⟩ := blockExists
  have blockAt : frame.body.basicBlocks[0]? = some block := by
    rw [body]
    exact blockEq
  have kind : block.terminator.kind = .SwitchInt (.Move ⟨4,#[]⟩) ⟨#[.Case 0 2],1⟩ := by
    exact reflectedKind
  have noStatement : block.statements[5]? = none := by
    have reflectedNoStatement : RootBody.reflected.body.body.basicBlocks[0]?.bind
        (fun bb => bb.statements[5]?) = none := by
      rfl
    rw [blockEq] at reflectedNoStatement
    exact reflectedNoStatement
  have current : before.stack.currentFrame? = some frame := by
    simp [before, Storage.withCurrent, Stack.currentFrame?]
  have sized : RootCompilerFacts.boolLayout.layout.backendRepr.isUnsized = false := by decide +kernel
  have initialized : CopyCompilerFacts.initializedScalar RootCompilerFacts.boolLayout = true := by decide +kernel
  obtain ⟨primitive, range, readable⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.boolLayout initialized
  let scalar : Scalar Provenance := Scalar.fromBool (n == 0)
  let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
  let op : OpTy Provenance := ⟨.immediate (.scalar scalar), RootCompilerFacts.boolLayout⟩
  have accountedFrame : accounted = Storage.withCurrent framesBefore frame accounted.machine := by
    rfl
  have getterLocal : hooks.compiler.validationInProgress
      (Storage.withCurrent framesBefore frame accounted.machine) =
      .ok false (Storage.withCurrent framesBefore frame accounted.machine) := by
    change hooks.compiler.validationInProgress accounted = .ok false accounted
    exact validGetter
  have localRead := LocalOperands.cached_immediate hooks () framesBefore frame accounted.machine 4
    (.scalar scalar) RootCompilerFacts.boolLayout none valid4 live4 cached4 sized noClocks
    false getterLocal
  have typeCheck := RootLocalStages.operand_check_skipped options limits () (remaining+1) span
    debugOff (OperandDispatch.wholeLocal 4) op accounted
  have operand := OperandDispatch.evalOperandAt_move_wholeLocal hooks ()
    (OperandPath.instruction "discriminant") 4 none accounted accounted op localRead typeCheck
  have operand' : OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
      (.Move ⟨4,#[]⟩) none accounted = .ok op accounted := by
    simpa only [OperandDispatch.wholeLocal] using operand
  have scalarRead := RootLocalStages.canonical_read_scalar options limits (remaining+1) span
    accounted scalar RootCompilerFacts.boolLayout ⟨primitive, range, readable⟩
  have read : MachineHooks.run (do
      PlaceMachine.readImmediate (ExecutionMachine.withValidation config limits).access
        (← OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
          (.Move ⟨4,#[]⟩) none)) accounted =
      (accounted,.ok (ScalarOperations.boolImmediate (n == 0) RootCompilerFacts.boolLayout)) := by
    change MachineHooks.run (do
      let value ← OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
        (.Move ⟨4,#[]⟩) none
      (ExecutionMachine.rvalueHooks config limits).readImmediate () value) accounted = _
    simp only [MachineHooks.run, Call.run, Bind.bind, EStateM.bind]
    rw [operand']
    exact congrArg (fun result => match result with
      | .ok value after => (after,Except.ok value)
      | .error error after => (after,Except.error error)) scalarRead
  have classify := RootScalarQueries.bool_classification options (remaining+1) span limits
  have boolLayout := RootScalarQueries.bool_layout options (remaining+1) span limits
  have width : RootCompilerFacts.boolLayout.layout.size = Size.ofBytes 1 := by decide +kernel
  have dispatch := BoolSwitch.dispatch config limits () block.terminator (.Move ⟨4,#[]⟩)
    2 1 accounted accounted RootCompilerFacts.boolLayout (n == 0) kind read classify boolLayout width
  have branch : (if (n == 0) == false then 2 else 1) = (if n == 0 then 1 else 2) := by
    by_cases h : n == 0 <;> simp [h]
  have effect : (ExecutionMachine.stepHooks config limits).terminator () block.terminator accounted =
      ControlFlow.goToBlock (if n == 0 then 1 else 2) accounted := by
    simpa [branch] using dispatch
  let afterFrame := {frame with location := .mir ⟨if n == 0 then 1 else 2, 0⟩}
  let after := Storage.withCurrent framesBefore afterFrame accounted.machine
  have goToBlockEq : ControlFlow.goToBlock (if n == 0 then 1 else 2) accounted = (after,.ok ()) := by
    simp [ControlFlow.goToBlock, ControlFlow.setLocation, after, afterFrame,
      accounted, SourceControl.accounted, before, Storage.withCurrent, Stack.currentFrame?]
  have effect' : (ExecutionMachine.stepHooks config limits).terminator () block.terminator accounted = (after,.ok ()) := by
    rw [effect, goToBlockEq]
  have step := StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) () before accounted after
    frame ⟨0,5⟩ block current location blockAt noStatement accounting effect'
  have sourceStep : ExecutionMachine.step config limits () before = (after,.ok true) := by
    simpa [ExecutionMachine.step] using step
  refine ⟨after, sourceStep, ?_, ?_⟩
  · simp [after, afterFrame, Storage.withCurrent, Stack.currentFrame?]
  · change before.machine.threads.fixedScheduling = machine.threads.fixedScheduling
    rfl

#print axioms actual_root_zero_switch_step

end DuplicatePrefix.RootZeroSwitch
