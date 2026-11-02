import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.ActualScalarCopy
import duplicate_prefix.RvalueDispatch
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.ParentFalseAssignment
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
def cacheReturnLayout (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.boolLayout valid0

def falseReturnFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size) :=
  let cached := cacheReturnLayout frame valid0
  let newSlot : LocalState Provenance LocalLayout :=
    {value := .live (.immediate (.scalar (.fromBool false))),
      layout := some RootCompilerFacts.boolLayout}
  let validCached : (0 : MIR.LocalId) < cached.locals.size := by
    simpa [cached, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using valid0
  let updatedLocals := cached.locals.set 0 newSlot validCached
  {cached with locals := updatedLocals}

theorem language_local0_normalized (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 0 = .ok 0 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl

theorem language_compute_local0
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 0
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.boolLayout (Storage.withCurrent framesBefore frame machine) := by
  have normalized := language_local0_normalized frame body identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 0 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent framesBefore frame machine)
    | .error error => EStateM.Result.error
        (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent framesBefore frame machine)) = _
  rw [RootCompilerFacts.bool_layout_eq]
  rfl

theorem canonical_return_place_uncached [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨0,#[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size (cacheReturnLayout frame valid0) 0 RootCompilerFacts.boolLayout)
      (Storage.withCurrent framesBefore (cacheReturnLayout frame valid0) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := cacheReturnLayout frame valid0
  let updated := Storage.withCurrent framesBefore updatedFrame machine
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let hooks := projection.place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : hooks.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = _
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  have frameIndex : hooks.frameIndex state = .ok framesBefore.size state := by
    change config.projection.place.frameIndex state = _
    rw [fields.projectionFrameIndex]
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure,Except.pure,Except.bind]
  have resolve : hooks.resolveLayout () 0 state = .ok RootCompilerFacts.boolLayout state := by
    change config.projection.place.resolveLayout () 0 state = _
    rw [fields.projectionResolveLayout,fields.layout]
    exact language_compute_local0 framesBefore frame machine body identity callee
  have setCached : hooks.setFrame updatedFrame state = .ok () updated := by
    change config.projection.place.setFrame updatedFrame state = _
    rw [fields.projectionSetFrame]
    exact Storage.set_current_frame framesBefore frame updatedFrame machine
  have getCached : hooks.getFrame updated = .ok updatedFrame updated := by
    change config.projection.place.getFrame updated = _
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore updatedFrame machine
  have indexCached : hooks.frameIndex updated = .ok framesBefore.size updated := by
    change config.projection.place.frameIndex updated = _
    rw [fields.projectionFrameIndex]
    simp [updated,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure,Except.pure,Except.bind]
  have sized : RootCompilerFacts.boolLayout.layout.isSized = true := by decide +kernel
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine 0
    framesBefore.size RootCompilerFacts.boolLayout valid0 uncached0 sized resolve getFrame frameIndex
    setCached getCached indexCached
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨0,#[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 0 RootCompilerFacts.boolLayout) updated
  exact LocalPlaces.evalPlace_local_empty_uncached projection () 0 framesBefore frame machine
    framesBefore.size RootCompilerFacts.boolLayout valid0 (state := state) (updated := updated) localPlace check

theorem evaluate
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨3,0⟩)
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
      (.Use (.Constant CopyPreconditions.Bodies.languageFalseConstant) .Yes) ⟨0,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore (falseReturnFrame frame valid0) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := cacheReturnLayout frame valid0
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 0 RootCompilerFacts.boolLayout
  let sourceOp : OpTy Provenance := ⟨.immediate (.scalar (.fromBool false)), RootCompilerFacts.boolLayout⟩
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
  have cachedIdentity : cachedFrame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using identity
  have cachedBodyIndex : cachedFrame.bodyIdentity.index = CopyPreconditions.Bodies.checkLanguage.loaded.identity.index := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using
      congrArg (fun value : BodyIdentity => value.index) identity
  have cachedLocation : cachedFrame.location = .mir ⟨3,0⟩ := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using location
  have operand := CopyLanguageGuard.canonical_parent_false_operand options limits (remaining+1) span source debugOff
    framesBefore cachedFrame machine cachedBodyIndex cachedLocation callee
  have evalSource : hooks.evalOperandAt () (OperandPath.rvalue "operand")
      (.Constant CopyPreconditions.Bodies.languageFalseConstant) (some (hooks.placeLayout dest)) state1 = .ok sourceOp state1 := by
    change OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)) ()
      (OperandPath.rvalue "operand") (.Constant CopyPreconditions.Bodies.languageFalseConstant)
      (some RootCompilerFacts.boolLayout) state1 = .ok sourceOp state1
    exact operand
  have writer := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff fuel fuelEq
    framesBefore cachedFrame machine 0 .uninit false valid0Cached uninit0Cached cached0
    noClocksCached ghostFalse shallow
  let afterFrame := falseReturnFrame frame valid0
  let after := Storage.withCurrent framesBefore afterFrame machine
  have outputFrameEq : falseReturnFrame frame valid0 =
      {cachedFrame with locals := (cachedFrame.locals.set 0
        {value := .live (.immediate (.scalar (.fromBool false))),
         layout := cachedFrame.locals[0].layout} valid0Cached)} := by
    simp [falseReturnFrame, cacheReturnLayout, cachedFrame, LocalPlaces.cachePlaceLayout,
      Array.set_set]
  have copyBody : hooks.copyOp () sourceOp dest state1 = .ok () after := by
    obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists
      RootCompilerFacts.boolLayout RootGenericBoolWrite.bool_initialized
    have actualCopy := ActualScalarCopy.actual_copy_scalar options limits (remaining+1) span debugOff
      RootCompilerFacts.boolLayout (.scalar (.fromBool false)) dest rfl
      (.Initialized (value := primitive) (validRange := range)) repr RootGenericBoolWrite.bool_sized
    have actualCopyFunction : hooks.copyOp () sourceOp dest =
        hooks.writeImmediate () (.scalar (.fromBool false)) dest := by
      change (ExecutionMachine.rvalueHooks config limits).copyOp ()
          ⟨.immediate (.scalar (.fromBool false)), RootCompilerFacts.boolLayout⟩ dest =
        (ExecutionMachine.rvalueHooks config limits).writeImmediate () (.scalar (.fromBool false)) dest
      exact actualCopy
    have actualCopy' : hooks.copyOp () sourceOp dest state1 =
        hooks.writeImmediate () (.scalar (.fromBool false)) dest state1 :=
      congrArg (fun action => action state1) actualCopyFunction
    have writer' : hooks.writeImmediate () (.scalar (.fromBool false)) dest state1 = .ok () after := by
      change hooks.writeImmediate () (.scalar (.fromBool false))
        (LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 0 RootCompilerFacts.boolLayout)
        (Storage.withCurrent framesBefore cachedFrame machine) =
        .ok () (Storage.withCurrent framesBefore (falseReturnFrame frame valid0) machine)
      rw [outputFrameEq]
      exact writer
    exact actualCopy'.trans writer'
  have trackerAt : state1.machine.borrowTracker = some tracker := by
    simpa [state1, Storage.withCurrent] using tracked
  have trackerAfter : after.machine.borrowTracker = some tracker := by
    simpa [after, afterFrame, falseReturnFrame, cachedFrame, cacheReturnLayout,
      LocalPlaces.cachePlaceLayout, Storage.withCurrent] using tracked
  have scopedCopy : hooks.withRetagMode () TreeBorrows.RetagPolicy.RetagMode.Default
      (hooks.copyOp () sourceOp dest) state1 = .ok () after := by
    change MachineHooks.withRetagMode TreeBorrows.RetagPolicy.RetagMode.Default
      (hooks.copyOp () sourceOp dest) state1 = .ok () after
    exact ScalarCopyStage.with_retag_mode_existing TreeBorrows.RetagPolicy.RetagMode.Default
      (hooks.copyOp () sourceOp dest) state1 after tracker () trackerAt defaultMode
      trackerAfter copyBody
  have effect := RvalueDispatch.use_operand hooks () (.Constant CopyPreconditions.Bodies.languageFalseConstant) .Yes ⟨0,#[]⟩
    dest sourceOp state0 state1 state1 after evalDest evalSource scopedCopy
  exact effect

theorem source_statement :
    ∃ block statement,
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[3]? = some block ∧
      block.statements[0]? = some statement ∧
      statement.kind = .Assign ⟨0,#[]⟩
        (.Use (.Constant CopyPreconditions.Bodies.languageFalseConstant) .Yes) := by
  have shape := CopyPreconditions.Bodies.language_parent_false_literal.1
  cases blockEq : CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[3]? with
  | none => simp [CopyPreconditions.Bodies.statementKindAt,blockEq] at shape
  | some block =>
    cases statementEq : block.statements[0]? with
    | none => simp [CopyPreconditions.Bodies.statementKindAt,blockEq,statementEq] at shape
    | some statement =>
      refine ⟨block,statement,rfl,statementEq,?_⟩
      simpa [CopyPreconditions.Bodies.statementKindAt,blockEq,statementEq] using shape

theorem source_step [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel+1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨3,0⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (uninit0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
    (Storage.withCurrent frames
      {falseReturnFrame frame valid0 with location := .mir ⟨3,1⟩} machine,.ok true) := by
  obtain ⟨block,statement,blockAt,statementAt,kind⟩ := source_statement
  have blockAt' : frame.body.basicBlocks[3]? = some block := by rw [body]; exact blockAt
  exact SourceSteps.assign_exact (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
    frames frame (falseReturnFrame frame valid0) machine machine ⟨3,0⟩ block statement ⟨0,#[]⟩
    (.Use (.Constant CopyPreconditions.Bodies.languageFalseConstant) .Yes) location blockAt'
    statementAt kind
    (evaluate options limits remaining span source debugOff fuel fuelEq frames frame machine body identity
      callee location valid0 uninit0 uncached0 noClocks tracker tracked defaultMode ghostFalse shallow)
    (by simpa [falseReturnFrame,cacheReturnLayout,LocalPlaces.cachePlaceLayout] using location)

theorem goto_parent_false [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (location : frame.location = .mir ⟨3,1⟩)
    (unchecked : ((PreparedContracts.actualConfig options () remaining span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () remaining span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () remaining span) limits ()
      (Storage.withCurrent frames frame machine) =
    (Storage.withCurrent frames {frame with location := .mir ⟨4,0⟩}
      (SourceControl.accounted (PreparedContracts.actualConfig options () remaining span).terminators
        (Storage.withCurrent frames frame machine)).machine,.ok true) := by
  let block := CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[3]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[3]? = some block := by rw [body]; with_unfolding_all rfl
  have noStatement : block.statements[1]? = none := by with_unfolding_all decide +kernel
  have kind : ∃ source, block.terminator.kind = .Goto 4 source := by
    refine ⟨#[],?_⟩
    with_unfolding_all rfl
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getSet : ∀ control user,
      (PreparedContracts.actualConfig options () remaining span).terminators.getControl
        ((PreparedContracts.actualConfig options () remaining span).terminators.setControl control user) = control := by
    rw [fields.terminators]
    intro control user
    rfl
  have setSet : ∀ first second user,
      (PreparedContracts.actualConfig options () remaining span).terminators.setControl second
        ((PreparedContracts.actualConfig options () remaining span).terminators.setControl first user) =
      (PreparedContracts.actualConfig options () remaining span).terminators.setControl second user := by
    rw [fields.terminators]
    intro first second user
    rfl
  exact SourceControl.goto_step (PreparedContracts.actualConfig options () remaining span) limits ()
    frames frame machine ⟨3,1⟩ block 4 location blockAt noStatement kind getSet setSet unchecked noGc fixed

#print axioms evaluate
#print axioms source_step
#print axioms goto_parent_false
end DuplicatePrefix.ParentFalseAssignment

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ParentFalseAssignment.language_local0_normalized,
      ``DuplicatePrefix.ParentFalseAssignment.language_compute_local0,
      ``DuplicatePrefix.ParentFalseAssignment.canonical_return_place_uncached,
      ``DuplicatePrefix.ParentFalseAssignment.evaluate,
      ``DuplicatePrefix.ParentFalseAssignment.source_statement,
      ``DuplicatePrefix.ParentFalseAssignment.source_step,
      ``DuplicatePrefix.ParentFalseAssignment.goto_parent_false] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError s!"unapproved parent false-assignment dependency {dependency}"
