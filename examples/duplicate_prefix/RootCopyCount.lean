import duplicate_prefix.RootLocalStages
import duplicate_prefix.ActualScalarCopy
import duplicate_prefix.RootUsizeWrite
import duplicate_prefix.SourceSteps

/-! Actual MIR statement 0:3 copies the usize count local2 into local5. The
source operand read, uncached destination layout resolution, scalar copy
selection, Default retag scope, shallow validation, and step/PC update all use
the production interpreter hooks. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.RootCopyCount
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def writeFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid5 : (5 : Miri.MIR.LocalId) < frame.locals.size) (n : UInt64) :=
  let cached := LocalPlaces.cachePlaceLayout frame 5 RootCompilerFacts.usizeLayout valid5
  let validCached : (5 : Miri.MIR.LocalId) < cached.locals.size := by
    simpa [cached, LocalPlaces.cachePlaceLayout] using valid5
  {cached with locals := (cached.locals.set 5
    {value := .live (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n)))),
     layout := cached.locals[5].layout} validCached)}

def postFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid5 : (5 : Miri.MIR.LocalId) < frame.locals.size) (n : UInt64) :=
  {(writeFrame frame valid5 n) with location := .mir ⟨0, 4⟩}

/-- Compiler local5 is the usize argument/local from the actual reflected root
body, using the real normalized-body and target-layout queries. -/
theorem root_local5_layout
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 5
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.usizeLayout (Storage.withCurrent framesBefore frame machine) := by
  have normalized : CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 5 = .ok 5 := by
    unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
    rw [body, identity, callee]
    with_unfolding_all rfl
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [normalized]
  unfold_frame_query_lift
  simp only [pure, EStateM.pure]
  have queried : PreparedReflection.actual.compiler.runtime.lookup 5 = .ok RootCompilerFacts.usizeLayout := by
    with_unfolding_all exact RootCompilerFacts.usize_layout_eq
  rw [queried]
  rfl

/-- The actual statement 0:3 succeeds through uncached local5 evaluation,
source local2 copy, and the real usize write/validation path. -/
theorem actual_copy_count_step
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (n : UInt64)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live2 : (frame.locals[2]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (valid5 : (5 : Miri.MIR.LocalId) < frame.locals.size)
    (uninit5 : (frame.locals[5]'(by omega)).value = .live (.immediate .uninit))
    (uncached5 : (frame.locals[5]'(by omega)).layout = none)
    (noClocks : frame.extra.dataRace = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (location : frame.location = .mir ⟨0, 3⟩)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (tracker : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = Miri.TreeBorrows.RetagPolicy.RetagMode.Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1) :
    ExecutionMachine.step
      (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
    (Storage.withCurrent framesBefore (postFrame frame valid5 n) machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let state0 := Storage.withCurrent framesBefore frame machine
  let cachedFrame := LocalPlaces.cachePlaceLayout frame 5 RootCompilerFacts.usizeLayout valid5
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let placeHooks := projection.place
  let rvalueHooks := ExecutionMachine.rvalueHooks config limits
  let operandHooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 5 RootCompilerFacts.usizeLayout
  let sourceValue : OpTy Provenance := ⟨.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n))), RootCompilerFacts.usizeLayout⟩
  let writtenFrame := writeFrame frame valid5 n
  let stateAfter := Storage.withCurrent framesBefore writtenFrame machine
  have valid5Cached : (5 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using valid5
  have cached5Cached : (cachedFrame.locals[5]'(by omega)).layout = some RootCompilerFacts.usizeLayout := by
    simp [cachedFrame, LocalPlaces.cachePlaceLayout]
  have uninit5Cached : (cachedFrame.locals[5]'(by omega)).value = .live (.immediate .uninit) := by
    have h5 : 5 < (frame.locals.set 5
        {value := frame.locals[5].value, layout := some RootCompilerFacts.usizeLayout} valid5).size := by
      simpa only [Array.size_set] using valid5
    change ((frame.locals.set 5
      {value := frame.locals[5].value, layout := some RootCompilerFacts.usizeLayout} valid5)[5]'h5).value = _
    rw [Array.getElem_set_self]
    exact uninit5
  have sourceValid : (2 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    have h2 : 2 < (frame.locals.set 5
        {value := frame.locals[5].value, layout := some RootCompilerFacts.usizeLayout} valid5).size := by
      simpa using valid2
    simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using h2
  have sourceLive : (cachedFrame.locals[2]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n)))) := by
    have ne : (5 : Nat) ≠ 2 := by omega
    have h2 : 2 < (frame.locals.set 5
        {value := frame.locals[5].value, layout := some RootCompilerFacts.usizeLayout} valid5).size := by
      simpa using valid2
    change ((frame.locals.set 5
      {value := frame.locals[5].value, layout := some RootCompilerFacts.usizeLayout} valid5)[2]'h2).value = _
    rw [Array.getElem_set_ne (h' := valid5) (pj := valid2) (h := ne)]
    exact live2
  have sourceCached : (cachedFrame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout := by
    have ne : (5 : Nat) ≠ 2 := by omega
    have h2 : 2 < (frame.locals.set 5
        {value := frame.locals[5].value, layout := some RootCompilerFacts.usizeLayout} valid5).size := by
      simpa using valid2
    change ((frame.locals.set 5
      {value := frame.locals[5].value, layout := some RootCompilerFacts.usizeLayout} valid5)[2]'h2).layout = _
    rw [Array.getElem_set_ne (h' := valid5) (pj := valid2) (h := ne)]
    exact cached2
  have noClocksCached : cachedFrame.extra.dataRace = none := by
    simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using noClocks
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have validGetter : operandHooks.compiler.validationInProgress state1 = .ok false state1 := by
    change config.compiler.validationInProgress state1 = _
    rw [fields.compilerValidationInProgress]
    have stateGhost : state1.machine.user.payload.ghost = false := by
      simpa [state1, Storage.withCurrent] using ghostFalse
    simp [ValidityMachine.validationInProgress, stateGhost, get, getThe,
      MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have localRead := LocalOperands.cached_immediate operandHooks () framesBefore cachedFrame machine
    2 (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n))) RootCompilerFacts.usizeLayout
    (some RootCompilerFacts.usizeLayout) sourceValid sourceLive sourceCached
    (by decide +kernel) noClocksCached false validGetter
  have typeCheck := RootLocalStages.operand_check_skipped options limits () (remaining + 1) span debugOff
    (OperandDispatch.wholeLocal 2) sourceValue state1
  have evalSource := OperandDispatch.evalOperandAt_copy_wholeLocal operandHooks ()
    (OperandPath.rvalue "operand") 2 (some RootCompilerFacts.usizeLayout) state1 state1 sourceValue
    localRead typeCheck
  have getFrame : placeHooks.getFrame state0 = .ok frame state0 := by
    change config.projection.place.getFrame state0 = .ok frame state0
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  have frameIndex : placeHooks.frameIndex state0 = .ok framesBefore.size state0 := by
    change config.projection.place.frameIndex state0 = .ok framesBefore.size state0
    rw [fields.projectionFrameIndex]
    simp [state0, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push, bind,
      EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, Except.pure]
  have resolve : placeHooks.resolveLayout () 5 state0 = .ok RootCompilerFacts.usizeLayout state0 := by
    change config.projection.place.resolveLayout () 5 state0 = .ok RootCompilerFacts.usizeLayout state0
    rw [fields.projectionResolveLayout, fields.layout]
    exact root_local5_layout framesBefore frame machine body identity callee
  have setCached : placeHooks.setFrame cachedFrame state0 = .ok () state1 := by
    change config.projection.place.setFrame cachedFrame state0 = .ok () state1
    rw [fields.projectionSetFrame]
    exact Storage.set_current_frame framesBefore frame cachedFrame machine
  have getCached : placeHooks.getFrame state1 = .ok cachedFrame state1 := by
    change config.projection.place.getFrame state1 = .ok cachedFrame state1
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore cachedFrame machine
  have indexCached : placeHooks.frameIndex state1 = .ok framesBefore.size state1 := by
    change config.projection.place.frameIndex state1 = .ok framesBefore.size state1
    rw [fields.projectionFrameIndex]
    simp [state1, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push, bind,
      EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, Except.pure]
  have destSized : RootCompilerFacts.usizeLayout.layout.isSized = true := ActualScalarCopy.usize_sized
  have localPlace := LocalPlaces.localToPlace_uncached placeHooks () framesBefore frame machine 5
    framesBefore.size RootCompilerFacts.usizeLayout valid5 uncached5 destSized resolve getFrame
    frameIndex setCached getCached indexCached
  have destCheck := RootLocalStages.place_check_skipped options limits () (remaining + 1) span debugOff
    ⟨5, #[]⟩ dest state1
  have evalDest := LocalPlaces.evalPlace_local_empty_uncached projection () 5 framesBefore frame machine
    framesBefore.size RootCompilerFacts.usizeLayout valid5 (state := state0) (updated := state1)
    localPlace destCheck
  have copyBody : rvalueHooks.copyOp () sourceValue dest state1 = .ok () stateAfter := by
    have actualCopy := ActualScalarCopy.actual_copy_usize options limits (remaining + 1) span debugOff n dest rfl
    have physical := RootUsizeWrite.write_usize_shallow options limits remaining span debugOff fuel fuelEq
      framesBefore cachedFrame machine 5 .uninit (ScalarInt.ofUInt64 n) valid5Cached uninit5Cached
      cached5Cached noClocksCached ghostFalse shallow
    have actualCopyFunction : rvalueHooks.copyOp () sourceValue dest =
        rvalueHooks.writeImmediate () (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n))) dest := by
      change (ExecutionMachine.rvalueHooks
        (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp ()
          ⟨.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n))), RootCompilerFacts.usizeLayout⟩ dest =
        (ExecutionMachine.rvalueHooks
          (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate ()
          (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n))) dest
      exact actualCopy
    have actualCopy' : rvalueHooks.copyOp () sourceValue dest state1 =
        rvalueHooks.writeImmediate () (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n))) dest state1 :=
      congrArg (fun action => action state1) actualCopyFunction
    have outputFrameEq : writtenFrame = {cachedFrame with locals := (cachedFrame.locals.set 5
        {value := .live (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n)))),
         layout := cachedFrame.locals[5].layout} valid5Cached)} := by
      simp [writtenFrame, RootCopyCount.writeFrame, cachedFrame, LocalPlaces.cachePlaceLayout]
    have physical' : rvalueHooks.writeImmediate ()
        (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n))) dest state1 = .ok () stateAfter := by
      change rvalueHooks.writeImmediate ()
        (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n)))
        (LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 5 RootCompilerFacts.usizeLayout)
        (Storage.withCurrent framesBefore cachedFrame machine) =
        .ok () (Storage.withCurrent framesBefore writtenFrame machine)
      rw [outputFrameEq]
      exact physical
    exact actualCopy'.trans physical'
  have trackerAt : state1.machine.borrowTracker = some tracker := by
    simpa [state1, Storage.withCurrent] using tracked
  have trackerAfter : stateAfter.machine.borrowTracker = some tracker := by
    simpa [stateAfter, writtenFrame, Storage.withCurrent] using tracked
  have scopedCopy : rvalueHooks.withRetagMode () Miri.TreeBorrows.RetagPolicy.RetagMode.Default
      (rvalueHooks.copyOp () sourceValue dest) state1 = .ok () stateAfter := by
    change MachineHooks.withRetagMode Miri.TreeBorrows.RetagPolicy.RetagMode.Default
      (rvalueHooks.copyOp () sourceValue dest) state1 = .ok () stateAfter
    exact ScalarCopyStage.with_retag_mode_existing Miri.TreeBorrows.RetagPolicy.RetagMode.Default
      (rvalueHooks.copyOp () sourceValue dest) state1 stateAfter tracker () trackerAt defaultMode
      trackerAfter copyBody
  have effect := RvalueDispatch.use_operand rvalueHooks () (.Copy ⟨2, #[]⟩) .Yes ⟨5, #[]⟩
    dest sourceValue state0 state1 state1 stateAfter evalDest evalSource scopedCopy
  let block := RootBody.reflected.body.body.basicBlocks[0]'(by decide)
  let statement := block.statements[3]'(by decide)
  have blockAt : frame.body.basicBlocks[0]? = some block := by
    rw [body]
    simp [block]
  have statementAt : block.statements[3]? = some statement := by simp [statement]
  have statementKind : statement.kind = .Assign ⟨5, #[]⟩ (.Use (.Copy ⟨2, #[]⟩) .Yes) := by
    have shape := RootBody.root_count_copy
    simp only [RootBody.statementKindAt] at shape
    rw [show RootBody.reflected.body.body.basicBlocks[0]? = some block by simp [block]] at shape
    change Option.map Statement.kind (block.statements[3]?) = _ at shape
    rw [statementAt] at shape
    cases shape
    rfl
  have afterLocation : writtenFrame.location = .mir ⟨0, 3⟩ := by
    change frame.location = .mir ⟨0, 3⟩
    exact location
  have effect' : evalRvalueIntoPlace rvalueHooks ()
      (.Use (.Copy ⟨2, #[]⟩) .Yes) ⟨5, #[]⟩ state0 = .ok () stateAfter := by
    exact effect
  have step := SourceSteps.assign_exact config limits () framesBefore frame writtenFrame machine machine
    ⟨0, 3⟩ block statement ⟨5, #[]⟩ (.Use (.Copy ⟨2, #[]⟩) .Yes)
    location blockAt statementAt statementKind effect' afterLocation
  simpa [postFrame, writeFrame, writtenFrame, RootCopyCount.writeFrame, LocalPlaces.cachePlaceLayout] using step

#print axioms actual_copy_count_step
end DuplicatePrefix.RootCopyCount
