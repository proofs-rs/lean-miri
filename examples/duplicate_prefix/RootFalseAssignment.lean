import duplicate_prefix.RootFalseConstant
import duplicate_prefix.RootZeroSwitch
namespace DuplicatePrefix.RootFalseAssignment
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
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

theorem evaluate
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
    (location : frame.location = .mir ⟨5,2⟩)
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
      (.Use (.Constant RootFalseConstant.constant) .Yes) ⟨0,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore (falseReturnFrame frame valid0) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := cacheReturnLayout frame valid0
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 0 RootCompilerFacts.boolLayout
  let sourceOp : OpTy Provenance := ⟨.immediate (.scalar (.fromBool false)), RootCompilerFacts.boolLayout⟩
  have evalDest := RootZeroSwitch.canonical_return_place_uncached options limits (remaining+1) span debugOff
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
  have cachedLocation : cachedFrame.location = .mir ⟨5,2⟩ := by
    simpa [cachedFrame, cacheReturnLayout, LocalPlaces.cachePlaceLayout] using location
  have operand := RootFalseConstant.operand options limits (remaining+1) span source debugOff
    framesBefore cachedFrame machine cachedBodyIndex cachedLocation callee
  have evalSource : hooks.evalOperandAt () (OperandPath.rvalue "operand")
      (.Constant RootFalseConstant.constant) (some (hooks.placeLayout dest)) state1 = .ok sourceOp state1 := by
    change OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)) ()
      (OperandPath.rvalue "operand") (.Constant RootFalseConstant.constant)
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
  have effect := RvalueDispatch.use_operand hooks () (.Constant RootFalseConstant.constant) .Yes ⟨0,#[]⟩
    dest sourceOp state0 state1 state1 after evalDest evalSource scopedCopy
  exact effect

#print axioms evaluate
end DuplicatePrefix.RootFalseAssignment
