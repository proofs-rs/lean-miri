import duplicate_prefix.RootEqUncached
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.RootCompilerFacts

/-! Complete source Eq guard assignment: the actual uncached destination cache,
actual MIR Eq operands and scalar operation, followed by actual local write and
Shallow validation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootEqSuccess
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem actual_root_eq_succeeds
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (n : UInt64)
    (valid4 : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (uninit4 : (frame.locals[4]'(by omega)).value = .live (.immediate .uninit))
    (valid5 : (5 : Miri.MIR.LocalId) < frame.locals.size)
    (live5 : (frame.locals[5]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached5 : (frame.locals[5]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (location : frame.location = .mir ⟨0, 4⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks
        (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      (.BinaryOp .Eq (.Move ⟨5, #[]⟩) (.Constant RootConstantStage.zeroConstant))
      ⟨4, #[]⟩ (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore
      {LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4 with
        locals := ((LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4).locals.set 4
          {value := .live (.immediate (.scalar (.fromBool (n == 0)))),
           layout := some RootCompilerFacts.boolLayout} (by simpa [LocalPlaces.cachePlaceLayout] using valid4))} machine) := by
  let cachedFrame := LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4
  let cachedState := Storage.withCurrent framesBefore cachedFrame machine
  have valid4' : (4 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using valid4
  have cached4' : (cachedFrame.locals[4]'(by omega)).layout = some RootCompilerFacts.boolLayout := by
    simp [cachedFrame, LocalPlaces.cachePlaceLayout]
  have uninit4' : (cachedFrame.locals[4]'(by omega)).value = .live (.immediate .uninit) := by
    have h4set : 4 < (frame.locals.set 4
        {value := frame.locals[4].value, layout := some RootCompilerFacts.boolLayout} valid4).size := by
      simpa only [Array.size_set] using valid4
    change ((frame.locals.set 4
      {value := frame.locals[4].value, layout := some RootCompilerFacts.boolLayout} valid4)[4]'h4set).value = _
    rw [Array.getElem_set_self]
    exact uninit4
  have valid5' : (5 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using valid5
  have live5' : (cachedFrame.locals[5]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))) := by
    have ne : (4 : Nat) ≠ 5 := by omega
    have valid5Set : 5 < (frame.locals.set 4
        {value := frame.locals[4].value, layout := some RootCompilerFacts.boolLayout} valid4).size := by
      simpa using valid5
    change ((frame.locals.set 4
      {value := frame.locals[4].value, layout := some RootCompilerFacts.boolLayout} valid4)[5]'valid5Set).value = _
    rw [Array.getElem_set_ne (h' := valid4) (pj := valid5) (h := ne)]
    exact live5
  have cached5' : (cachedFrame.locals[5]'(by omega)).layout = some RootCompilerFacts.usizeLayout := by
    have ne : (4 : Nat) ≠ 5 := by omega
    have valid5Set : 5 < (frame.locals.set 4
        {value := frame.locals[4].value, layout := some RootCompilerFacts.boolLayout} valid4).size := by
      simpa using valid5
    change ((frame.locals.set 4
      {value := frame.locals[4].value, layout := some RootCompilerFacts.boolLayout} valid4)[5]'valid5Set).layout = _
    rw [Array.getElem_set_ne (h' := valid4) (pj := valid5) (h := ne)]
    exact cached5
  have noClocks' : cachedFrame.extra.dataRace = none := by
    simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using noClocks
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have usizeSized : RootCompilerFacts.usizeLayout.layout.backendRepr.isUnsized = false := by decide +kernel
  obtain ⟨primitive, range, usizeReadable⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.usizeLayout CopyCompilerFacts.primitive_layouts_initialized.2.2.2
  have usizeWidth : RootCompilerFacts.usizeLayout.layout.size = Size.ofBytes 8 := by decide +kernel
  have getter : (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation config limits)).compiler.validationInProgress cachedState =
      .ok false cachedState := by
    change config.compiler.validationInProgress cachedState = _
    rw [fields.compilerValidationInProgress]
    have stateGhost : cachedState.machine.user.payload.ghost = false := by
      simpa [cachedState, Storage.withCurrent] using ghostFalse
    simp [ValidityMachine.validationInProgress, stateGhost,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have rootEq := RootEqUncached.actual_root_eq_uncached_to_write options limits (remaining + 1) span source
    debugOff framesBefore frame machine n valid4 uncached4 valid5 live5 cached5 usizeSized
    ⟨primitive, range, usizeReadable⟩
    noClocks getter body (by rw [identity]) identity location fnInstance usizeWidth
  have writer := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff fuel fuelEq
    framesBefore cachedFrame machine 4 .uninit (n == 0) valid4' uninit4' cached4' noClocks' ghostFalse shallow
  simpa [cachedState, cached4'] using rootEq.trans writer

#print axioms actual_root_eq_succeeds
end DuplicatePrefix.RootEqSuccess
