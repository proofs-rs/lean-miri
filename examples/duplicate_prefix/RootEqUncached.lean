import duplicate_prefix.RootLocalStages
import duplicate_prefix.RootScalarQueries
import duplicate_prefix.DestinationCache

/-! Compose the uncached destination layout cache with the real root Eq rvalue
stages, preserving the source interpreter's destination-first order. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace DuplicatePrefix.RootEqUncached
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- The root guard assignment evaluates from an uncached local4 through the
actual compiler layout resolver, then continues through the cached-state Eq
bridge and reaches the real write hook. -/
theorem actual_root_eq_uncached_to_write
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
    (valid5 : (5 : Miri.MIR.LocalId) < frame.locals.size)
    (live5 : (frame.locals[5]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached5 : (frame.locals[5]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (usizeSized : RootCompilerFacts.usizeLayout.layout.backendRepr.isUnsized = false)
    (usizeReadable : ∃ primitive range, RootCompilerFacts.usizeLayout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range)))
    (noClocks : frame.extra.dataRace = none)
    (validationGetterCached : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).compiler.validationInProgress
        (Storage.withCurrent framesBefore
          (LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4) machine) =
      .ok false (Storage.withCurrent framesBefore
        (LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4) machine))
    (body : frame.body = RootBody.reflected.body.body)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (location : frame.location = .mir ⟨0, 4⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance)
    (usizeWidth : RootCompilerFacts.usizeLayout.layout.size = Size.ofBytes 8) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks
        (PreparedContracts.actualConfig options () remaining span) limits) ()
      (.BinaryOp .Eq (.Move ⟨5, #[]⟩) (.Constant RootConstantStage.zeroConstant))
      ⟨4, #[]⟩ (Storage.withCurrent framesBefore frame machine) =
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).writeImmediate
      () (.scalar (.fromBool (n == 0)))
      (LocalPlaces.localRuntimePlace framesBefore.size
        (LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4) 4
        RootCompilerFacts.boolLayout)
      (Storage.withCurrent framesBefore
        (LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4
  let initial := Storage.withCurrent framesBefore frame machine
  let cached := Storage.withCurrent framesBefore cachedFrame machine
  have valid4' : (4 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using valid4
  have cached4' : (cachedFrame.locals[4]'(by omega)).layout = some RootCompilerFacts.boolLayout := by
    simp [cachedFrame, LocalPlaces.cachePlaceLayout]
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
  have validationGetter' := validationGetterCached
  have first : hooks.evalPlace () ⟨4, #[]⟩ true initial =
      .ok (LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 4 RootCompilerFacts.boolLayout) cached := by
    simpa [hooks, config, cachedFrame, initial, cached, ExecutionMachine.rvalueHooks,
      ExecutionMachine.withValidation] using
      RootLocalStages.canonical_destination_local_uncached options limits remaining span debugOff
        framesBefore frame machine valid4 uncached4 body identity fnInstance
  have again : hooks.evalPlace () ⟨4, #[]⟩ true cached =
      .ok (LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 4 RootCompilerFacts.boolLayout) cached := by
    simpa [hooks, config, cachedFrame, cached, ExecutionMachine.rvalueHooks,
      ExecutionMachine.withValidation] using
      RootLocalStages.canonical_destination_local options limits remaining span debugOff
        framesBefore cachedFrame machine RootCompilerFacts.boolLayout valid4' cached4'
        (by decide +kernel)
  have cachedRun : evalRvalueIntoPlace hooks ()
      (.BinaryOp .Eq (.Move ⟨5, #[]⟩) (.Constant RootConstantStage.zeroConstant))
      ⟨4, #[]⟩ cached = hooks.writeImmediate () (.scalar (.fromBool (n == 0)))
        (LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 4 RootCompilerFacts.boolLayout) cached := by
    apply RootLocalStages.canonical_root_eq_to_write options limits remaining span source debugOff
      framesBefore cachedFrame machine n RootCompilerFacts.boolLayout valid4' cached4'
      (by decide +kernel) valid5' live5' cached5' usizeSized usizeReadable noClocks'
      validationGetter' (by simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using bodyIndex)
      (by simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using location)
      (by simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using fnInstance)
      (RootScalarQueries.usize_classification options remaining span limits)
      (RootScalarQueries.bool_layout options remaining span limits)
      usizeWidth
  have cacheStage := DestinationCache.evaluate_from_cached hooks ()
    (.BinaryOp .Eq (.Move ⟨5, #[]⟩) (.Constant RootConstantStage.zeroConstant))
    ⟨4, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 4 RootCompilerFacts.boolLayout)
    initial cached first again
  simpa [hooks, config, cachedFrame, cached] using cacheStage.trans cachedRun

#print axioms actual_root_eq_uncached_to_write
end DuplicatePrefix.RootEqUncached
