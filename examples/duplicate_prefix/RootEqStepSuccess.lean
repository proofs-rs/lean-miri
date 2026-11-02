import duplicate_prefix.RootEqSuccess
import duplicate_prefix.SourceSteps

/-! Lift the actual Eq write effect through the production statement dispatcher
and source step/PC update. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootEqStepSuccess
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def postFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid4 : (4 : Miri.MIR.LocalId) < frame.locals.size) (n : UInt64) :
    Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  let cached := LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4
  let validCached : (4 : Miri.MIR.LocalId) < cached.locals.size := by
    simpa [cached, LocalPlaces.cachePlaceLayout] using valid4
  {cached with
    locals := cached.locals.set 4
      {value := .live (.immediate (.scalar (.fromBool (n == 0)))),
       layout := some RootCompilerFacts.boolLayout} validCached
    location := .mir ⟨0, 5⟩}

theorem actual_root_eq_step_succeeds
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
    ExecutionMachine.step
      (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
    (Storage.withCurrent framesBefore (postFrame frame valid4 n) machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let rootBody := RootBody.reflected.body.body
  let block := rootBody.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[4]'(by with_unfolding_all decide +kernel)
  have blockAtRoot : rootBody.basicBlocks[0]? = some block := by
    simp [block]
  have statementAt : block.statements[4]? = some statement := by
    simp [statement]
  have blockAt : frame.body.basicBlocks[0]? = some block := by
    rw [body]
    exact blockAtRoot
  have statementKind : statement.kind =
      .Assign ⟨4, #[]⟩ (.BinaryOp .Eq (.Move ⟨5, #[]⟩)
        (.Constant RootConstantStage.zeroConstant)) := by
    have shape := RootBody.root_guard_zero_test
    simp only [RootBody.statementKindAt] at shape
    rw [blockAtRoot] at shape
    change Option.map Statement.kind (block.statements[4]?) = _ at shape
    rw [statementAt] at shape
    cases shape
    rfl
  let cached := LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid4
  have cachedValid4 : (4 : Miri.MIR.LocalId) < cached.locals.size := by
    simpa [cached, LocalPlaces.cachePlaceLayout] using valid4
  let beforeWriteFrame := {cached with locals := (cached.locals.set 4
      {value := .live (.immediate (.scalar (.fromBool (n == 0)))),
       layout := cached.locals[4].layout} cachedValid4)}
  have effect := RootEqSuccess.actual_root_eq_succeeds options limits remaining span source debugOff
    framesBefore frame machine n valid4 uncached4 uninit4 valid5 live5 cached5
    noClocks body identity location fnInstance ghostFalse shallow fuel fuelEq
  have afterLocation : beforeWriteFrame.location = .mir ⟨0, 4⟩ := by
    simp [beforeWriteFrame, cached, LocalPlaces.cachePlaceLayout, location]
  have effect' : evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) ()
      (.BinaryOp .Eq (.Move ⟨5, #[]⟩) (.Constant RootConstantStage.zeroConstant))
      ⟨4, #[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore beforeWriteFrame machine) := by
    simpa [config, beforeWriteFrame, cached, LocalPlaces.cachePlaceLayout, cached] using effect
  have step := SourceSteps.assign_exact config limits () framesBefore frame beforeWriteFrame machine machine
    ⟨0, 4⟩ block statement ⟨4, #[]⟩
    (.BinaryOp .Eq (.Move ⟨5, #[]⟩) (.Constant RootConstantStage.zeroConstant))
    location blockAt statementAt statementKind effect' afterLocation
  simpa [postFrame, beforeWriteFrame, cached, LocalPlaces.cachePlaceLayout] using step

#print axioms actual_root_eq_step_succeeds
end DuplicatePrefix.RootEqStepSuccess
