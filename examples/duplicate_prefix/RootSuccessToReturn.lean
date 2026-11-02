import duplicate_prefix.RootSuccessCleanup
namespace DuplicatePrefix.RootSuccessToReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem reaches_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (size : frame.locals.size = 25) (temp15 temp18 temp19 temp21 temp24 : Immediate Provenance)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (none0 : (frame.locals[0]'(by omega)).layout = none)
    (live15 : (frame.locals[15]'(by omega)).value = .live (.immediate temp15))
    (live17 : (frame.locals[17]'(by omega)).value = .live (.immediate .uninit))
    (none17 : (frame.locals[17]'(by omega)).layout = none)
    (live18 : (frame.locals[18]'(by omega)).value = .live (.immediate temp18))
    (live19 : (frame.locals[19]'(by omega)).value = .live (.immediate temp19))
    (live21 : (frame.locals[21]'(by omega)).value = .live (.immediate temp21))
    (live24 : (frame.locals[24]'(by omega)).value = .live (.immediate temp24))
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨9,0⟩) (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore {done with location := .mir ⟨10,0⟩}
          (SourceControl.accounted config.terminators (Storage.withCurrent framesBefore done machine)).machine) ∧
      RootSuccessCleanupFacts.Shape frame done RootCompilerFacts.boolLayout (.scalar (.fromBool true)) := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨done, history, shape⟩ := RootSuccessCleanup.statements options limits remaining span source debugOff fuel validationFuel
    framesBefore frame machine size temp15 temp18 temp19 temp21 temp24
    live0 none0 live15 live17 none17 live18 live19 live21 live24 body identity callee location noClocks
    tracker tracked defaultMode ghostFalse shallow
  let block := RootBody.reflected.body.body.basicBlocks[9]'(by with_unfolding_all decide +kernel)
  have last := SourceControl.goto_step config limits () framesBefore done machine ⟨9,8⟩ block 10 shape.location
    (by rw [shape.body, body]; simp [block])
    (by with_unfolding_all rfl) (by exact ⟨#[],by with_unfolding_all rfl⟩)
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  exact ⟨done, SuccessfulTrace.append history (.next last (.refl _)), shape⟩
#print axioms reaches_return
end DuplicatePrefix.RootSuccessToReturn
