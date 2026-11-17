import duplicate_prefix.RootMutPreparationFacts
import duplicate_prefix.RootUnitAssignment
import duplicate_prefix.SevenSteps
namespace DuplicatePrefix.RootMutPreparation
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem raw_storage (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).lifecycle.storage.veryTriviallySized 8 = .ok true := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
  with_unfolding_all rfl

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (size : frame.locals.size = 25) (temp7 temp8 temp9 temp10 : Immediate Provenance)
    (live7 : (frame.locals[7]'(by omega)).value = .live (.immediate temp7))
    (none7 : (frame.locals[7]'(by omega)).layout = none)
    (live8 : (frame.locals[8]'(by omega)).value = .live (.immediate temp8))
    (live9 : (frame.locals[9]'(by omega)).value = .live (.immediate temp9))
    (live10 : (frame.locals[10]'(by omega)).value = .live (.immediate temp10))
    (dead15 : (frame.locals[15]'(by omega)).value = .dead)
    (none15 : (frame.locals[15]'(by omega)).layout = none)
    (dead16 : (frame.locals[16]'(by omega)).value = .dead)
    (none16 : (frame.locals[16]'(by omega)).layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨6,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore done machine) ∧ RootMutPreparationFacts.Shape frame done := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[6]? = some block := by rw [body];simp [block]
  have v10 : (10 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let f1 := SourceSteps.deadFrame frame ⟨6,0⟩ 10 v10
  have e1 := SourceSteps.storage_dead_exact config limits () framesBefore frame machine ⟨6,0⟩ block stmt0
    10 temp10 location blockAt (by simp [stmt0]) (by with_unfolding_all rfl) v10 (by decide) live10
  have sz1 : f1.locals.size = 25 := by simp [f1,SourceSteps.deadFrame,size]
  have v9 : (9 : Miri.MIR.LocalId) < f1.locals.size := by rw [sz1];decide
  let stmt1 := block.statements[1]'(by with_unfolding_all decide +kernel)
  let f2 := SourceSteps.deadFrame f1 ⟨6,1⟩ 9 v9
  have e2 := SourceSteps.storage_dead_exact config limits () framesBefore f1 machine ⟨6,1⟩ block stmt1
    9 temp9 rfl blockAt (by simp [stmt1]) (by with_unfolding_all rfl) v9 (by decide)
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using live9)
  have sz2 : f2.locals.size = 25 := by simp [f2,SourceSteps.deadFrame,sz1]
  have v7 : (7 : Miri.MIR.LocalId) < f2.locals.size := by rw [sz2];decide
  let f3 := {(ActualLocalCopy.written f2 7 CopyHelperUnit.layout v7 .uninit) with location := .mir ⟨6,3⟩}
  have e3 := RootUnitAssignment.step options limits remaining span source debugOff fuel validationFuel .afterGuard
    framesBefore f2 machine v7 temp7
    (by simpa [RootUnitAssignment.localIdOf,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live7)
    (by simpa [RootUnitAssignment.localIdOf,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using none7)
    body identity callee rfl noClocks tracker tracked defaultMode ghostFalse shallow
  have sz3 : f3.locals.size = 25 := by simp [f3,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,sz2]
  have v8 : (8 : Miri.MIR.LocalId) < f3.locals.size := by rw [sz3];decide
  let stmt3 := block.statements[3]'(by with_unfolding_all decide +kernel)
  let f4 := SourceSteps.deadFrame f3 ⟨6,3⟩ 8 v8
  have e4 := SourceSteps.storage_dead_exact config limits () framesBefore f3 machine ⟨6,3⟩ block stmt3
    8 temp8 rfl blockAt (by simp [stmt3]) (by with_unfolding_all rfl) v8 (by decide)
    (by simpa [f3,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live8)
  have sz4 : f4.locals.size = 25 := by simp [f4,SourceSteps.deadFrame,sz3]
  have v7' : (7 : Miri.MIR.LocalId) < f4.locals.size := by rw [sz4];decide
  let stmt4 := block.statements[4]'(by with_unfolding_all decide +kernel)
  let f5 := SourceSteps.deadFrame f4 ⟨6,4⟩ 7 v7'
  have e5 := SourceSteps.storage_dead_exact config limits () framesBefore f4 machine ⟨6,4⟩ block stmt4
    7 .uninit rfl blockAt (by simp [stmt4]) (by with_unfolding_all rfl) v7' (by decide)
    (by simp [f4,SourceSteps.deadFrame,f3,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set])
  have sz5 : f5.locals.size = 25 := by simp [f5,SourceSteps.deadFrame,sz4]
  have v15 : (15 : Miri.MIR.LocalId) < f5.locals.size := by rw [sz5];decide
  let stmt5 := block.statements[5]'(by with_unfolding_all decide +kernel)
  let f6 := SourceSteps.liveFrame f5 ⟨6,5⟩ 15 v15
  have e6 := SourceSteps.storage_live_exact config limits () framesBefore f5 machine ⟨6,5⟩ block stmt5
    15 8 rfl blockAt (by simp [stmt5]) (by with_unfolding_all rfl) v15
    (by change frame.body.locals[15]? = _;rw [body];with_unfolding_all rfl)
    (raw_storage options (remaining+1) span)
    (by simpa [f5,f4,f3,f2,f1,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using dead15) noClocks
  have sz6 : f6.locals.size = 25 := by simp [f6,SourceSteps.liveFrame,sz5]
  have v16 : (16 : Miri.MIR.LocalId) < f6.locals.size := by rw [sz6];decide
  let stmt6 := block.statements[6]'(by with_unfolding_all decide +kernel)
  let f7 := SourceSteps.liveFrame f6 ⟨6,6⟩ 16 v16
  have e7 := SourceSteps.storage_live_exact config limits () framesBefore f6 machine ⟨6,6⟩ block stmt6
    16 3 rfl blockAt (by simp [stmt6]) (by with_unfolding_all rfl) v16
    (by change frame.body.locals[16]? = _;rw [body];with_unfolding_all rfl)
    (CanonicalConfigFacts.actual_storage_slice options () (remaining+1) span)
    (by simpa [f6,f5,f4,f3,f2,f1,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using dead16) noClocks
  have history : SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
      (Storage.withCurrent framesBefore f7 machine) := SevenSteps.trace e1 e2 e3 e4 e5 e6 e7
  have resultEq : f7 = RootMutPreparationFacts.result frame CopyHelperUnit.layout size := by rfl
  have shape := RootMutPreparationFacts.shape frame CopyHelperUnit.layout size none15 none16
  rw [← resultEq] at shape
  generalize finalEq : f7 = final at history shape
  exact ⟨final,history,shape⟩

#print axioms executes
end DuplicatePrefix.RootMutPreparation
