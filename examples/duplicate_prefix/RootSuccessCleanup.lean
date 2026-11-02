import duplicate_prefix.SuccessfulTrace
import duplicate_prefix.RootSuccessCleanupFacts
import duplicate_prefix.RootUnitAssignment
import duplicate_prefix.RootSuccessAssignment
import duplicate_prefix.SourceControl
namespace DuplicatePrefix.RootSuccessCleanup
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem success_frame_eq (frame : CompilerFrameContext.ActualFrame) (valid : (0 : Miri.MIR.LocalId) < frame.locals.size) :
    RootSuccessAssignment.successReturnFrame frame valid =
    ActualLocalCopy.written frame 0 RootCompilerFacts.boolLayout valid (.scalar (.fromBool true)) := by
  simp [RootSuccessAssignment.successReturnFrame,RootSuccessAssignment.cacheReturnLayout,
    ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.set_set]

theorem statements
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
    (ghostFalse : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore done machine) ∧
      RootSuccessCleanupFacts.Shape frame done RootCompilerFacts.boolLayout (.scalar (.fromBool true)) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[9]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[9]? = some block := by rw [body];simp [block]
  have v24 : (24 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let s0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let f1 := SourceSteps.deadFrame frame ⟨9,0⟩ 24 v24
  have e1 := SourceSteps.storage_dead_exact config limits () framesBefore frame machine ⟨9,0⟩ block s0
    24 temp24 location blockAt (by simp [s0]) (by with_unfolding_all rfl) v24 (by decide) live24
  have sz1 : f1.locals.size = 25 := by simp [f1,SourceSteps.deadFrame,size]
  have v21 : (21 : Miri.MIR.LocalId) < f1.locals.size := by rw [sz1];decide
  let s1 := block.statements[1]'(by with_unfolding_all decide +kernel)
  let f2 := SourceSteps.deadFrame f1 ⟨9,1⟩ 21 v21
  have e2 := SourceSteps.storage_dead_exact config limits () framesBefore f1 machine ⟨9,1⟩ block s1
    21 temp21 rfl blockAt (by simp [s1]) (by with_unfolding_all rfl) v21 (by decide)
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using live21)
  have sz2 : f2.locals.size = 25 := by simp [f2,SourceSteps.deadFrame,sz1]
  have v19 : (19 : Miri.MIR.LocalId) < f2.locals.size := by rw [sz2];decide
  let s2 := block.statements[2]'(by with_unfolding_all decide +kernel)
  let f3 := SourceSteps.deadFrame f2 ⟨9,2⟩ 19 v19
  have e3 := SourceSteps.storage_dead_exact config limits () framesBefore f2 machine ⟨9,2⟩ block s2
    19 temp19 rfl blockAt (by simp [s2]) (by with_unfolding_all rfl) v19 (by decide)
    (by simpa [f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live19)
  have sz3 : f3.locals.size = 25 := by simp [f3,SourceSteps.deadFrame,sz2]
  have v18 : (18 : Miri.MIR.LocalId) < f3.locals.size := by rw [sz3];decide
  let s3 := block.statements[3]'(by with_unfolding_all decide +kernel)
  let f4 := SourceSteps.deadFrame f3 ⟨9,3⟩ 18 v18
  have e4 := SourceSteps.storage_dead_exact config limits () framesBefore f3 machine ⟨9,3⟩ block s3
    18 temp18 rfl blockAt (by simp [s3]) (by with_unfolding_all rfl) v18 (by decide)
    (by simpa [f3,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live18)
  have sz4 : f4.locals.size = 25 := by simp [f4,SourceSteps.deadFrame,sz3]
  have history4 : SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
      (Storage.withCurrent framesBefore f4 machine) := .next e1 (.next e2 (.next e3 (.next e4 (.refl _))))
  have v0 : (0 : Miri.MIR.LocalId) < f4.locals.size := by rw [sz4];decide
  have v15 : (15 : Miri.MIR.LocalId) < f4.locals.size := by rw [sz4];decide
  have v17 : (17 : Miri.MIR.LocalId) < f4.locals.size := by rw [sz4];decide
  have at4 : f4.location = .mir ⟨9,4⟩ := rfl
  have body4 : f4.body = RootBody.reflected.body.body := body
  have identity4 : f4.bodyIdentity = RootBody.reflected.body.identity := identity
  have callee4 : f4.functionInstance = RootBody.reflected.functionInstance := callee
  have clocks4 : f4.extra.dataRace = none := noClocks
  have live0_4 : (f4.locals[0]'v0).value = .live (.immediate .uninit) := by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live0
  have none0_4 : (f4.locals[0]'v0).layout = none := by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using none0
  have live15_4 : (f4.locals[15]'v15).value = .live (.immediate temp15) := by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live15
  have live17_4 : (f4.locals[17]'v17).value = .live (.immediate .uninit) := by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live17
  have none17_4 : (f4.locals[17]'v17).layout = none := by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using none17
  generalize middleEq : f4 = middle at history4 sz4 v0 v15 v17 at4 body4 identity4 callee4 clocks4 live0_4 none0_4 live15_4 live17_4 none17_4
  let f5 := {(ActualLocalCopy.written middle 17 CopyHelperUnit.layout v17 .uninit) with location := .mir ⟨9,5⟩}
  have e5 := RootUnitAssignment.step options limits remaining span source debugOff fuel validationFuel .afterCopy
    framesBefore middle machine v17 .uninit live17_4 none17_4 body4 identity4 callee4 at4 clocks4 tracker tracked defaultMode ghostFalse shallow
  have sz5 : f5.locals.size = 25 := by simp [f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,sz4]
  have v17' : (17 : Miri.MIR.LocalId) < f5.locals.size := by rw [sz5];decide
  let s5 := block.statements[5]'(by with_unfolding_all decide +kernel)
  let f6 := SourceSteps.deadFrame f5 ⟨9,5⟩ 17 v17'
  have e6 := SourceSteps.storage_dead_exact config limits () framesBefore f5 machine ⟨9,5⟩ block s5
    17 .uninit rfl (by change middle.body.basicBlocks[9]? = _;rw [body4];simp [block])
    (by simp [s5]) (by with_unfolding_all rfl) v17' (by decide)
    (by simp [f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
  have sz6 : f6.locals.size = 25 := by simp [f6,SourceSteps.deadFrame,sz5]
  have v0' : (0 : Miri.MIR.LocalId) < f6.locals.size := by rw [sz6];decide
  let f7 := {(RootSuccessAssignment.successReturnFrame f6 v0') with location := .mir ⟨9,7⟩}
  have e7 := RootSuccessAssignment.step options limits remaining span source debugOff fuel validationFuel framesBefore f6 machine
    body4 identity4 callee4 rfl v0'
    (by simpa [f6,f5,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live0_4)
    (by simpa [f6,f5,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using none0_4)
    clocks4 tracker tracked defaultMode ghostFalse shallow
  have sz7 : f7.locals.size = 25 := by simp [f7,RootSuccessAssignment.successReturnFrame,RootSuccessAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,sz6]
  have v15' : (15 : Miri.MIR.LocalId) < f7.locals.size := by rw [sz7];decide
  let s7 := block.statements[7]'(by with_unfolding_all decide +kernel)
  let f8 := SourceSteps.deadFrame f7 ⟨9,7⟩ 15 v15'
  have e8 := SourceSteps.storage_dead_exact config limits () framesBefore f7 machine ⟨9,7⟩ block s7
    15 temp15 rfl (by change middle.body.basicBlocks[9]? = _;rw [body4];simp [block])
    (by simp [s7]) (by with_unfolding_all rfl) v15' (by decide)
    (by simpa [f7,RootSuccessAssignment.successReturnFrame,RootSuccessAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,
      f6,f5,SourceSteps.deadFrame,ActualLocalCopy.written,Array.getElem_set] using live15_4)
  have tail : SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore middle machine)
      (Storage.withCurrent framesBefore f8 machine) := .next e5 (.next e6 (.next e7 (.next e8 (.refl _))))
  have history := SuccessfulTrace.append history4 tail
  have resultEq : f8 = RootSuccessCleanupFacts.result frame CopyHelperUnit.layout RootCompilerFacts.boolLayout (.scalar (.fromBool true)) size := by
    subst middle
    simp only [f8, f7, f6, f5, success_frame_eq]
    rfl
  have facts := RootSuccessCleanupFacts.shape frame CopyHelperUnit.layout RootCompilerFacts.boolLayout (.scalar (.fromBool true)) size
  rw [← resultEq] at facts
  generalize finalEq : f8 = final at history facts
  exact ⟨final,history,facts⟩

#print axioms statements
end DuplicatePrefix.RootSuccessCleanup
