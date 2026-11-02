import duplicate_prefix.RootGuardStatements
import duplicate_prefix.RootGuardSwitch
import duplicate_prefix.SuccessfulTrace
namespace DuplicatePrefix.RootGuardBlock
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (len count : UInt64)
    (size : frame.locals.size = 25)
    (lenLive : (frame.locals[11]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))))
    (lenCached : (frame.locals[11]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (countLive : (frame.locals[9]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (countCached : (frame.locals[9]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (divLive : (frame.locals[10]'(by omega)).value = .live (.immediate .uninit))
    (divUncached : (frame.locals[10]'(by omega)).layout = none)
    (boolLive : (frame.locals[8]'(by omega)).value = .live (.immediate .uninit))
    (boolUncached : (frame.locals[8]'(by omega)).layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨4,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ resultFrame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits
        (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore
          {resultFrame with location := .mir ⟨if count > len/2 then 5 else 6,0⟩}
          (SourceControl.accounted config.terminators (Storage.withCurrent framesBefore resultFrame machine)).machine) ∧
      resultFrame.body = frame.body ∧ resultFrame.bodyIdentity = frame.bodyIdentity ∧
      resultFrame.functionInstance = frame.functionInstance ∧ resultFrame.extra = frame.extra ∧
      resultFrame.returnPlace = frame.returnPlace ∧ resultFrame.returnContinuation = frame.returnContinuation ∧
      resultFrame.locals.size = 25 ∧
      resultFrame.locals[8]? = some ⟨.live (.immediate (.scalar (.fromBool (count > len/2)))),some RootCompilerFacts.boolLayout⟩ ∧
      resultFrame.locals[9]? = frame.locals[9]? ∧
      resultFrame.locals[10]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 (len/2))))),some RootCompilerFacts.usizeLayout⟩ ∧
      resultFrame.locals[11]?.map (·.value) = some .dead := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have v8 : (8 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v10 : (10 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let f1 := {(ActualLocalCopy.written frame 10 RootCompilerFacts.usizeLayout v10
    (.scalar (.fromScalarInt (.ofUInt64 (len/2))))) with location := .mir ⟨4,1⟩}
  have step1 := RootGuardStatements.division options limits remaining span source debugOff fuel validationFuel
    framesBefore frame machine len (by rw [size];decide) v10 lenLive lenCached divLive divUncached
    body identity callee location noClocks ghostFalse shallow
  have size1 : f1.locals.size = 25 := by simp [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size]
  have v11 : (11 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1];decide
  let block := RootBody.reflected.body.body.basicBlocks[4]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[1]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[4]? = some block := by rw [body];simp [block]
  let f2 := SourceSteps.deadFrame f1 ⟨4,1⟩ 11 v11
  have step2 := SourceSteps.storage_dead_exact config limits () framesBefore f1 machine ⟨4,1⟩ block statement 11
    (.scalar (.fromScalarInt (.ofUInt64 len))) rfl blockAt
    (by simp [statement]) (by with_unfolding_all rfl) v11 (by decide)
    (by simpa [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using lenLive)
  have size2 : f2.locals.size = 25 := by simp [f2,SourceSteps.deadFrame,size1]
  have v28 : (8 : Miri.MIR.LocalId) < f2.locals.size := by rw [size2];decide
  let f3 := {(ActualLocalCopy.written f2 8 RootCompilerFacts.boolLayout v28
    (.scalar (.fromBool (count > len/2)))) with location := .mir ⟨4,3⟩}
  have step3 := RootGuardStatements.greater_than options limits remaining span debugOff fuel validationFuel
    framesBefore f2 machine count (len/2) (by rw [size2];decide) (by rw [size2];decide) v28
    (by simpa [f2,SourceSteps.deadFrame,f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using countLive)
    (by simp [f2,SourceSteps.deadFrame,f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set])
    (by simpa [f2,SourceSteps.deadFrame,f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using countCached)
    (by simp [f2,SourceSteps.deadFrame,f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set])
    (by simpa [f2,SourceSteps.deadFrame,f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using boolLive)
    (by simpa [f2,SourceSteps.deadFrame,f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using boolUncached)
    body identity callee noClocks ghostFalse shallow rfl
  have size3 : f3.locals.size = 25 := by simp [f3,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size2]
  have step4 := RootGuardSwitch.step options limits remaining span debugOff framesBefore f3 machine (count > len/2)
    body identity callee rfl size3 (by rw [size3];decide)
    (by simp [f3,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
    (by simp [f3,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
    noClocks ghostFalse unchecked noGc fixed
  refine ⟨f3, ?_, ?_⟩
  · have trace := SuccessfulTrace.Trace.next step1 (.next step2 (.next step3 (.next step4 (.refl _))))
    by_cases h : count > len/2 <;> simpa only [h,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false] using trace
  · simp [f3,f2,f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,SourceSteps.deadFrame,
      size]

#print axioms executes
end DuplicatePrefix.RootGuardBlock
