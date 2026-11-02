import duplicate_prefix.RootFalseBranch
import duplicate_prefix.CopyHelperCleanup
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.EmptyRootSafetyFalse
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
theorem reaches_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (allImmediate : CopyHelperCleanup.AllImmediate frame)
    (size : frame.locals.size = 25)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (temp7 temp8 temp9 temp10 : Immediate Provenance)
    (live7 : (frame.locals[7]'(by omega)).value = .live (.immediate temp7))
    (live8 : (frame.locals[8]'(by omega)).value = .live (.immediate temp8))
    (live9 : (frame.locals[9]'(by omega)).value = .live (.immediate temp9))
    (live10 : (frame.locals[10]'(by omega)).value = .live (.immediate temp10))
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨5,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ resultFrame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore {resultFrame with location := .mir ⟨10,0⟩}
          (SourceControl.accounted config.terminators (Storage.withCurrent framesBefore resultFrame machine)).machine) ∧
      CopyHelperCleanup.AllImmediate resultFrame ∧
      resultFrame.body = frame.body ∧ resultFrame.bodyIdentity = frame.bodyIdentity ∧
      resultFrame.functionInstance = frame.functionInstance ∧ resultFrame.extra = frame.extra ∧
      resultFrame.returnPlace = frame.returnPlace ∧ resultFrame.returnContinuation = frame.returnContinuation ∧
      resultFrame.vaList=frame.vaList ∧ resultFrame.localsIdentity=frame.localsIdentity ∧
      resultFrame.locals.size = 25 ∧
      resultFrame.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      resultFrame.locals[1]? = frame.locals[1]? ∧ resultFrame.locals[2]? = frame.locals[2]? := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[5]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[5]? = some block := by rw [body];simp [block]
  have v1 : (10 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let f1 := SourceSteps.deadFrame frame ⟨5,0⟩ 10 v1
  have step1 := SourceSteps.storage_dead_exact config limits () framesBefore frame machine ⟨5,0⟩ block stmt0
    10 temp10 location blockAt (by simp [stmt0]) (by with_unfolding_all rfl) v1 (by decide)
    (by simpa using live10)
  have size1 : f1.locals.size = 25 := by simp [f1,SourceSteps.deadFrame,size]
  have v2 : (9 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1];decide
  let stmt1 := block.statements[1]'(by with_unfolding_all decide +kernel)
  let f2 := SourceSteps.deadFrame f1 ⟨5,1⟩ 9 v2
  have step2 := SourceSteps.storage_dead_exact config limits () framesBefore f1 machine ⟨5,1⟩ block stmt1
    9 temp9 rfl blockAt (by simp [stmt1]) (by with_unfolding_all rfl) v2 (by decide)
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using live9)
  have size2 : f2.locals.size = 25 := by simp [f2,SourceSteps.deadFrame,size1]
  have valid0 : (0 : Miri.MIR.LocalId) < f2.locals.size := by rw [size2];decide
  have effect := RootFalseAssignment.evaluate options limits remaining span source debugOff fuel validationFuel
    framesBefore f2 machine body identity callee rfl valid0
    (by simpa [f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live0)
    (by simpa [f2,f1,SourceSteps.deadFrame,Array.getElem_set] using uncached0)
    noClocks tracker tracked defaultMode ghostFalse shallow
  let f3 := {(RootFalseAssignment.falseReturnFrame f2 valid0) with location := .mir ⟨5,3⟩}
  let stmt2 := block.statements[2]'(by with_unfolding_all decide +kernel)
  have step3 := SourceSteps.assign_exact config limits () framesBefore f2
    (RootFalseAssignment.falseReturnFrame f2 valid0) machine machine ⟨5,2⟩ block stmt2
    ⟨0,#[]⟩ (.Use (.Constant RootFalseConstant.constant) .Yes) rfl blockAt
    (by simp [stmt2]) (by with_unfolding_all rfl) effect rfl
  have size3 : f3.locals.size = 25 := by simp [f3,RootFalseAssignment.falseReturnFrame,RootFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,size2]
  have v4 : (8 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3];decide
  let stmt3 := block.statements[3]'(by with_unfolding_all decide +kernel)
  let f4 := SourceSteps.deadFrame f3 ⟨5,3⟩ 8 v4
  have step4 := SourceSteps.storage_dead_exact config limits () framesBefore f3 machine ⟨5,3⟩ block stmt3
    8 temp8 rfl blockAt (by simp [stmt3]) (by with_unfolding_all rfl) v4 (by decide)
    (by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,RootFalseAssignment.falseReturnFrame,
      RootFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live8)
  have size4 : f4.locals.size = 25 := by simp [f4,SourceSteps.deadFrame,size3]
  have v5 : (7 : Miri.MIR.LocalId) < f4.locals.size := by rw [size4];decide
  let stmt4 := block.statements[4]'(by with_unfolding_all decide +kernel)
  let f5 := SourceSteps.deadFrame f4 ⟨5,4⟩ 7 v5
  have step5 := SourceSteps.storage_dead_exact config limits () framesBefore f4 machine ⟨5,4⟩ block stmt4
    7 temp7 rfl blockAt (by simp [stmt4]) (by with_unfolding_all rfl) v5 (by decide)
    (by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,RootFalseAssignment.falseReturnFrame,
      RootFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live7)
  have size5 : f5.locals.size = 25 := by simp [f5,SourceSteps.deadFrame,size4]
  have step6 := SourceControl.goto_step config limits () framesBefore f5 machine ⟨5,5⟩ block 10 rfl blockAt
    (by with_unfolding_all rfl) ⟨#[],by with_unfolding_all rfl⟩
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have all1 : CopyHelperCleanup.AllImmediate f1 := CopyHelperCleanup.all_immediate_set frame 10 _ v1 allImmediate (by intro memory;simp)
  have all2 : CopyHelperCleanup.AllImmediate f2 := CopyHelperCleanup.all_immediate_set f1 9 _ v2 all1 (by intro memory;simp)
  have all3 : CopyHelperCleanup.AllImmediate f3 := by
    apply CopyHelperCleanup.all_immediate_set (RootFalseAssignment.cacheReturnLayout f2 valid0) 0 _
      (by simpa [RootFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using valid0)
      (CopyHelperCleanup.all_immediate_cache f2 0 RootCompilerFacts.boolLayout valid0 all2)
    intro memory
    simp
  have all4 : CopyHelperCleanup.AllImmediate f4 := CopyHelperCleanup.all_immediate_set f3 8 _ v4 all3 (by intro memory;simp)
  have all5 : CopyHelperCleanup.AllImmediate f5 := CopyHelperCleanup.all_immediate_set f4 7 _ v5 all4 (by intro memory;simp)
  refine ⟨f5, .next step1 (.next step2 (.next step3 (.next step4 (.next step5 (.next step6 (.refl _)))))), all5, ?_⟩
  simp [f5,f4,f3,f2,f1,SourceSteps.deadFrame,RootFalseAssignment.falseReturnFrame,
    RootFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,size,Array.getElem?_set,Array.getElem_set]

#print axioms reaches_return
end DuplicatePrefix.EmptyRootSafetyFalse
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.EmptyRootSafetyFalse.reaches_return) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved empty slice false-guard stage dependency {dependency}"
