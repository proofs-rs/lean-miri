import duplicate_prefix.RootDivisionPrelude
import duplicate_prefix.CopyHelperCleanup
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.EmptyRootSafetyPrelude
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (allImmediate : CopyHelperCleanup.AllImmediate frame)
    (size : frame.locals.size = 25)
    (temp12 : Immediate Provenance)
    (live12 : (frame.locals[12]'(by omega)).value = .live (.immediate temp12))
    (live13 : (frame.locals[13]'(by omega)).value = .live (.immediate .uninit))
    (uncached13 : (frame.locals[13]'(by omega)).layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨3,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ resultFrame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore {resultFrame with location := .mir ⟨4,0⟩}
          (SourceControl.accounted config.terminators (Storage.withCurrent framesBefore resultFrame machine)).machine) ∧
      CopyHelperCleanup.AllImmediate resultFrame ∧
      resultFrame.body = frame.body ∧ resultFrame.bodyIdentity = frame.bodyIdentity ∧
      resultFrame.functionInstance = frame.functionInstance ∧ resultFrame.extra = frame.extra ∧
      resultFrame.returnPlace = frame.returnPlace ∧ resultFrame.returnContinuation = frame.returnContinuation ∧
      resultFrame.vaList=frame.vaList ∧ resultFrame.localsIdentity=frame.localsIdentity ∧
      resultFrame.locals.size = 25 ∧
      (∀ id, id ≠ 12 → id ≠ 13 → resultFrame.locals[id]? = frame.locals[id]?) ∧
      resultFrame.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have v12 : (12 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let block := RootBody.reflected.body.body.basicBlocks[3]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[3]? = some block := by rw [body];simp [block]
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let f1 := SourceSteps.deadFrame frame ⟨3,0⟩ 12 v12
  have step1 := SourceSteps.storage_dead_exact config limits () framesBefore frame machine ⟨3,0⟩ block stmt0
    12 temp12 location blockAt (by simp [stmt0]) (by with_unfolding_all rfl) v12 (by decide) live12
  have size1 : f1.locals.size = 25 := by simp [f1,SourceSteps.deadFrame,size]
  have v13 : (13 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1];decide
  have effect := RootDivisionCheck.evaluate options limits remaining span source debugOff fuel validationFuel
    framesBefore f1 machine v13
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using live13)
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using uncached13)
    body identity callee rfl noClocks ghostFalse shallow
  let written := ActualLocalCopy.written f1 13 RootCompilerFacts.boolLayout v13 (.scalar (.fromBool false))
  let f2 := {written with location := .mir ⟨3,2⟩}
  let stmt1 := block.statements[1]'(by with_unfolding_all decide +kernel)
  have step2 := SourceSteps.assign_exact config limits () framesBefore f1 written machine machine ⟨3,1⟩ block stmt1
    ⟨13,#[]⟩ (.BinaryOp .Eq (.Constant RootDivisionCheckTwo.constant) (.Constant RootDivisionCheckZero.constant))
    rfl blockAt (by simp [stmt1]) (by with_unfolding_all rfl) effect rfl
  have size2 : f2.locals.size = 25 := by simp [f2,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size1]
  have step3 := RootDivisionAssert.step options limits remaining span debugOff framesBefore f2 machine
    body identity callee rfl size2 (by rw [size2];decide)
    (by simp [f2,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
    (by simp [f2,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
    noClocks ghostFalse unchecked noGc fixed
  have all1 : CopyHelperCleanup.AllImmediate f1 := CopyHelperCleanup.all_immediate_set frame 12 _ v12 allImmediate (by intro memory;simp)
  have all2 : CopyHelperCleanup.AllImmediate f2 := CopyHelperCleanup.all_immediate_written f1 13 RootCompilerFacts.boolLayout
    (.scalar (.fromBool false)) v13 all1
  refine ⟨f2,.next step1 (.next step2 (.next step3 (.refl _))),all2,?_⟩
  simp [f2,written,f1,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size,
    Array.getElem?_set]
  intro id not12 not13
  simp [Ne.symm not12,Ne.symm not13]

#print axioms executes
end DuplicatePrefix.EmptyRootSafetyPrelude
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.EmptyRootSafetyPrelude.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved empty slice false-guard stage dependency {dependency}"
