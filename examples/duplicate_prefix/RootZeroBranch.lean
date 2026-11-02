import duplicate_prefix.RootZeroSwitch
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.RootZeroBranch
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem reaches_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (size : frame.locals.size = 25)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live3 : (frame.locals[3]'(by omega)).value = .live (.immediate .uninit))
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate (.scalar (.fromBool true))))
    (live5 : (frame.locals[5]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))))
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨1,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ f1 f2 f3 f4 : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
        (Storage.withCurrent framesBefore f1 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f1 machine) =
        (Storage.withCurrent framesBefore f2 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f2 machine) =
        (Storage.withCurrent framesBefore f3 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f3 machine) =
        (Storage.withCurrent framesBefore f4 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f4 machine) =
        (Storage.withCurrent framesBefore {f4 with location := .mir ⟨10,0⟩}
          (SourceControl.accounted config.terminators (Storage.withCurrent framesBefore f4 machine)).machine,.ok true) ∧
      f4.body = frame.body ∧ f4.bodyIdentity = frame.bodyIdentity ∧ f4.functionInstance = frame.functionInstance ∧
      f4.extra = frame.extra ∧ f4.returnPlace = frame.returnPlace ∧ f4.returnContinuation = frame.returnContinuation ∧
      f4.vaList = frame.vaList ∧ f4.localsIdentity = frame.localsIdentity ∧ f4.locals.size = 25 ∧
      f4.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      f4.locals[1]? = frame.locals[1]? ∧ f4.locals[2]? = frame.locals[2]? ∧
      f4.locals[3]?.map (·.value) = some .dead ∧ f4.locals[4]?.map (·.value) = some .dead ∧
      f4.locals[5]?.map (·.value) = some .dead := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have v0 : (0 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v3 : (3 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v4 : (4 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v5 : (5 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let block := RootBody.reflected.body.body.basicBlocks[1]'(by with_unfolding_all decide +kernel)
  have blockAt : RootBody.reflected.body.body.basicBlocks[1]? = some block := by simp [block]
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let stmt1 := block.statements[1]'(by with_unfolding_all decide +kernel)
  let stmt2 := block.statements[2]'(by with_unfolding_all decide +kernel)
  let stmt3 := block.statements[3]'(by with_unfolding_all decide +kernel)
  have at0 : block.statements[0]? = some stmt0 := by simp [stmt0]
  have at1 : block.statements[1]? = some stmt1 := by simp [stmt1]
  have at2 : block.statements[2]? = some stmt2 := by simp [stmt2]
  have at3 : block.statements[3]? = some stmt3 := by simp [stmt3]
  have kind0 : stmt0.kind = .StorageDead 5 := by with_unfolding_all rfl
  have kind1 : stmt1.kind = .Assign ⟨0,#[]⟩ (.Use (.Constant RootZeroSwitch.trueConstant) .Yes) := by with_unfolding_all rfl
  have kind2 : stmt2.kind = .StorageDead 4 := by with_unfolding_all rfl
  have kind3 : stmt3.kind = .StorageDead 3 := by with_unfolding_all rfl
  let f1 := SourceSteps.deadFrame frame ⟨1,0⟩ 5 v5
  have step1 := SourceSteps.storage_dead_exact config limits () framesBefore frame machine ⟨1,0⟩ block stmt0 5
    (.scalar (.fromScalarInt (.ofUInt64 0))) location (by rw [body];exact blockAt) at0 kind0 v5 (by decide) live5
  have size1 : f1.locals.size = 25 := by simp [f1,SourceSteps.deadFrame,size]
  have v10 : (0 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1];decide
  have effect := RootZeroSwitch.actual_true_return_assignment options limits remaining span source debugOff fuel validationFuel
    framesBefore f1 machine body identity callee rfl v10
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using live0)
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using uncached0)
    noClocks tracker tracked defaultMode ghostFalse shallow
  let written := RootZeroSwitch.trueReturnFrame f1 v10
  let f2 := {written with location := .mir ⟨1,2⟩}
  have step2 := SourceSteps.assign_exact config limits () framesBefore f1 written machine machine ⟨1,1⟩ block stmt1
    ⟨0,#[]⟩ (.Use (.Constant RootZeroSwitch.trueConstant) .Yes) rfl
    (by change frame.body.basicBlocks[1]? = _;rw [body];exact blockAt) at1 kind1 effect rfl
  have size2 : f2.locals.size = 25 := by
    simp [f2,written,RootZeroSwitch.trueReturnFrame,RootZeroSwitch.cacheReturnLayout,LocalPlaces.cachePlaceLayout,size1]
  have v24 : (4 : Miri.MIR.LocalId) < f2.locals.size := by rw [size2];decide
  let f3 := SourceSteps.deadFrame f2 ⟨1,2⟩ 4 v24
  have step3 := SourceSteps.storage_dead_exact config limits () framesBefore f2 machine ⟨1,2⟩ block stmt2 4
    (.scalar (.fromBool true)) rfl (by change frame.body.basicBlocks[1]? = _;rw [body];exact blockAt) at2 kind2 v24 (by decide)
    (by simpa [f2,written,RootZeroSwitch.trueReturnFrame,RootZeroSwitch.cacheReturnLayout,LocalPlaces.cachePlaceLayout,
      f1,SourceSteps.deadFrame,Array.getElem_set] using live4)
  have size3 : f3.locals.size = 25 := by simp [f3,SourceSteps.deadFrame,size2]
  have v33 : (3 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3];decide
  let f4 := SourceSteps.deadFrame f3 ⟨1,3⟩ 3 v33
  have step4 := SourceSteps.storage_dead_exact config limits () framesBefore f3 machine ⟨1,3⟩ block stmt3 3 .uninit rfl
    (by change frame.body.basicBlocks[1]? = _;rw [body];exact blockAt) at3 kind3 v33 (by decide)
    (by simpa [f3,SourceSteps.deadFrame,f2,written,RootZeroSwitch.trueReturnFrame,RootZeroSwitch.cacheReturnLayout,
      LocalPlaces.cachePlaceLayout,f1,Array.getElem_set] using live3)
  have step5 := SourceControl.goto_step config limits () framesBefore f4 machine ⟨1,4⟩ block 10 rfl
    (by change frame.body.basicBlocks[1]? = _;rw [body];exact blockAt)
    (by with_unfolding_all rfl) (by exact ⟨#[],by with_unfolding_all rfl⟩)
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  refine ⟨f1,f2,f3,f4,step1,step2,step3,step4,step5,?_⟩
  simp [f4,SourceSteps.deadFrame,f3,f2,written,RootZeroSwitch.trueReturnFrame,RootZeroSwitch.cacheReturnLayout,
    LocalPlaces.cachePlaceLayout,f1,size,Array.getElem?_set,Array.getElem_set]

#print axioms reaches_return
end DuplicatePrefix.RootZeroBranch
