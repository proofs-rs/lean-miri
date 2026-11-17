import duplicate_prefix.RootUsizeAssignment
import duplicate_prefix.LocalDirectness
import duplicate_prefix.SuccessfulTrace
namespace DuplicatePrefix.RootCopyPreparation
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def result (frame : CompilerFrameContext.ActualFrame) (layout : LocalLayout)
    (value : Immediate Provenance) (size : frame.locals.size = 25) :=
  let f1 := SourceSteps.deadFrame frame ⟨8,0⟩ 23 (by rw [size];decide)
  let f2 := SourceSteps.deadFrame f1 ⟨8,1⟩ 22 (by simp [f1,SourceSteps.deadFrame,size])
  let f3 := SourceSteps.liveFrame f2 ⟨8,2⟩ 24 (by simp [f2,f1,SourceSteps.deadFrame,size])
  {(ActualLocalCopy.written f3 24 layout (by simp [f3,SourceSteps.liveFrame,f2,f1,SourceSteps.deadFrame,size]) value) with location := .mir ⟨8,4⟩}

structure Shape (before after : CompilerFrameContext.ActualFrame) (layout : LocalLayout) (value : Immediate Provenance) : Prop where
  body : after.body = before.body
  identity : after.bodyIdentity = before.bodyIdentity
  callee : after.functionInstance = before.functionInstance
  extra : after.extra = before.extra
  destination : after.returnPlace = before.returnPlace
  continuation : after.returnContinuation = before.returnContinuation
  varargs : after.vaList = before.vaList
  localsIdentity : after.localsIdentity = before.localsIdentity
  trackedCaller : after.trackCallerArg = before.trackCallerArg
  size : after.locals.size = 25
  location : after.location = .mir ⟨8,4⟩
  kept : ∀ id, id ≠ 22 → id ≠ 23 → id ≠ 24 → after.locals[id]? = before.locals[id]?
  count : after.locals[24]? = some ⟨.live (.immediate value),some layout⟩
  immediate : CopyHelperCleanup.AllImmediate before → CopyHelperCleanup.AllImmediate after

theorem shape (frame : CompilerFrameContext.ActualFrame) (layout : LocalLayout)
    (value : Immediate Provenance) (size : frame.locals.size = 25) :
    Shape frame (result frame layout value size) layout value := by
  constructor
  case immediate =>
    intro all
    unfold result
    apply LocalDirectness.written_at
    apply LocalDirectness.live
    apply LocalDirectness.dead
    apply LocalDirectness.dead
    exact all
  case kept =>
    intro id not22 not23 not24
    simp [result,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,
      Array.getElem?_set,Ne.symm not22,Ne.symm not23,Ne.symm not24]
  all_goals simp [result,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size]

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (count : UInt64) (temp22 temp23 : Immediate Provenance) (size : frame.locals.size = 25)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live22 : (frame.locals[22]'(by omega)).value = .live (.immediate temp22))
    (live23 : (frame.locals[23]'(by omega)).value = .live (.immediate temp23))
    (dead24 : (frame.locals[24]'(by omega)).value = .dead)
    (none24 : (frame.locals[24]'(by omega)).layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨8,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore done machine) ∧
      Shape frame done RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 count))) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[8]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[8]? = some block := by rw [body];simp [block]
  have v23 : (23 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let f1 := SourceSteps.deadFrame frame ⟨8,0⟩ 23 v23
  have e1 := SourceSteps.storage_dead_exact config limits () framesBefore frame machine ⟨8,0⟩ block stmt0
    23 temp23 location blockAt (by simp [stmt0]) (by with_unfolding_all rfl) v23 (by decide) live23
  have sz1 : f1.locals.size = 25 := by simp [f1,SourceSteps.deadFrame,size]
  have v22 : (22 : Miri.MIR.LocalId) < f1.locals.size := by rw [sz1];decide
  let stmt1 := block.statements[1]'(by with_unfolding_all decide +kernel)
  let f2 := SourceSteps.deadFrame f1 ⟨8,1⟩ 22 v22
  have e2 := SourceSteps.storage_dead_exact config limits () framesBefore f1 machine ⟨8,1⟩ block stmt1
    22 temp22 rfl blockAt (by simp [stmt1]) (by with_unfolding_all rfl) v22 (by decide)
    (by simpa [f1,SourceSteps.deadFrame,Array.getElem_set] using live22)
  have sz2 : f2.locals.size = 25 := by simp [f2,SourceSteps.deadFrame,sz1]
  have v24 : (24 : Miri.MIR.LocalId) < f2.locals.size := by rw [sz2];decide
  let stmt2 := block.statements[2]'(by with_unfolding_all decide +kernel)
  let f3 := SourceSteps.liveFrame f2 ⟨8,2⟩ 24 v24
  have e3 := SourceSteps.storage_live_exact config limits () framesBefore f2 machine ⟨8,2⟩ block stmt2
    24 5 rfl blockAt (by simp [stmt2]) (by with_unfolding_all rfl) v24
    (by change frame.body.locals[24]? = _;rw [body];with_unfolding_all rfl)
    (CanonicalConfigFacts.actual_storage_usize options () (remaining+1) span)
    (by simpa [f2,f1,SourceSteps.deadFrame,Array.getElem_set] using dead24) noClocks
  have sz3 : f3.locals.size = 25 := by simp [f3,SourceSteps.liveFrame,sz2]
  have v24' : (24 : Miri.MIR.LocalId) < f3.locals.size := by rw [sz3];decide
  let f4 := {(ActualLocalCopy.written f3 24 RootCompilerFacts.usizeLayout v24'
    (.scalar (.fromScalarInt (.ofUInt64 count)))) with location := .mir ⟨8,4⟩}
  have e4 := RootUsizeAssignment.step options limits remaining span debugOff fuel validationFuel
    framesBefore f3 machine count .copyCount (by rw [sz3];decide) v24'
    (by simpa [f3,SourceSteps.liveFrame,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using live2)
    (by simpa [f3,SourceSteps.liveFrame,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using cached2)
    (by simp [RootUsizeAssignment.destId,f3,SourceSteps.liveFrame])
    (by simpa [RootUsizeAssignment.destId,f3,SourceSteps.liveFrame,f2,f1,SourceSteps.deadFrame,Array.getElem_set] using none24)
    body identity callee rfl noClocks tracker tracked defaultMode ghostFalse shallow
  have history : SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
      (Storage.withCurrent framesBefore f4 machine) := .next e1 (.next e2 (.next e3 (.next e4 (.refl _))))
  have resultEq : f4 = result frame RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 count))) size := by rfl
  have facts := shape frame RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 count))) size
  rw [← resultEq] at facts
  generalize finalEq : f4 = final at history facts
  exact ⟨final,history,facts⟩

#print axioms shape
#print axioms executes
end DuplicatePrefix.RootCopyPreparation
