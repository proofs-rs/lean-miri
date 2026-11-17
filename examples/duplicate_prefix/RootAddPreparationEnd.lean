import duplicate_prefix.RootAddPreparationStorage
import duplicate_prefix.RootPointerAssignment
import duplicate_prefix.RootPointerCastAssignment
import duplicate_prefix.RootUsizeAssignment
import duplicate_prefix.LocalDirectness
import duplicate_prefix.SevenSteps
namespace DuplicatePrefix.RootAddPreparationEnd
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationFuel : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (pointer : Scalar Provenance) (count : UInt64)
    (size : frame.locals.size=25)
    (live15 : (frame.locals[15]'(by omega)).value=.live (.immediate (.scalar pointer)))
    (cache15 : (frame.locals[15]'(by omega)).layout=some CopyCompilerFacts.destPointerLayout)
    (live20 : (frame.locals[20]'(by omega)).value=.live (.immediate (.scalar pointer)))
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (unused : ∀i(v:i<frame.locals.size),21≤i→i≤23→(frame.locals[i]'v)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨7,7⟩)
    (noClocks : frame.extra.dataRace=none) (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (mode : tracker.retagMode=.Default) (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (all : CopyHelperCleanup.AllImmediate frame) :
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames frame machine) (Storage.withCurrent frames result machine) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.trackCallerArg=frame.trackCallerArg ∧ result.locals.size=25 ∧ result.location=.mir ⟨7,13⟩ ∧
      result.locals[21]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[22]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[23]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀i,i≠20→i≠21→i≠22→i≠23→result.locals[i]?=frame.locals[i]?) ∧
      CopyHelperCleanup.AllImmediate result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[7]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[7]?=some block := by rw [body];simp [block]
  have init21 := unused 21 (by rw [size];decide) (by decide) (by decide)
  have init22 := unused 22 (by rw [size];decide) (by decide) (by decide)
  have init23 := unused 23 (by rw [size];decide) (by decide) (by decide)
  have v1 : (20:MIR.LocalId)<frame.locals.size := by simp [SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]
  let stmt1 := block.statements[7]'(by with_unfolding_all decide +kernel)
  let f1 := SourceSteps.deadFrame frame ⟨7,7⟩ 20 v1
  have step1 := SourceSteps.storage_dead_exact config limits () frames frame machine ⟨7,7⟩ block stmt1
    20 (.scalar pointer) location blockAt (by simp [stmt1]) (by with_unfolding_all rfl) v1 (by decide) live20
  have v2 : (21:MIR.LocalId)<f1.locals.size := by simp [f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]
  let stmt2 := block.statements[8]'(by with_unfolding_all decide +kernel)
  let f2 := SourceSteps.liveFrame f1 ⟨7,8⟩ 21 v2
  have step2 := SourceSteps.storage_live_exact config limits () frames f1 machine ⟨7,8⟩ block stmt2
    21 8 rfl blockAt (by simp [stmt2]) (by with_unfolding_all rfl) v2
    (by change frame.body.locals[21]?=_;rw [body];with_unfolding_all rfl) (RootAddPreparationStorage.storage_raw options (remaining+1) span 8 (by decide))
    (by simpa [f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23] using congrArg (fun row=>row.value) init21) noClocks
  have v3 : (22:MIR.LocalId)<f2.locals.size := by simp [f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]
  let stmt3 := block.statements[9]'(by with_unfolding_all decide +kernel)
  let f3 := SourceSteps.liveFrame f2 ⟨7,9⟩ 22 v3
  have step3 := SourceSteps.storage_live_exact config limits () frames f2 machine ⟨7,9⟩ block stmt3
    22 8 rfl blockAt (by simp [stmt3]) (by with_unfolding_all rfl) v3
    (by change frame.body.locals[22]?=_;rw [body];with_unfolding_all rfl) (RootAddPreparationStorage.storage_raw options (remaining+1) span 8 (by decide))
    (by simpa [f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23] using congrArg (fun row=>row.value) init22) noClocks
  have v4 : (22:MIR.LocalId)<f3.locals.size := by simp [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]
  let f4 := {ActualLocalCopy.written f3 22 CopyCompilerFacts.destPointerLayout v4 (.scalar pointer) with location:=FrameLocation.mir ⟨7,11⟩}
  have step4 := RootPointerAssignment.step options limits remaining span debugOff fuel validationFuel frames f3 machine pointer .addInput
    (by simp [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]) v4 (by simpa [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23] using live15) (by simpa [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23] using cache15)
    (by simp [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]) (by simp [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]) body identity callee rfl noClocks tracker tracked mode ghost shallow
  have v5 : (23:MIR.LocalId)<f4.locals.size := by simp [f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]
  let stmt5 := block.statements[11]'(by with_unfolding_all decide +kernel)
  let f5 := SourceSteps.liveFrame f4 ⟨7,11⟩ 23 v5
  have step5 := SourceSteps.storage_live_exact config limits () frames f4 machine ⟨7,11⟩ block stmt5
    23 5 rfl blockAt (by simp [stmt5]) (by with_unfolding_all rfl) v5
    (by change frame.body.locals[23]?=_;rw [body];with_unfolding_all rfl) (CanonicalConfigFacts.actual_storage_usize options () (remaining+1) span)
    (by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23] using congrArg (fun row=>row.value) init23) noClocks
  have v6 : (23:MIR.LocalId)<f5.locals.size := by simp [f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]
  let f6 := {ActualLocalCopy.written f5 23 RootCompilerFacts.usizeLayout v6 (.scalar (.fromScalarInt (.ofUInt64 count))) with location:=FrameLocation.mir ⟨7,13⟩}
  have step6 := RootUsizeAssignment.step options limits remaining span debugOff fuel validationFuel frames f5 machine count .addCount
    (by simp [f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]) v6 (by simpa [f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23] using live2) (by simpa [f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23] using cache2)
    (by simp [f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]) (by simp [f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,init21,init22,init23]) body identity callee rfl noClocks tracker tracked mode ghost shallow
  have history : SuccessfulTrace.Trace config limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames f6 machine) :=
    .next step1 (.next step2 (.next step3 (.next step4 (.next step5 (.next step6 (.refl _))))))
  have all1 : CopyHelperCleanup.AllImmediate f1 := LocalDirectness.dead frame ⟨7,7⟩ 20 v1 all
  have all2 : CopyHelperCleanup.AllImmediate f2 := LocalDirectness.live f1 ⟨7,8⟩ 21 v2 all1
  have all3 : CopyHelperCleanup.AllImmediate f3 := LocalDirectness.live f2 ⟨7,9⟩ 22 v3 all2
  have all4 : CopyHelperCleanup.AllImmediate f4 := LocalDirectness.written_at f3 22 CopyCompilerFacts.destPointerLayout (.scalar pointer) v4 ⟨7,11⟩ all3
  have all5 : CopyHelperCleanup.AllImmediate f5 := LocalDirectness.live f4 ⟨7,11⟩ 23 v5 all4
  have all6 : CopyHelperCleanup.AllImmediate f6 := LocalDirectness.written_at f5 23 RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 count))) v6 ⟨7,13⟩ all5
  generalize finalEq : f6=final at history all6
  refine ⟨final,history,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,all6⟩
  all_goals rw [←finalEq]
  all_goals simp [f6,f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set,size,Array.getElem?_set,init21,init22,init23]
  intro i n20 n21 n22 n23
  simp [Ne.symm n20,Ne.symm n21,Ne.symm n22,Ne.symm n23]

#print axioms executes
end DuplicatePrefix.RootAddPreparationEnd
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootAddPreparationEnd.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual add preparation dependency {dependency}"
