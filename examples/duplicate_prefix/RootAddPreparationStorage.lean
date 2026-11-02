import duplicate_prefix.RootPointerAssignment
import duplicate_prefix.RootPointerCastAssignment
import duplicate_prefix.RootUsizeAssignment
import duplicate_prefix.LocalDirectness
import duplicate_prefix.SevenSteps
namespace DuplicatePrefix.RootAddPreparationStorage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem storage_raw (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ty : TyId) (raw : ty=8 ∨ ty=9) :
    (PreparedContracts.actualConfig options () remaining span).lifecycle.storage.veryTriviallySized ty=.ok true := by
  rcases raw with rfl|rfl <;> rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage] <;> with_unfolding_all rfl

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationFuel : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (pointer : Scalar Provenance) (temp16 : Immediate Provenance)
    (size : frame.locals.size=25)
    (live15 : (frame.locals[15]'(by omega)).value=.live (.immediate (.scalar pointer)))
    (cache15 : (frame.locals[15]'(by omega)).layout=some CopyCompilerFacts.destPointerLayout)
    (live16 : (frame.locals[16]'(by omega)).value=.live (.immediate temp16))
    (unused : ∀i(v:i<frame.locals.size),17≤i→i≤23→(frame.locals[i]'v)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨7,0⟩)
    (noClocks : frame.extra.dataRace=none) (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (mode : tracker.retagMode=.Default) (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (all : CopyHelperCleanup.AllImmediate frame) :
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames frame machine) (Storage.withCurrent frames result machine) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.trackCallerArg=frame.trackCallerArg ∧ result.locals.size=25 ∧ result.location=.mir ⟨7,5⟩ ∧
      result.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[20]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      (∀i,i≠16→i≠17→i≠18→i≠19→i≠20→result.locals[i]?=frame.locals[i]?) ∧
      CopyHelperCleanup.AllImmediate result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[7]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[7]?=some block := by rw [body];simp [block]
  have init17 := unused 17 (by rw [size];decide) (by decide) (by decide)
  have init18 := unused 18 (by rw [size];decide) (by decide) (by decide)
  have init19 := unused 19 (by rw [size];decide) (by decide) (by decide)
  have init20 := unused 20 (by rw [size];decide) (by decide) (by decide)
  have init21 := unused 21 (by rw [size];decide) (by decide) (by decide)
  have init22 := unused 22 (by rw [size];decide) (by decide) (by decide)
  have init23 := unused 23 (by rw [size];decide) (by decide) (by decide)
  have v1 : (16:MIR.LocalId)<frame.locals.size := by simp [SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size]
  let stmt1 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let f1 := SourceSteps.deadFrame frame ⟨7,0⟩ 16 v1
  have step1 := SourceSteps.storage_dead_exact config limits () frames frame machine ⟨7,0⟩ block stmt1
    16 temp16 location blockAt (by simp [stmt1]) (by with_unfolding_all rfl) v1 (by decide) live16
  have v2 : (17:MIR.LocalId)<f1.locals.size := by simp [f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size]
  let stmt2 := block.statements[1]'(by with_unfolding_all decide +kernel)
  let f2 := SourceSteps.liveFrame f1 ⟨7,1⟩ 17 v2
  have step2 := SourceSteps.storage_live_exact config limits () frames f1 machine ⟨7,1⟩ block stmt2
    17 2 rfl blockAt (by simp [stmt2]) (by with_unfolding_all rfl) v2
    (by change frame.body.locals[17]?=_;rw [body];with_unfolding_all rfl) (CanonicalConfigFacts.actual_storage_type2 options () (remaining+1) span)
    (by simpa [f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size] using congrArg (fun row=>row.value) init17) noClocks
  have v3 : (18:MIR.LocalId)<f2.locals.size := by simp [f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size]
  let stmt3 := block.statements[2]'(by with_unfolding_all decide +kernel)
  let f3 := SourceSteps.liveFrame f2 ⟨7,2⟩ 18 v3
  have step3 := SourceSteps.storage_live_exact config limits () frames f2 machine ⟨7,2⟩ block stmt3
    18 2 rfl blockAt (by simp [stmt3]) (by with_unfolding_all rfl) v3
    (by change frame.body.locals[18]?=_;rw [body];with_unfolding_all rfl) (CanonicalConfigFacts.actual_storage_type2 options () (remaining+1) span)
    (by simpa [f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size] using congrArg (fun row=>row.value) init18) noClocks
  have v4 : (19:MIR.LocalId)<f3.locals.size := by simp [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size]
  let stmt4 := block.statements[3]'(by with_unfolding_all decide +kernel)
  let f4 := SourceSteps.liveFrame f3 ⟨7,3⟩ 19 v4
  have step4 := SourceSteps.storage_live_exact config limits () frames f3 machine ⟨7,3⟩ block stmt4
    19 9 rfl blockAt (by simp [stmt4]) (by with_unfolding_all rfl) v4
    (by change frame.body.locals[19]?=_;rw [body];with_unfolding_all rfl) (storage_raw options (remaining+1) span 9 (by decide))
    (by simpa [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size] using congrArg (fun row=>row.value) init19) noClocks
  have v5 : (20:MIR.LocalId)<f4.locals.size := by simp [f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size]
  let stmt5 := block.statements[4]'(by with_unfolding_all decide +kernel)
  let f5 := SourceSteps.liveFrame f4 ⟨7,4⟩ 20 v5
  have step5 := SourceSteps.storage_live_exact config limits () frames f4 machine ⟨7,4⟩ block stmt5
    20 8 rfl blockAt (by simp [stmt5]) (by with_unfolding_all rfl) v5
    (by change frame.body.locals[20]?=_;rw [body];with_unfolding_all rfl) (storage_raw options (remaining+1) span 8 (by decide))
    (by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootPointerAssignment.destId,RootPointerAssignment.siteLocation,Array.getElem_set,size] using congrArg (fun row=>row.value) init20) noClocks
  have history : SuccessfulTrace.Trace config limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames f5 machine) :=
    .next step1 (.next step2 (.next step3 (.next step4 (.next step5 (.refl _)))))
  have all1 : CopyHelperCleanup.AllImmediate f1 := LocalDirectness.dead frame ⟨7,0⟩ 16 v1 all
  have all2 : CopyHelperCleanup.AllImmediate f2 := LocalDirectness.live f1 ⟨7,1⟩ 17 v2 all1
  have all3 : CopyHelperCleanup.AllImmediate f3 := LocalDirectness.live f2 ⟨7,2⟩ 18 v3 all2
  have all4 : CopyHelperCleanup.AllImmediate f4 := LocalDirectness.live f3 ⟨7,3⟩ 19 v4 all3
  have all5 : CopyHelperCleanup.AllImmediate f5 := LocalDirectness.live f4 ⟨7,4⟩ 20 v5 all4
  generalize finalEq : f5=final at history all5
  refine ⟨final,history,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,all5⟩
  all_goals rw [←finalEq]
  all_goals simp [f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,size,Array.getElem?_set,init17,init18,init19,init20]
  intro i n16 n17 n18 n19 n20
  simp [Ne.symm n16,Ne.symm n17,Ne.symm n18,Ne.symm n19,Ne.symm n20]

#print axioms executes
end DuplicatePrefix.RootAddPreparationStorage
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootAddPreparationStorage.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual add preparation dependency {dependency}"
