import duplicate_prefix.RootAddPreparationStorage
import duplicate_prefix.RootPointerAssignment
import duplicate_prefix.RootPointerCastAssignment
import duplicate_prefix.RootUsizeAssignment
import duplicate_prefix.LocalDirectness
import duplicate_prefix.SevenSteps
namespace DuplicatePrefix.RootAddPreparationStart
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

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
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.trackCallerArg=frame.trackCallerArg ∧ result.locals.size=25 ∧ result.location=.mir ⟨7,7⟩ ∧
      result.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[20]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      (∀i,i≠16→i≠17→i≠18→i≠19→i≠20→result.locals[i]?=frame.locals[i]?) ∧
      CopyHelperCleanup.AllImmediate result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨p,pt,pb,pi,pfn,pex,prp,prc,pva,pli,ptrack,psz,ploc,p17,p18,p19,p20,pkeep,pa⟩ :=
    RootAddPreparationStorage.executes options limits remaining span debugOff fuel validationFuel frames frame machine pointer temp16 size
      live15 cache15 live16 unused body identity callee location noClocks tracker tracked mode ghost shallow all
  have vp (i : Fin 25) : i.val<p.locals.size := by rw [psz];exact i.isLt
  have vo (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  have same15 : (p.locals[15]'(vp ⟨15,by decide⟩))=(frame.locals[15]'(vo ⟨15,by decide⟩)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨15,by decide⟩)).symm.trans
      ((pkeep 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (Array.getElem?_eq_getElem (vo ⟨15,by decide⟩))))
  have cell (n : Fin 25) {row : LocalState Provenance LocalLayout} (known : p.locals[n.val]?=some row) : (p.locals[n.val]'(vp n))=row :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp n)).symm.trans known)
  have cell19 := cell ⟨19,by decide⟩ p19
  have cell20 := cell ⟨20,by decide⟩ p20
  let f1 := {ActualLocalCopy.written p 20 CopyCompilerFacts.destPointerLayout (vp ⟨20,by decide⟩) (.scalar pointer) with location:=FrameLocation.mir ⟨7,6⟩}
  have step1 := RootPointerAssignment.step options limits remaining span debugOff fuel validationFuel frames p machine pointer .castInput
    (vp ⟨15,by decide⟩) (vp ⟨20,by decide⟩) (by rw [same15];exact live15) (by rw [same15];exact cache15)
    (by simpa only [RootPointerAssignment.destId] using congrArg (fun row=>row.value) cell20) (by simpa only [RootPointerAssignment.destId] using congrArg (fun row=>row.layout) cell20) (pb.trans body) (pi.trans identity) (pfn.trans callee) ploc (by rw [pex];exact noClocks)
    tracker tracked mode ghost shallow
  have v19 : (19:MIR.LocalId)<f1.locals.size := by simp [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,psz]
  have v20 : (20:MIR.LocalId)<f1.locals.size := by simp [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,psz]
  let f2 := {ActualLocalCopy.written f1 19 CopyCompilerFacts.sourcePointerLayout v19 (.scalar pointer) with location:=FrameLocation.mir ⟨7,7⟩}
  have step2 := RootPointerCastAssignment.step options limits remaining span debugOff fuel validationFuel frames f1 machine pointer v19 v20
    (by simpa [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using congrArg (fun row=>row.value) cell19)
    (by simpa [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using congrArg (fun row=>row.layout) cell19)
    (by simp [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]) (by simp [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
    (pb.trans body) (pi.trans identity) (pfn.trans callee) rfl (by change p.extra.dataRace=none;rw [pex];exact noClocks) ghost shallow
  have history : SuccessfulTrace.Trace config limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames f2 machine) :=
    SuccessfulTrace.append pt (.next step1 (.next step2 (.refl _)))
  have all1 : CopyHelperCleanup.AllImmediate f1 := LocalDirectness.written_at p 20 CopyCompilerFacts.destPointerLayout (.scalar pointer) (vp ⟨20,by decide⟩) ⟨7,6⟩ pa
  have all2 : CopyHelperCleanup.AllImmediate f2 := LocalDirectness.written_at f1 19 CopyCompilerFacts.sourcePointerLayout (.scalar pointer) v19 ⟨7,7⟩ all1
  generalize finalEq : f2=final at history all2
  refine ⟨final,history,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,all2⟩
  all_goals rw [←finalEq]
  all_goals simp only [f2,f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set,Array.getElem?_set,Array.getElem_set]
  all_goals try first | exact pb | exact pi | exact pfn | exact pex | exact prp | exact prc | exact pva | exact pli | exact ptrack | exact psz | rfl
  all_goals try simp only [Nat.reduceEqDiff,eq_self_iff_true,ite_false,ite_true]
  all_goals try first | exact p17 | exact p18 | rfl
  intro i n16 n17 n18 n19 n20
  simpa [Ne.symm n19,Ne.symm n20] using pkeep i n16 n17 n18 n19 n20

#print axioms executes
end DuplicatePrefix.RootAddPreparationStart
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootAddPreparationStart.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual add preparation dependency {dependency}"
