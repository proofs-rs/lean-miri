import duplicate_prefix.RootAddPreparationStart
import duplicate_prefix.RootAddPreparationEnd
import duplicate_prefix.RootPointerAssignment
import duplicate_prefix.RootPointerCastAssignment
import duplicate_prefix.RootUsizeAssignment
import duplicate_prefix.LocalDirectness
import duplicate_prefix.SevenSteps
namespace DuplicatePrefix.RootAddPreparation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem executes_tracked
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationFuel : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (pointer : Scalar Provenance) (count : UInt64) (temp16 : Immediate Provenance)
    (size : frame.locals.size=25)
    (live15 : (frame.locals[15]'(by omega)).value=.live (.immediate (.scalar pointer)))
    (cache15 : (frame.locals[15]'(by omega)).layout=some CopyCompilerFacts.destPointerLayout)
    (live16 : (frame.locals[16]'(by omega)).value=.live (.immediate temp16))
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
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
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.trackCallerArg=frame.trackCallerArg ∧ result.locals.size=25 ∧ result.location=.mir ⟨7,13⟩ ∧
      result.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[22]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[23]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀i,i<16 ∨ 23<i→result.locals[i]?=frame.locals[i]?) ∧
      CopyHelperCleanup.AllImmediate result := by
  obtain ⟨p,pt,pb,pi,pfn,pex,prp,prc,pva,pli,ptrack,psz,ploc,p17,p18,p19,p20,pkeep,pa⟩ :=
    RootAddPreparationStart.executes options limits remaining span debugOff fuel validationFuel frames frame machine pointer temp16 size
      live15 cache15 live16 unused body identity callee location noClocks tracker tracked mode ghost shallow all
  have vp (i : Fin 25) : i.val<p.locals.size := by rw [psz];exact i.isLt
  have vo (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  have same (n : Fin 25) (n16 : n.val≠16) (n17 : n.val≠17) (n18 : n.val≠18) (n19 : n.val≠19) (n20 : n.val≠20) :
      (p.locals[n.val]'(vp n))=(frame.locals[n.val]'(vo n)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp n)).symm.trans ((pkeep n.val n16 n17 n18 n19 n20).trans (Array.getElem?_eq_getElem (vo n))))
  have same15 := same ⟨15,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have same2 := same ⟨2,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have cell20 : (p.locals[20]'(vp ⟨20,by decide⟩))=⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨20,by decide⟩)).symm.trans p20)
  have pu : ∀i(v:i<p.locals.size),21≤i→i≤23→(p.locals[i]'v)=⟨.dead,none⟩ := by
    intro i valid low high
    have old : i<frame.locals.size := by omega
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid,pkeep i (by omega) (by omega) (by omega) (by omega) (by omega),Array.getElem?_eq_getElem old,unused i old (by omega) high]
  obtain ⟨r,rt,rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,rloc,r21,r22,r23,rkeep,ra⟩ :=
    RootAddPreparationEnd.executes options limits remaining span debugOff fuel validationFuel frames p machine pointer count psz
      (by rw [same15];exact live15) (by rw [same15];exact cache15) (by rw [cell20])
      (by rw [same2];exact live2) (by rw [same2];exact cache2) pu
      (pb.trans body) (pi.trans identity) (pfn.trans callee) ploc (by rw [pex];exact noClocks) tracker tracked mode ghost shallow pa
  refine ⟨r,SuccessfulTrace.append pt rt,rb.trans pb,ri.trans pi,rfn.trans pfn,rex.trans pex,rrp.trans prp,rrc.trans prc,
    rva.trans pva,rli.trans pli,rtrack.trans ptrack,rsz,rloc,?_,?_,?_,r21,r22,r23,?_,ra⟩
  · exact (rkeep 17 (by decide) (by decide) (by decide) (by decide)).trans p17
  · exact (rkeep 18 (by decide) (by decide) (by decide) (by decide)).trans p18
  · exact (rkeep 19 (by decide) (by decide) (by decide) (by decide)).trans p19
  · intro i range
    exact (rkeep i (by omega) (by omega) (by omega) (by omega)).trans (pkeep i (by omega) (by omega) (by omega) (by omega) (by omega))

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationFuel : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (pointer : Scalar Provenance) (count : UInt64) (temp16 : Immediate Provenance)
    (size : frame.locals.size=25)
    (live15 : (frame.locals[15]'(by omega)).value=.live (.immediate (.scalar pointer)))
    (cache15 : (frame.locals[15]'(by omega)).layout=some CopyCompilerFacts.destPointerLayout)
    (live16 : (frame.locals[16]'(by omega)).value=.live (.immediate temp16))
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
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
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧ result.location=.mir ⟨7,13⟩ ∧
      result.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[22]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[23]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀i,i<16 ∨ 23<i→result.locals[i]?=frame.locals[i]?) ∧
      CopyHelperCleanup.AllImmediate result := by
  obtain ⟨r,rt,rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,rloc,r17,r18,r19,r21,r22,r23,rkeep,ra⟩ :=
    executes_tracked options limits remaining span debugOff fuel validationFuel frames frame machine pointer count temp16 size
      live15 cache15 live16 live2 cache2 unused body identity callee location noClocks tracker tracked mode ghost shallow all
  exact ⟨r,rt,rb,ri,rfn,rex,rrp,rrc,rva,rli,rsz,rloc,r17,r18,r19,r21,r22,r23,rkeep,ra⟩

#print axioms executes
end DuplicatePrefix.RootAddPreparation
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootAddPreparation.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual full add preparation dependency {dependency}"
