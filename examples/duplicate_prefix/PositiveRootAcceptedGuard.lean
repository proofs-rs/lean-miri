import duplicate_prefix.PositiveRootGuardPrelude
import duplicate_prefix.PositiveRootGuardBlock
import duplicate_prefix.EmptyRootSafetyFalse
import duplicate_prefix.RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PositiveRootAcceptedGuard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootZeroCompleteState
private theorem slot_eq (a b : Array α) (i : Nat) (va : i<a.size) (vb : i<b.size)
    (same : a[i]?=b[i]?) : (a[i]'va)=(b[i]'vb) :=
  Option.some.inj ((Array.getElem?_eq_getElem va).symm.trans (same.trans (Array.getElem?_eq_getElem vb)))

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (within : count≤len/2) (size : frame.locals.size=25)
    (temp12 : Immediate Provenance)
    (live12 : (frame.locals[12]'(by omega)).value=.live (.immediate temp12))
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live11 : (frame.locals[11]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))))
    (cache11 : (frame.locals[11]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨3,0⟩)
    (all : CopyHelperCleanup.AllImmediate frame) (noClocks : frame.extra.dataRace=none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (tick options remaining span (tick options remaining span machine))) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.trackCallerArg=frame.trackCallerArg ∧
      result.locals.size=25 ∧ result.location=.mir ⟨6,0⟩ ∧
      result.locals[8]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.locals[10]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 (len/2))))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[13]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      (∀i,i≠8→i≠10→i≠11→i≠12→i≠13→result.locals[i]?=frame.locals[i]?) ∧
      CopyHelperCleanup.AllImmediate result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have valid (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  obtain ⟨p,pt,pa,pb,pi,pfn,pex,prp,prc,pva,pli,ptrack,psz,pkeep,p13⟩ :=
    PositiveRootGuardPrelude.executes options limits remaining span source debug fuel fuelEq #[] frame machine all size
      temp12 live12 live13 cache13 body identity callee location noClocks ghost shallow unchecked noGc fixed
  let pframe := {p with location:=FrameLocation.mir ⟨4,0⟩}
  let m1 := tick options remaining span machine
  have vp (i : Fin 25) : i.val<pframe.locals.size := by change i.val<p.locals.size;rw [psz];exact i.isLt
  have ps (i : Fin 25) (n12 : i.val≠12) (n13 : i.val≠13) :
      (pframe.locals[i.val]'(vp i))=(frame.locals[i.val]'(valid i)) := slot_eq _ _ _ _ _ (pkeep i.val n12 n13)
  have ghost1 : m1.user.payload.ghost=false := (tick_ghost options remaining span machine).trans ghost
  have shallow1 : m1.user.payload.validation=.Shallow := (tick_shallow options remaining span machine).trans shallow
  have unchecked1 := (tick_flags options remaining span machine).1.trans unchecked
  have noGc1 := (tick_flags options remaining span machine).2.trans noGc
  obtain ⟨g,gtRace,ga,gb,gi,gfn,gex,grp,grc,gva,gli,gtrack,gsz,g8,g9,g10,g11,gkeep⟩ :=
    PositiveRootGuardBlock.executes options limits remaining span source debug fuel fuelEq #[] pframe m1 len count pa psz
      ((congrArg (fun row=>row.value) (ps ⟨11,by decide⟩ (by decide) (by decide))).trans live11)
      ((congrArg (fun row=>row.layout) (ps ⟨11,by decide⟩ (by decide) (by decide))).trans cache11)
      ((congrArg (fun row=>row.value) (ps ⟨9,by decide⟩ (by decide) (by decide))).trans live9)
      ((congrArg (fun row=>row.layout) (ps ⟨9,by decide⟩ (by decide) (by decide))).trans cache9)
      ((congrArg (fun row=>row.value) (ps ⟨10,by decide⟩ (by decide) (by decide))).trans live10)
      ((congrArg (fun row=>row.layout) (ps ⟨10,by decide⟩ (by decide) (by decide))).trans cache10)
      ((congrArg (fun row=>row.value) (ps ⟨8,by decide⟩ (by decide) (by decide))).trans live8)
      ((congrArg (fun row=>row.layout) (ps ⟨8,by decide⟩ (by decide) (by decide))).trans cache8)
      (pb.trans body) (pi.trans identity) (pfn.trans callee) rfl ((congrArg (fun extra=>extra.dataRace) pex).trans noClocks)
      ghost1 shallow1 unchecked1 noGc1 fixed
  let result := {g with location:=FrameLocation.mir ⟨6,0⟩}
  let m2 := tick options remaining span m1
  have notGt : ¬count>len/2 := by
    intro h
    have hlt := UInt64.lt_iff_toNat_lt.mp h
    have hle := UInt64.le_iff_toNat_le.mp within
    omega
  have pt' : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] pframe m1) := by
    simpa only [pframe,m1,tick,SourceControl.accounted,Storage.withCurrent] using pt
  have gt' : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] pframe m1) (Storage.withCurrent #[] result m2) := by
    simpa only [result,m2,tick,SourceControl.accounted,Storage.withCurrent,notGt,ite_false] using gtRace
  refine ⟨result,SuccessfulTrace.append pt' gt',gb.trans pb,gi.trans pi,gfn.trans pfn,gex.trans pex,grp.trans prp,grc.trans prc,
    gva.trans pva,gli.trans pli,gtrack.trans ptrack,gsz,rfl,?_,g10,?_,?_,ga⟩
  · simpa only [notGt,decide_false] using g8
  · exact (gkeep 13 (by decide) (by decide) (by decide)).trans p13
  · intro i n8 n10 n11 n12 n13
    exact (gkeep i n8 n10 n11).trans (pkeep i n12 n13)

#print axioms executes
end DuplicatePrefix.PositiveRootAcceptedGuard
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootAcceptedGuard.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual accepted guard dependency {dependency}"
