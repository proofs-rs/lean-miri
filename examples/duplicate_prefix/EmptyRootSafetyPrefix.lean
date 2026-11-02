import duplicate_prefix.EmptyRootSafetyPrelude
import duplicate_prefix.EmptyRootSafetyGuard
import duplicate_prefix.EmptyRootSafetyFalse
import duplicate_prefix.RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.EmptyRootSafetyPrefix
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
    (count : UInt64) (positive : count>0) (size : frame.locals.size=25)
    (temp12 : Immediate Provenance)
    (live12 : (frame.locals[12]'(by omega)).value=.live (.immediate temp12))
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live11 : (frame.locals[11]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))))
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
        (Storage.withCurrent #[] result (tick options remaining span (tick options remaining span (tick options remaining span machine)))) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧
      result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have valid (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  have halfZero : (0:UInt64)/2=0 := by decide +kernel
  have gt : count>(0:UInt64)/2 := by rw [halfZero];exact positive
  obtain ⟨p,pt,pa,pb,pi,pfn,pex,prp,prc,pva,pli,psz,pkeep,p13⟩ :=
    EmptyRootSafetyPrelude.executes options limits remaining span source debug fuel fuelEq #[] frame machine all size
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
  obtain ⟨g,gtRace,ga,gb,gi,gfn,gex,grp,grc,gva,gli,gsz,g8,g9,g10,g11,gkeep⟩ :=
    EmptyRootSafetyGuard.executes options limits remaining span source debug fuel fuelEq #[] pframe m1 0 count pa psz
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
  let gframe := {g with location:=FrameLocation.mir ⟨5,0⟩}
  let m2 := tick options remaining span m1
  have vg (i : Fin 25) : i.val<gframe.locals.size := by change i.val<g.locals.size;rw [gsz];exact i.isLt
  have gs (i : Fin 25) (n8 : i.val≠8) (n10 : i.val≠10) (n11 : i.val≠11) :
      (gframe.locals[i.val]'(vg i))=(pframe.locals[i.val]'(vp i)) := slot_eq _ _ _ _ _ (gkeep i.val n8 n10 n11)
  have g0 := (gs ⟨0,by decide⟩ (by decide) (by decide) (by decide)).trans (ps ⟨0,by decide⟩ (by decide) (by decide))
  have g7 := (gs ⟨7,by decide⟩ (by decide) (by decide) (by decide)).trans (ps ⟨7,by decide⟩ (by decide) (by decide))
  have slot8 : (gframe.locals[8]'(vg ⟨8,by decide⟩))=⟨.live (.immediate (.scalar (.fromBool (count>(0:UInt64)/2)))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vg ⟨8,by decide⟩)).symm.trans g8)
  have slot9 := slot_eq gframe.locals pframe.locals 9 (vg ⟨9,by decide⟩) (vp ⟨9,by decide⟩) g9
  have slot10 : (gframe.locals[10]'(vg ⟨10,by decide⟩))=⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 ((0:UInt64)/2))))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vg ⟨10,by decide⟩)).symm.trans g10)
  have ghost2 : m2.user.payload.ghost=false := (tick_ghost options remaining span m1).trans ghost1
  have shallow2 : m2.user.payload.validation=.Shallow := (tick_shallow options remaining span m1).trans shallow1
  have unchecked2 := (tick_flags options remaining span m1).1.trans unchecked1
  have noGc2 := (tick_flags options remaining span m1).2.trans noGc1
  obtain ⟨f,ft,fa,fb,fi,ffn,fex,frp,frc,fva,fli,fsz,f0,f1,f2⟩ :=
    EmptyRootSafetyFalse.reaches_return options limits remaining span source debug fuel fuelEq #[] gframe m2 ga gsz
      ((congrArg (fun row=>row.value) g0).trans live0) ((congrArg (fun row=>row.layout) g0).trans cache0)
      .uninit (.scalar (.fromBool (count>(0:UInt64)/2))) (.scalar (.fromScalarInt (.ofUInt64 count)))
      (.scalar (.fromScalarInt (.ofUInt64 ((0:UInt64)/2))))
      ((congrArg (fun row=>row.value) g7).trans live7) (congrArg (fun row=>row.value) slot8)
      ((congrArg (fun row=>row.value) (slot9.trans (ps ⟨9,by decide⟩ (by decide) (by decide)))).trans live9)
      (congrArg (fun row=>row.value) slot10) ((gb.trans pb).trans body) ((gi.trans pi).trans identity)
      ((gfn.trans pfn).trans callee) rfl ((congrArg (fun extra=>extra.dataRace) (gex.trans pex)).trans noClocks) tracker tracked mode ghost2 shallow2 unchecked2 noGc2 fixed
  let result := {f with location:=FrameLocation.mir ⟨10,0⟩}
  have pt' : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] pframe m1) := by
    simpa only [pframe,m1,tick,SourceControl.accounted,Storage.withCurrent] using pt
  have gt' : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] pframe m1) (Storage.withCurrent #[] gframe m2) := by
    simpa only [gframe,m2,tick,SourceControl.accounted,Storage.withCurrent,gt,ite_true] using gtRace
  have ft' : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] gframe m2)
      (Storage.withCurrent #[] result (tick options remaining span m2)) := by
    simpa only [result,tick,SourceControl.accounted,Storage.withCurrent] using ft
  exact ⟨result,SuccessfulTrace.append pt' (SuccessfulTrace.append gt' ft'),(fb.trans gb).trans pb,(fi.trans gi).trans pi,
    (ffn.trans gfn).trans pfn,(fex.trans gex).trans pex,(frp.trans grp).trans prp,(frc.trans grc).trans prc,
    (fva.trans gva).trans pva,(fli.trans gli).trans pli,fsz,rfl,f0,fa⟩

#print axioms executes
end DuplicatePrefix.EmptyRootSafetyPrefix
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.EmptyRootSafetyPrefix.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved empty positive-count false prefix dependency {dependency}"
