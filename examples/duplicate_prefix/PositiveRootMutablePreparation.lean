import duplicate_prefix.PositiveRootAcceptedGuard
import duplicate_prefix.RootMutPreparation
import duplicate_prefix.PositiveRootGuardBlock
import duplicate_prefix.EmptyRootSafetyFalse
import duplicate_prefix.RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PositiveRootMutablePreparation
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
    (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)
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
      result.locals.size=25 ∧ result.location=.mir ⟨6,7⟩ ∧
      result.locals[0]?=frame.locals[0]? ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[13]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      (∀i,17≤i→result.locals[i]?=frame.locals[i]?) ∧ CopyHelperCleanup.AllImmediate result := by
  obtain ⟨g,gt,gb,gi,gfn,gex,grp,grc,gva,gli,gtrack,gsz,gloc,g8,g10,g13,gkeep,ga⟩ :=
    PositiveRootAcceptedGuard.executes options limits remaining span source debug fuel fuelEq frame machine len count within size
      temp12 live12 live13 cache13 live0 cache0 live7 live8 cache8 live9 cache9 live10 cache10 live11 cache11
      body identity callee location all noClocks tracker tracked mode ghost shallow unchecked noGc fixed
  let m2 := tick options remaining span (tick options remaining span machine)
  have vg (i : Fin 25) : i.val<g.locals.size := by rw [gsz];exact i.isLt
  have vo (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  have same (i : Fin 25) (n8 : i.val≠8) (n10 : i.val≠10) (n11 : i.val≠11) (n12 : i.val≠12) (n13 : i.val≠13) :
      (g.locals[i.val]'(vg i))=(frame.locals[i.val]'(vo i)) := slot_eq _ _ _ _ _ (gkeep i.val n8 n10 n11 n12 n13)
  have g7 := same ⟨7,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have g9 := same ⟨9,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have g15 := same ⟨15,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have g16 := same ⟨16,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have slot8 : (g.locals[8]'(vg ⟨8,by decide⟩))=⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vg ⟨8,by decide⟩)).symm.trans g8)
  have slot10 : (g.locals[10]'(vg ⟨10,by decide⟩))=⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 (len/2))))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vg ⟨10,by decide⟩)).symm.trans g10)
  have ghost2 : m2.user.payload.ghost=false := (tick_ghost options remaining span _).trans ((tick_ghost options remaining span _).trans ghost)
  have shallow2 : m2.user.payload.validation=.Shallow := (tick_shallow options remaining span _).trans ((tick_shallow options remaining span _).trans shallow)
  obtain ⟨r,rt,shape⟩ := RootMutPreparation.executes options limits remaining span source debug fuel fuelEq #[] g m2 gsz
    .uninit (.scalar (.fromBool false)) (.scalar (.fromScalarInt (.ofUInt64 count))) (.scalar (.fromScalarInt (.ofUInt64 (len/2))))
    (by rw [g7];exact live7) (by rw [g7];exact cache7) (by rw [slot8]) (by rw [g9];exact live9) (by rw [slot10])
    (by rw [g15];exact dead15) (by rw [g15];exact cache15) (by rw [g16];exact dead16) (by rw [g16];exact cache16)
    (gb.trans body) (gi.trans identity) (gfn.trans callee) gloc (by rw [gex];exact noClocks) tracker tracked mode ghost2 shallow2
  refine ⟨r,SuccessfulTrace.append gt rt,shape.body.trans gb,shape.identity.trans gi,shape.callee.trans gfn,shape.extra.trans gex,
    shape.destination.trans grp,shape.continuation.trans grc,shape.varargs.trans gva,shape.localsIdentity.trans gli,
    shape.trackedCaller.trans gtrack,shape.size,shape.location,?_,?_,?_,shape.slot13.trans g13,shape.slot15,shape.slot16,?_,shape.immediate ga⟩
  · exact shape.slot0.trans (gkeep 0 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact shape.slot1.trans (gkeep 1 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact shape.slot2.trans (gkeep 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · intro i lower
    exact (shape.kept i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (gkeep i (by omega) (by omega) (by omega) (by omega) (by omega))

#print axioms executes
end DuplicatePrefix.PositiveRootMutablePreparation
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootMutablePreparation.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual mutable preparation dependency {dependency}"
