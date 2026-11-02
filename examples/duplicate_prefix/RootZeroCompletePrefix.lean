import duplicate_prefix.RootZeroCompleteState
import duplicate_prefix.SuccessfulTrace
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RootZeroCompletePrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootZeroCompleteState

theorem reaches_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout=none)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (defaultMode : tracker.retagMode=.Default)
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
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧
      result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let guard := guardFrame frame size
  obtain ⟨s1,s2,s3,s4,s5,h1,h2,h3,h4,h5,thirdEq,lastEq,lastLoc⟩ := RootBlock0.actual_first_block_statements
    options limits remaining span source debugOff #[] frame machine 0 body identity location callee size dead3 dead4 dead5
    uncached4 uncached5 (by rw [size];decide) live2 cached2 noClocks tracker tracked defaultMode ghost shallow fuel fuelEq
  have last : s5 = Storage.withCurrent #[] guard machine := by simpa only [guard,guardFrame] using lastEq
  rw [last] at h5
  obtain ⟨b,idn,fn,ex,rp,rc,va,li,sz,loc,s0,s3value,s4slot,s5slot⟩ := guard_shape frame size
  have gsz : guard.locals.size=25 := sz
  have v0 : (0:MIR.LocalId)<guard.locals.size := by rw [gsz];decide
  have v3 : (3:MIR.LocalId)<guard.locals.size := by rw [gsz];decide
  have v4 : (4:MIR.LocalId)<guard.locals.size := by rw [gsz];decide
  have v5 : (5:MIR.LocalId)<guard.locals.size := by rw [gsz];decide
  have slot4 : (guard.locals[4]'v4) = ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem v4).symm.trans s4slot)
  have slot5 : (guard.locals[5]'v5) = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem v5).symm.trans s5slot)
  have initialValid0 : (0:MIR.LocalId)<frame.locals.size := by rw [size];decide
  have zeroSlot : (guard.locals[0]'v0) = (frame.locals[0]'initialValid0) :=
    Option.some.inj ((Array.getElem?_eq_getElem v0).symm.trans (s0.trans (Array.getElem?_eq_getElem (by rw [size];decide))))
  have live3 : (guard.locals[3]'v3).value = .live (.immediate .uninit) := by
    change guard.locals[3]?.map (·.value) = _ at s3value
    rw [Array.getElem?_eq_getElem v3] at s3value
    exact Option.some.inj s3value
  have switch := RootZeroCompleteSwitch.switch_exact options limits remaining span debugOff #[] guard machine 0
    (b.trans body) (idn.trans identity) (fn.trans callee) loc sz v4 (by rw [slot4];rfl) (by rw [slot4])
    (by rw [ex];exact noClocks) ghost unchecked noGc fixed
  let branch := {guard with location := FrameLocation.mir ⟨1,0⟩}
  let next := tick options remaining span machine
  have switch' : ExecutionMachine.step config limits () (Storage.withCurrent #[] guard machine) =
      (Storage.withCurrent #[] branch next,.ok true) := by simpa only [branch,next,tick,config,SourceControl.accounted,Storage.withCurrent,beq_self_eq_true,↓reduceIte] using switch
  have nextGhost : next.user.payload.ghost=false := (tick_ghost options remaining span machine).trans ghost
  have nextShallow : next.user.payload.validation=.Shallow := (tick_shallow options remaining span machine).trans shallow
  have nextUnchecked := (tick_flags options remaining span machine).1.trans unchecked
  have nextNoGc := (tick_flags options remaining span machine).2.trans noGc
  obtain ⟨f1,f2,f3,f4,q1,q2,q3,q4,q5,all4,fb,fi,ff,fe,frp,frc,fva,fli,fsz,f0,f1slot,f2slot,f3slot,f4slot,f5slot⟩ :=
    RootZeroCompleteBranch.branch_exact options limits remaining span source debugOff fuel fuelEq #[] branch next
      (guard_all frame size all) sz (by rw [zeroSlot];exact live0) (by rw [zeroSlot];exact uncached0)
      live3 (by rw [slot4]) (by rw [slot5]) (b.trans body) (idn.trans identity) (fn.trans callee) rfl
      (by rw [ex];exact noClocks) tracker tracked defaultMode nextGhost nextShallow nextUnchecked nextNoGc fixed
  let result := {f4 with location := FrameLocation.mir ⟨10,0⟩}
  have trace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
      (Storage.withCurrent #[] result (tick options remaining span next)) :=
    .next h1 (.next h2 (.next h3 (.next h4 (.next h5 (.next switch' (.next q1 (.next q2 (.next q3 (.next q4 (.next q5 (.refl _)))))))))))
  refine ⟨result,trace,fb.trans b,fi.trans idn,ff.trans fn,fe.trans ex,frp.trans rp,frc.trans rc,fva.trans va,fli.trans li,fsz,rfl,f0,all4⟩

#print axioms reaches_return
end DuplicatePrefix.RootZeroCompletePrefix
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootZeroCompletePrefix.reaches_return) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved full root zero prefix dependency {dependency}"
