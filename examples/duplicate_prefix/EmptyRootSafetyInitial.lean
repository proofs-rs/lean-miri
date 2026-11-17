import duplicate_prefix.EmptyRootSafetyInitialState
import duplicate_prefix.SuccessfulTrace
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.EmptyRootSafetyInitial
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (count : UInt64) (nonzero : count≠0)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (defaultMode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let result := {EmptyRootSafetyInitialState.guardFrame frame size count with location:=FrameLocation.mir ⟨2,0⟩}
    SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
      (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span machine)) ∧
    result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
    result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
    result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧
    result.locals[0]?=frame.locals[0]? ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
    (∀ id,id≠3→id≠4→id≠5→result.locals[id]?=frame.locals[id]?) ∧ CopyHelperCleanup.AllImmediate result := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let guard := EmptyRootSafetyInitialState.guardFrame frame size count
  obtain ⟨s1,s2,s3,s4,s5,h1,h2,h3,h4,h5,thirdEq,lastEq,lastLoc⟩ := RootBlock0.actual_first_block_statements
    options limits remaining span source debugOff #[] frame machine count body identity location callee size dead3 dead4 dead5
    uncached4 uncached5 (by rw [size];decide) live2 cached2 noClocks tracker tracked defaultMode ghost shallow fuel fuelEq
  have last : s5=Storage.withCurrent #[] guard machine := by simpa only [guard,EmptyRootSafetyInitialState.guardFrame] using lastEq
  rw [last] at h5
  obtain ⟨b,idn,fn,ex,rp,rc,va,li,sz,loc,s0,s1slot,s2slot,s3value,s4slot,s5slot,keep⟩ := EmptyRootSafetyInitialState.shape frame size count
  have gsz : guard.locals.size=25 := sz
  have v4 : (4:MIR.LocalId)<guard.locals.size := by rw [gsz];decide
  have slot4 : (guard.locals[4]'v4)=⟨.live (.immediate (.scalar (.fromBool (count==0)))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem v4).symm.trans s4slot)
  have switch := RootZeroCompleteSwitch.switch_exact options limits remaining span debugOff #[] guard machine count
    (b.trans body) (idn.trans identity) (fn.trans callee) loc sz v4 (by rw [slot4]) (by rw [slot4])
    (by rw [ex];exact noClocks) ghost unchecked noGc fixed
  let result := {guard with location:=FrameLocation.mir ⟨2,0⟩}
  have nz : (count==0)=false := by simp [nonzero]
  have switch' : ExecutionMachine.step config limits () (Storage.withCurrent #[] guard machine)=
      (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span machine),.ok true) := by
    simpa only [config,result,RootZeroCompleteState.tick,SourceControl.accounted,Storage.withCurrent,nz,Bool.false_eq_true,ite_false] using switch
  have trace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
      (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span machine)) :=
    .next h1 (.next h2 (.next h3 (.next h4 (.next h5 (.next switch' (.refl _))))))
  exact ⟨trace,b,idn,fn,ex,rp,rc,va,li,sz,s0,s1slot,s2slot,keep,EmptyRootSafetyInitialState.all frame size count all⟩

#print axioms executes
end DuplicatePrefix.EmptyRootSafetyInitial
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.EmptyRootSafetyInitial.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved nonzero-count actual first-block dependency {dependency}"
