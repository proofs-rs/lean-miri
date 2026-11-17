import duplicate_prefix.EmptyRootSafetyInitial
import duplicate_prefix.RootLenPrefix

namespace DuplicatePrefix.GenericFunctionEntryPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure Shape (before after : CompilerFrameContext.ActualFrame) (count : UInt64) : Prop where
  body : after.body = before.body
  identity : after.bodyIdentity = before.bodyIdentity
  callee : after.functionInstance = before.functionInstance
  extra : after.extra = before.extra
  returnPlace : after.returnPlace = before.returnPlace
  continuation : after.returnContinuation = before.returnContinuation
  vaList : after.vaList = before.vaList
  localsIdentity : after.localsIdentity = before.localsIdentity
  size : after.locals.size = 25
  location : after.location = .mir ⟨2,11⟩
  slot0 : after.locals[0]? = before.locals[0]?
  slot1 : after.locals[1]? = before.locals[1]?
  slot2 : after.locals[2]? = before.locals[2]?
  slot7 : after.locals[7]? = some ⟨.live (.immediate .uninit),none⟩
  slot8 : after.locals[8]? = some ⟨.live (.immediate .uninit),none⟩
  slot9 : after.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slot10 : after.locals[10]? = some ⟨.live (.immediate .uninit),none⟩
  slot11 : after.locals[11]? = some ⟨.live (.immediate .uninit),none⟩
  slot12 : after.locals[12]? = some ⟨.live (.immediate .uninit),none⟩
  track : after.trackCallerArg = before.trackCallerArg
  immediate : CopyHelperCleanup.AllImmediate after
  keep : ∀ index,13 ≤ index → after.locals[index]? = before.locals[index]?

theorem executes_preserving
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions=false) (validityFuel : Nat)
    (validityEq : options.limits.validation=validityFuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (count : UInt64) (countNonzero : count≠0)
    (size : frame.locals.size=25)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (cache3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (cache4 : (frame.locals[4]'(by omega)).layout=none) (cache5 : (frame.locals[5]'(by omega)).layout=none)
    (unused : ∀id(valid:id<frame.locals.size),7≤id→id≤12→(frame.locals[id]'valid)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
 :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span machine)) ∧
      Shape frame result count := by
  let f := {EmptyRootSafetyInitialState.guardFrame frame size count with location:=FrameLocation.mir ⟨2,0⟩}
  let m := RootZeroCompleteState.tick options remaining span machine
  obtain ⟨initial,b,i,fn,ex,rp,rc,va,li,sz,s0,s1,s2,keep,fa⟩ := EmptyRootSafetyInitial.executes
    options limits remaining span source debug validityFuel validityEq frame machine count countNonzero body identity callee location
    size dead3 dead4 dead5 cache4 cache5 live2 cache2 noClocks all tracker tracked mode ghost shallow unchecked noGc fixed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,s4,s5,_⟩ := EmptyRootSafetyInitialState.shape frame size count
  have vf (n : Fin 25) : n.val<f.locals.size := by rw [sz];exact n.isLt
  have vo (n : Fin 25) : n.val<frame.locals.size := by rw [size];exact n.isLt
  have original2 : (f.locals[2]'(vf ⟨2,by decide⟩))=(frame.locals[2]'(vo ⟨2,by decide⟩)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨2,by decide⟩)).symm.trans (s2.trans (Array.getElem?_eq_getElem (vo ⟨2,by decide⟩))))
  have slot3 : (f.locals[3]'(vf ⟨3,by decide⟩))=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨3,by decide⟩)).symm.trans (EmptyRootSafetyInitialState.slot3 frame size count cache3))
  have slot4 : (f.locals[4]'(vf ⟨4,by decide⟩))=⟨.live (.immediate (.scalar (.fromBool (count==0)))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨4,by decide⟩)).symm.trans s4)
  have slot5 : (f.locals[5]'(vf ⟨5,by decide⟩))=⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨5,by decide⟩)).symm.trans s5)
  have fu : ∀id(valid:id<f.locals.size),7≤id→id≤12→(f.locals[id]'valid)=⟨.dead,none⟩ := by
    intro id valid low high
    have old : id<frame.locals.size := by omega
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid,keep id (by omega) (by omega) (by omega),Array.getElem?_eq_getElem old,unused id old low high]
  have trackF : f.trackCallerArg=frame.trackCallerArg := by
    simp only [f,EmptyRootSafetyInitialState.guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,
      RootCopyCount.postFrame,RootCopyCount.writeFrame,RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout]
  obtain ⟨result,⟨rest,rb,ri,rfn,re,rrp,rrc,rsz,rloc,r0,r1,r2,r7,r8,r9,r10,r11,r12,r13,rva,rli,ra⟩,rTrack,rKeep⟩ :=
    RootLenPrefix.executes_preserving options limits remaining span source debug validityFuel validityEq
      #[] f m count (.scalar (.fromBool (count==0))) (.scalar (.fromScalarInt (.ofUInt64 count))) sz
      (by rw [original2];exact live2) (by rw [original2];exact cache2)
      (by rw [slot3]) (by rw [slot3]) (by rw [slot4]) (by rw [slot5]) fu
      (b.trans body) (i.trans identity) (fn.trans callee) rfl (by rw [ex];exact noClocks) tracker tracked mode
      ((RootZeroCompleteState.tick_ghost options remaining span machine).trans ghost)
      ((RootZeroCompleteState.tick_shallow options remaining span machine).trans shallow) fa
  exact ⟨result,SuccessfulTrace.append initial rest,
    ⟨rb.trans b,ri.trans i,rfn.trans fn,re.trans ex,rrp.trans rp,rrc.trans rc,rva.trans va,rli.trans li,rsz,rloc,
      r0.trans s0,r1.trans s1,r2.trans s2,r7,r8,r9,r10,r11,r12,
      rTrack.trans trackF,ra,fun index high => (rKeep index high).trans (keep index (by omega) (by omega) (by omega))⟩⟩

end DuplicatePrefix.GenericFunctionEntryPrefix
