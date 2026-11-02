import duplicate_prefix.GenericLenAcceptedPrelude
import duplicate_prefix.GenericSharedLenAccepted
namespace DuplicatePrefix.GeneralBorrowExposedScopedAcceptedControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure FrameFacts (frame : CompilerFrameContext.ActualFrame) (len count : UInt64) : Prop where
  body : frame.body=RootBody.reflected.body.body
  identity : frame.bodyIdentity=RootBody.reflected.body.identity
  callee : frame.functionInstance=RootBody.reflected.functionInstance
  size : frame.locals.size=25
  location : frame.location=.mir ⟨3,0⟩
  all : CopyHelperCleanup.AllImmediate frame
  clocks : frame.extra.dataRace=none
  slot0 : frame.locals[0]?=some ⟨.live (.immediate .uninit),none⟩
  slot7 : frame.locals[7]?=some ⟨.live (.immediate .uninit),none⟩
  slot8 : frame.locals[8]?=some ⟨.live (.immediate .uninit),none⟩
  slot9 : frame.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slot10 : frame.locals[10]?=some ⟨.live (.immediate .uninit),none⟩
  slot11 : frame.locals[11]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩
  slot12 : ∃ value,frame.locals[12]?.map (·.value)=some (.live (.immediate value))
  slot13 : frame.locals[13]?=some ⟨.live (.immediate .uninit),none⟩
  slot15 : frame.locals[15]?=some ⟨.dead,none⟩
  slot16 : frame.locals[16]?=some ⟨.dead,none⟩

structure Result (before after : CompilerFrameContext.ActualFrame) : Prop where
  body : after.body=before.body
  identity : after.bodyIdentity=before.bodyIdentity
  callee : after.functionInstance=before.functionInstance
  extra : after.extra=before.extra
  returnPlace : after.returnPlace=before.returnPlace
  continuation : after.returnContinuation=before.returnContinuation
  varargs : after.vaList=before.vaList
  localsIdentity : after.localsIdentity=before.localsIdentity
  trackCallerArg : after.trackCallerArg=before.trackCallerArg
  size : after.locals.size=25
  location : after.location=.mir ⟨6,7⟩
  slot1 : after.locals[1]?=before.locals[1]?
  slot2 : after.locals[2]?=before.locals[2]?
  slot15 : after.locals[15]?=some ⟨.live (.immediate .uninit),none⟩
  slot16 : after.locals[16]?=some ⟨.live (.immediate .uninit),none⟩
  all : CopyHelperCleanup.AllImmediate after

def machine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span before)

theorem executes (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (countPositive : (0 : UInt64)<count) (within : count≤len/2) (facts : FrameFacts frame len count)
    (tracker : MachineHooks.BorrowState) (tracked : before.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (ghost : before.user.payload.ghost=false) (shallow : before.user.payload.validation=.Shallow)
    (unchecked : ((ActualReferenceContext.config options (remaining+1) span).terminators.getControl before.user).checkedArithmetic=false)
    (noGc : ((ActualReferenceContext.config options (remaining+1) span).terminators.getControl before.user).gcInterval=0)
    (fixed : before.threads.fixedScheduling=true) :
    ∃ result,
      SuccessfulTrace.Trace (ActualReferenceContext.config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame before) (Storage.withCurrent #[] result (machine options remaining span before)) ∧
      Result frame result ∧ GenericLenAcceptedPrelude.FrameFacts frame result := by
  have valid (i : Nat) (bound : i<25) : i<frame.locals.size := by rw [facts.size];exact bound
  have row (i : Nat) (bound : i<25) (expected : LocalState Provenance LocalLayout)
      (known : frame.locals[i]?=some expected) : frame.locals[i]'(valid i bound)=expected :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid i bound)).symm.trans known)
  obtain ⟨temp12,live12⟩:=facts.slot12
  have twelve : (frame.locals[12]'(valid 12 (by decide))).value=.live (.immediate temp12) := by
    have known:=live12
    rw [Array.getElem?_eq_getElem (valid 12 (by decide))] at known
    exact Option.some.inj known
  obtain ⟨result,properties,kept⟩:=GenericLenAcceptedPrelude.executes_full options limits remaining span source debug fuel fuelEq
    frame before len count countPositive within facts.size temp12 twelve
    (congrArg LocalState.value (row 13 (by decide) _ facts.slot13)) (congrArg LocalState.layout (row 13 (by decide) _ facts.slot13))
    (congrArg LocalState.value (row 0 (by decide) _ facts.slot0)) (congrArg LocalState.layout (row 0 (by decide) _ facts.slot0))
    (congrArg LocalState.value (row 7 (by decide) _ facts.slot7)) (congrArg LocalState.layout (row 7 (by decide) _ facts.slot7))
    (congrArg LocalState.value (row 15 (by decide) _ facts.slot15)) (congrArg LocalState.layout (row 15 (by decide) _ facts.slot15))
    (congrArg LocalState.value (row 16 (by decide) _ facts.slot16)) (congrArg LocalState.layout (row 16 (by decide) _ facts.slot16))
    (congrArg LocalState.value (row 8 (by decide) _ facts.slot8)) (congrArg LocalState.layout (row 8 (by decide) _ facts.slot8))
    (congrArg LocalState.value (row 9 (by decide) _ facts.slot9)) (congrArg LocalState.layout (row 9 (by decide) _ facts.slot9))
    (congrArg LocalState.value (row 10 (by decide) _ facts.slot10)) (congrArg LocalState.layout (row 10 (by decide) _ facts.slot10))
    (congrArg LocalState.value (row 11 (by decide) _ facts.slot11)) (congrArg LocalState.layout (row 11 (by decide) _ facts.slot11))
    facts.body facts.identity facts.callee facts.location facts.all facts.clocks tracker tracked mode ghost shallow unchecked noGc fixed
  rcases properties with ⟨trace,body,identity,callee,extra,returnPlace,continuation,varargs,localsIdentity,track,size,location,slot1,slot2,slot15,slot16,all⟩
  exact ⟨result,trace,⟨body,identity,callee,extra,returnPlace,continuation,varargs,localsIdentity,track,size,location,slot1,slot2,slot15,slot16,all⟩,kept⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedAcceptedControl
