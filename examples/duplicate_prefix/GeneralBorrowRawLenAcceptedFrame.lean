import duplicate_prefix.GenericLenAcceptedPrelude
import duplicate_prefix.LenCallResultFrame
namespace DuplicatePrefix.GeneralBorrowRawLenAcceptedFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (caller : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (countPositive : (0 : UInt64) < count) (within : count≤len/2) (size : caller.locals.size=25)
    (temp12 : Immediate Provenance)
    (live12 : (caller.locals[12]'(by omega)).value=.live (.immediate temp12))
    (live13 : (caller.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (caller.locals[13]'(by omega)).layout=none)
    (live0 : (caller.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (caller.locals[0]'(by omega)).layout=none)
    (live7 : (caller.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (cache7 : (caller.locals[7]'(by omega)).layout=none)
    (dead15 : (caller.locals[15]'(by omega)).value=.dead) (cache15 : (caller.locals[15]'(by omega)).layout=none)
    (dead16 : (caller.locals[16]'(by omega)).value=.dead) (cache16 : (caller.locals[16]'(by omega)).layout=none)
    (live8 : (caller.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (caller.locals[8]'(by omega)).layout=none)
    (live9 : (caller.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (caller.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (caller.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (caller.locals[10]'(by omega)).layout=none)
    (body : caller.body=RootBody.reflected.body.body) (identity : caller.bodyIdentity=RootBody.reflected.body.identity)
    (callee : caller.functionInstance=RootBody.reflected.functionInstance)
    (all : CopyHelperCleanup.AllImmediate caller) (noClocks : caller.extra.dataRace=none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
 :
    let frame := LenCallResultFrame.resultFrame caller (by omega) len
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      (SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (tick options remaining span (tick options remaining span machine))) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.trackCallerArg = frame.trackCallerArg ∧
      result.locals.size = 25 ∧ result.location = .mir ⟨6,7⟩ ∧
      result.locals[1]? = frame.locals[1]? ∧ result.locals[2]? = frame.locals[2]? ∧
      result.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧ CopyHelperCleanup.AllImmediate result) ∧ GenericLenAcceptedPrelude.FrameFacts frame result := by
  let valid11 : 11 < caller.locals.size := by omega
  let frame := LenCallResultFrame.resultFrame caller valid11 len
  have frameSize : frame.locals.size = 25 := (LenCallResultFrame.size caller valid11 len).trans size
  have original (i : Fin 25) : i.val < caller.locals.size := by rw [size];exact i.isLt
  have bounded (i : Fin 25) : i.val < frame.locals.size := by rw [frameSize];exact i.isLt
  have keep (i : Fin 25) (different : i.val ≠ 11) : frame.locals[i.val]'(bounded i) = caller.locals[i.val]'(original i) := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (bounded i)).symm.trans
      ((LenCallResultFrame.other caller valid11 len i.val different).trans (Array.getElem?_eq_getElem (original i))))
  have eleven : frame.locals[11]'(by omega) =
      (⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ : LocalState Provenance LocalLayout) := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans (LenCallResultFrame.value caller valid11 len))
  exact GenericLenAcceptedPrelude.executes_full options limits remaining span source debug fuel fuelEq frame machine len count
    countPositive within frameSize temp12
    ((congrArg LocalState.value (keep ⟨12,by decide⟩ (by decide))).trans live12)
    ((congrArg LocalState.value (keep ⟨13,by decide⟩ (by decide))).trans live13)
    ((congrArg LocalState.layout (keep ⟨13,by decide⟩ (by decide))).trans cache13)
    ((congrArg LocalState.value (keep ⟨0,by decide⟩ (by decide))).trans live0)
    ((congrArg LocalState.layout (keep ⟨0,by decide⟩ (by decide))).trans cache0)
    ((congrArg LocalState.value (keep ⟨7,by decide⟩ (by decide))).trans live7)
    ((congrArg LocalState.layout (keep ⟨7,by decide⟩ (by decide))).trans cache7)
    ((congrArg LocalState.value (keep ⟨15,by decide⟩ (by decide))).trans dead15)
    ((congrArg LocalState.layout (keep ⟨15,by decide⟩ (by decide))).trans cache15)
    ((congrArg LocalState.value (keep ⟨16,by decide⟩ (by decide))).trans dead16)
    ((congrArg LocalState.layout (keep ⟨16,by decide⟩ (by decide))).trans cache16)
    ((congrArg LocalState.value (keep ⟨8,by decide⟩ (by decide))).trans live8)
    ((congrArg LocalState.layout (keep ⟨8,by decide⟩ (by decide))).trans cache8)
    ((congrArg LocalState.value (keep ⟨9,by decide⟩ (by decide))).trans live9)
    ((congrArg LocalState.layout (keep ⟨9,by decide⟩ (by decide))).trans cache9)
    ((congrArg LocalState.value (keep ⟨10,by decide⟩ (by decide))).trans live10)
    ((congrArg LocalState.layout (keep ⟨10,by decide⟩ (by decide))).trans cache10)
    (congrArg LocalState.value eleven) (congrArg LocalState.layout eleven)
    body identity callee rfl (LenCallResultFrame.all_immediate caller valid11 len all) noClocks
    tracker tracked mode ghost shallow unchecked noGc fixed
/-- The two actual accounting steps in the accepted prelude preserve the exact
memory and borrow ledger. In particular all raw permission/runtime predicates
remain about the same stored trees and global protector table. -/
theorem machine_ledger (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let post := tick options remaining span (tick options remaining span machine)
    post.memory = machine.memory ∧ post.borrowTracker = machine.borrowTracker ∧
    post.dataRace = machine.dataRace ∧ post.threads = machine.threads ∧
    post.user.addresses = machine.user.addresses ∧
    post.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
    post.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
    post.user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
  dsimp only
  unfold tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.GeneralBorrowRawLenAcceptedFrame
