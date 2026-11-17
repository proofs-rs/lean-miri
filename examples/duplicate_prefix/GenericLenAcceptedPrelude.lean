import duplicate_prefix.PositiveRootAcceptedGuard
import duplicate_prefix.RootMutPreparation

/-! Actual post-len success guard and pure frame preparation, independent of
the allocation tree. Positive count and the accepted count <= len/2 branch are
initial numeric data. The endpoint precedes the mutable-reference statement. -/
namespace DuplicatePrefix.GenericLenAcceptedPrelude
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option autoImplicit false in
structure FrameFacts (before after : CompilerFrameContext.ActualFrame) : Prop where
  destination : after.returnPlace=before.returnPlace
  continuation : after.returnContinuation=before.returnContinuation
  varargs : after.vaList=before.vaList
  slot0 : after.locals[0]?=before.locals[0]?
  slot13 : after.locals[13]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  high : ∀ i,17≤i → after.locals[i]?=before.locals[i]?

theorem executes_full
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (countPositive : (0 : UInt64) < count) (within : count≤len/2) (size : frame.locals.size=25)
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
    (fixed : machine.threads.fixedScheduling=true)
 :
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
      result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧ CopyHelperCleanup.AllImmediate result) ∧ FrameFacts frame result := by
  obtain ⟨guard,guardTrace,gbody,gidentity,gcallee,gextra,greturn,gcontinuation,gva,gid,gtrack,gsize,glocation,g8,g10,g13,keep,gall⟩ :=
    PositiveRootAcceptedGuard.executes options limits remaining span source debug fuel fuelEq frame machine len count within size
      temp12 live12 live13 cache13 live0 cache0 live7 live8 cache8 live9 cache9 live10 cache10 live11 cache11 body identity callee
      location all noClocks tracker tracked mode ghost shallow unchecked noGc fixed
  have valid (i : Fin 25) : i.val < guard.locals.size := by rw [gsize];exact i.isLt
  have original (i : Fin 25) : i.val < frame.locals.size := by rw [size];exact i.isLt
  have unchanged (i : Fin 25) (n8 : i.val ≠ 8) (n10 : i.val ≠ 10) (n11 : i.val ≠ 11)
      (n12 : i.val ≠ 12) (n13 : i.val ≠ 13) :
      (guard.locals[i.val]'(valid i)) = (frame.locals[i.val]'(original i)) := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (valid i)).symm.trans
      ((keep i.val n8 n10 n11 n12 n13).trans (Array.getElem?_eq_getElem (original i))))
  have seven := unchanged ⟨7,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have nine := unchanged ⟨9,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have fifteen := unchanged ⟨15,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have sixteen := unchanged ⟨16,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
  have guard8 : (guard.locals[8]'(valid ⟨8,by decide⟩)).value = .live (.immediate (.scalar (.fromBool false))) := by
    simpa only [Array.getElem?_eq_getElem (valid ⟨8,by decide⟩),Option.some.injEq,Option.map_some] using congrArg (Option.map LocalState.value) g8
  have guard10 : (guard.locals[10]'(valid ⟨10,by decide⟩)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 (len/2))))) := by
    simpa only [Array.getElem?_eq_getElem (valid ⟨10,by decide⟩),Option.some.injEq,Option.map_some] using congrArg (Option.map LocalState.value) g10
  let finalMachine := tick options remaining span (tick options remaining span machine)
  have finalGhost : finalMachine.user.payload.ghost = false :=
    (tick_ghost options remaining span _).trans ((tick_ghost options remaining span machine).trans ghost)
  have finalValidation : finalMachine.user.payload.validation = .Shallow :=
    (tick_shallow options remaining span _).trans ((tick_shallow options remaining span machine).trans shallow)
  obtain ⟨result,preparation,shape⟩ := RootMutPreparation.executes options limits remaining span source debug fuel fuelEq
    #[] guard finalMachine gsize .uninit (.scalar (.fromBool false)) (.scalar (.fromScalarInt (.ofUInt64 count)))
    (.scalar (.fromScalarInt (.ofUInt64 (len/2))))
    ((congrArg LocalState.value seven).trans live7) ((congrArg LocalState.layout seven).trans cache7)
    guard8 ((congrArg LocalState.value nine).trans live9) guard10
    ((congrArg LocalState.value fifteen).trans dead15) ((congrArg LocalState.layout fifteen).trans cache15)
    ((congrArg LocalState.value sixteen).trans dead16) ((congrArg LocalState.layout sixteen).trans cache16)
    (gbody.trans body) (gidentity.trans identity) (gcallee.trans callee) glocation (gextra ▸ noClocks)
    tracker tracked mode finalGhost finalValidation
  refine ⟨result,?_,?_⟩
  · exact ⟨SuccessfulTrace.append guardTrace preparation,shape.body.trans gbody,shape.identity.trans gidentity,
    shape.callee.trans gcallee,shape.extra.trans gextra,shape.destination.trans greturn,shape.continuation.trans gcontinuation,
    shape.varargs.trans gva,shape.localsIdentity.trans gid,shape.trackedCaller.trans gtrack,shape.size,shape.location,
    shape.slot1.trans (keep 1 (by decide) (by decide) (by decide) (by decide) (by decide)),
    shape.slot2.trans (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide)),
    shape.slot15,shape.slot16,shape.immediate gall⟩
  · refine ⟨shape.destination.trans greturn,shape.continuation.trans gcontinuation,shape.varargs.trans gva,
      shape.slot0.trans (keep 0 (by decide) (by decide) (by decide) (by decide) (by decide)),shape.slot13.trans g13,?_⟩
    intro i high
    exact (shape.kept i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (keep i (by omega) (by omega) (by omega) (by omega) (by omega))


theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (countPositive : (0 : UInt64) < count) (within : count≤len/2) (size : frame.locals.size=25)
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
    (fixed : machine.threads.fixedScheduling=true)
 :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (tick options remaining span (tick options remaining span machine))) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.trackCallerArg = frame.trackCallerArg ∧
      result.locals.size = 25 ∧ result.location = .mir ⟨6,7⟩ ∧
      result.locals[1]? = frame.locals[1]? ∧ result.locals[2]? = frame.locals[2]? ∧
      result.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧ CopyHelperCleanup.AllImmediate result := by
  obtain ⟨result,properties,_⟩ := executes_full options limits remaining span source debug fuel fuelEq frame machine len count
    countPositive within size temp12 live12 live13 cache13 live0 cache0 live7 cache7 dead15 cache15 dead16 cache16 live8 cache8
    live9 cache9 live10 cache10 live11 cache11 body identity callee location all noClocks tracker tracked mode ghost shallow unchecked noGc fixed
  exact ⟨result,properties⟩

end DuplicatePrefix.GenericLenAcceptedPrelude
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GenericLenAcceptedPrelude.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved generic post-len accepted guard dependency {dependency}"
