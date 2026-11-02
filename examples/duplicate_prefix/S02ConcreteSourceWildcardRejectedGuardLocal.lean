import duplicate_prefix.GeneralBorrowRawLenRejectedFrame
import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame

namespace DuplicatePrefix.S02ConcreteSourceWildcardRejectedGuardLocal
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Actual rejected guard starting from the exact post-len caller. All premises
are current frame/control facts; no future operation result is assumed. -/
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel+1)
    (site : CompilerFrameContext.ActualFrame)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (rejected : count > len/2)
    (size : site.locals.size = 25)
    (validDest : 12 < site.locals.size)
    (value : Immediate Provenance)
    (valid11 : 11 < (GeneralBorrowForestSharedPreLenFrame.after site validDest value).locals.size)
    (site0 : site.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (site13 : site.locals[13]? = some ⟨.live (.immediate .uninit),none⟩)
    (site7 : site.locals[7]? = some ⟨.live (.immediate .uninit),none⟩)
    (site8 : site.locals[8]? = some ⟨.live (.immediate .uninit),none⟩)
    (site9 : site.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
      some RootCompilerFacts.usizeLayout⟩)
    (site10 : site.locals[10]? = some ⟨.live (.immediate .uninit),none⟩)
    (body : site.body = RootBody.reflected.body.body)
    (identity : site.bodyIdentity = RootBody.reflected.body.identity)
    (callee : site.functionInstance = RootBody.reflected.functionInstance)
    (noClocks : site.extra.dataRace = none)
    (allImmediate : CopyHelperCleanup.AllImmediate site)
    (held : MachineHooks.BorrowState) (enabled : post.borrowTracker = some held)
    (mode : held.retagMode = .Default)
    (ghost : post.user.payload.ghost = false)
    (shallow : post.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).gcInterval = 0)
    (fixed : post.threads.fixedScheduling = true) :
    let caller := GeneralBorrowForestSharedPreLenFrame.after site validDest value
    let frame := LenCallResultFrame.resultFrame caller valid11 len
    ∃ guard : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame post)
        (Storage.withCurrent #[] guard
          (RootZeroCompleteState.tick options remaining span
            (RootZeroCompleteState.tick options remaining span
              (RootZeroCompleteState.tick options remaining span post)))) ∧
      guard.body = frame.body ∧ guard.bodyIdentity = frame.bodyIdentity ∧
      guard.functionInstance = frame.functionInstance ∧ guard.extra = frame.extra ∧
      guard.returnPlace = frame.returnPlace ∧ guard.returnContinuation = frame.returnContinuation ∧
      guard.vaList = frame.vaList ∧ guard.localsIdentity = frame.localsIdentity ∧
      guard.locals.size = 25 ∧ guard.location = .mir ⟨10,0⟩ ∧
      guard.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate guard := by
  let caller := GeneralBorrowForestSharedPreLenFrame.after site validDest value
  have callerSize : caller.locals.size = 25 := by
    simpa only [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using size
  have original (i : Fin 25) : i.val < site.locals.size := by rw [size]; exact i.isLt
  have bounded (i : Fin 25) : i.val < caller.locals.size := by rw [callerSize]; exact i.isLt
  have keepOpt (i : Nat) (different : i ≠ 12) : caller.locals[i]? = site.locals[i]? := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,different,Ne.symm different]
  have keep (i : Fin 25) (different : i.val ≠ 12) :
      caller.locals[i.val]'(bounded i) = site.locals[i.val]'(original i) := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (bounded i)).symm.trans
      ((keepOpt i.val different).trans (Array.getElem?_eq_getElem (original i))))
  have callerLive : caller.locals[12].value = .live (.immediate value) := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have callerAll : CopyHelperCleanup.AllImmediate caller :=
    CopyHelperCleanup.all_immediate_written site 12 SharedReferenceMetadata.sharedLayout value
      validDest allImmediate
  have slot (i : Fin 25) {row : LocalState Provenance LocalLayout}
      (slot : site.locals[i.val]? = some row) :
      site.locals[i.val]'(original i) = row :=
    Option.some.inj ((Array.getElem?_eq_getElem (original i)).symm.trans slot)
  obtain ⟨guard,trace,fb,fi,fc,fe,frp,frc,fva,fli,fsz,loc,f0,all⟩ :=
    GeneralBorrowRawLenRejectedFrame.executes options limits remaining span source debug fuel fuelEq
      caller post len count rejected callerSize value callerLive
      ((congrArg LocalState.value (keep ⟨13,by decide⟩ (by decide))).trans
        (congrArg LocalState.value (slot ⟨13,by decide⟩ site13)))
      ((congrArg LocalState.layout (keep ⟨13,by decide⟩ (by decide))).trans
        (congrArg LocalState.layout (slot ⟨13,by decide⟩ site13)))
      ((congrArg LocalState.value (keep ⟨0,by decide⟩ (by decide))).trans
        (congrArg LocalState.value (slot ⟨0,by decide⟩ site0)))
      ((congrArg LocalState.layout (keep ⟨0,by decide⟩ (by decide))).trans
        (congrArg LocalState.layout (slot ⟨0,by decide⟩ site0)))
      ((congrArg LocalState.value (keep ⟨7,by decide⟩ (by decide))).trans
        (congrArg LocalState.value (slot ⟨7,by decide⟩ site7)))
      ((congrArg LocalState.value (keep ⟨8,by decide⟩ (by decide))).trans
        (congrArg LocalState.value (slot ⟨8,by decide⟩ site8)))
      ((congrArg LocalState.layout (keep ⟨8,by decide⟩ (by decide))).trans
        (congrArg LocalState.layout (slot ⟨8,by decide⟩ site8)))
      ((congrArg LocalState.value (keep ⟨9,by decide⟩ (by decide))).trans
        (congrArg LocalState.value (slot ⟨9,by decide⟩ site9)))
      ((congrArg LocalState.layout (keep ⟨9,by decide⟩ (by decide))).trans
        (congrArg LocalState.layout (slot ⟨9,by decide⟩ site9)))
      ((congrArg LocalState.value (keep ⟨10,by decide⟩ (by decide))).trans
        (congrArg LocalState.value (slot ⟨10,by decide⟩ site10)))
      ((congrArg LocalState.layout (keep ⟨10,by decide⟩ (by decide))).trans
        (congrArg LocalState.layout (slot ⟨10,by decide⟩ site10)))
      body identity callee callerAll noClocks held enabled mode ghost shallow unchecked noGc fixed
  exact ⟨guard,trace,fb,fi,fc,fe,frp,frc,fva,fli,fsz,loc,f0,all⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardRejectedGuardLocal

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardRejectedGuardLocal.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard rejected-guard dependency {dependency}"
