import duplicate_prefix.GeneralBorrowRawLenAcceptedFrame
import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame

namespace DuplicatePrefix.S02ConcreteSourceWildcardAcceptedGuardLocal
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The accepted guard takes the real post-len frame to MIR 6,7, irrespective
of the return pointer provenance. Future borrow/copy operations are not assumed. -/
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel+1)
    (site : CompilerFrameContext.ActualFrame)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (countPositive : (0 : UInt64) < count) (within : count ≤ len/2)
    (size : site.locals.size = 25)
    (validDest : 12 < site.locals.size)
    (value : Immediate Provenance)
    (site0 : site.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (site13 : site.locals[13]? = some ⟨.live (.immediate .uninit),none⟩)
    (site7 : site.locals[7]? = some ⟨.live (.immediate .uninit),none⟩)
    (site8 : site.locals[8]? = some ⟨.live (.immediate .uninit),none⟩)
    (site9 : site.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
      some RootCompilerFacts.usizeLayout⟩)
    (site10 : site.locals[10]? = some ⟨.live (.immediate .uninit),none⟩)
    (site15 : site.locals[15]? = some ⟨.dead,none⟩)
    (site16 : site.locals[16]? = some ⟨.dead,none⟩)
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
    let frame := LenCallResultFrame.resultFrame caller (by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using (show 11 < site.locals.size by omega)) len
    ∃ guard : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame post)
        (Storage.withCurrent #[] guard
          (RootZeroCompleteState.tick options remaining span
            (RootZeroCompleteState.tick options remaining span post))) ∧
      guard.location = .mir ⟨6,7⟩ ∧
      guard.body = frame.body ∧ guard.bodyIdentity = frame.bodyIdentity ∧
      guard.functionInstance = frame.functionInstance ∧ guard.extra = frame.extra ∧
      guard.returnPlace = frame.returnPlace ∧ guard.returnContinuation = frame.returnContinuation ∧
      guard.vaList = frame.vaList ∧ guard.localsIdentity = frame.localsIdentity ∧
      guard.trackCallerArg = frame.trackCallerArg ∧ guard.locals.size = 25 ∧
      guard.locals[1]? = frame.locals[1]? ∧ guard.locals[2]? = frame.locals[2]? ∧
      guard.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      guard.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate guard ∧
      GenericLenAcceptedPrelude.FrameFacts frame guard := by
  let caller := GeneralBorrowForestSharedPreLenFrame.after site validDest value
  have callerSize : caller.locals.size = 25 := by
    simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using size
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
      (present : site.locals[i.val]? = some row) :
      site.locals[i.val]'(original i) = row :=
    Option.some.inj ((Array.getElem?_eq_getElem (original i)).symm.trans present)
  obtain ⟨guard,⟨trace,gb,gi,gc,ge,gp,gcont,gva,gli,gtrack,gsz,gloc,g1,g2,g15,g16,gall⟩,facts⟩ :=
    GeneralBorrowRawLenAcceptedFrame.executes options limits remaining span source debug fuel fuelEq
      caller post len count countPositive within callerSize value callerLive
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
      ((congrArg LocalState.layout (keep ⟨7,by decide⟩ (by decide))).trans
        (congrArg LocalState.layout (slot ⟨7,by decide⟩ site7)))
      ((congrArg LocalState.value (keep ⟨15,by decide⟩ (by decide))).trans
        (congrArg LocalState.value (slot ⟨15,by decide⟩ site15)))
      ((congrArg LocalState.layout (keep ⟨15,by decide⟩ (by decide))).trans
        (congrArg LocalState.layout (slot ⟨15,by decide⟩ site15)))
      ((congrArg LocalState.value (keep ⟨16,by decide⟩ (by decide))).trans
        (congrArg LocalState.value (slot ⟨16,by decide⟩ site16)))
      ((congrArg LocalState.layout (keep ⟨16,by decide⟩ (by decide))).trans
        (congrArg LocalState.layout (slot ⟨16,by decide⟩ site16)))
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
  exact ⟨guard,trace,gloc,gb,gi,gc,ge,gp,gcont,gva,gli,gtrack,gsz,g1,g2,g15,g16,gall,facts⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardAcceptedGuardLocal

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedGuardLocal.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard accepted-guard dependency {dependency}"
