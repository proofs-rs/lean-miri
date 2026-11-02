import duplicate_prefix.S03SeparateLivePacket
import duplicate_prefix.S03SeparateEmptyBody
import duplicate_prefix.S03FinalReturnBounds
import duplicate_prefix.S03EmptyPositiveDestination

namespace DuplicatePrefix.S03SeparatePositiveReturnBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification S04FinalReturnVariantsInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual positive-count separate-allocation empty body and original Return.
The argument may have zero capacity; its release facts come from the actual
zero constructors, with no positive byte observer invented for that allocation. -/
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (machine : Before)
    (place : MPlaceTy Provenance) (address count : UInt64)
    (p : S03SeparateLiveInstalledPacket.Packet options remaining span frame machine place address count)
    (nonnull : address ≠ 0) (countNonzero : count ≠ 0) (fuel dynamicFuel budget : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1) (dispatchEq : limits.callDispatch = budget+1)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (debugOff : options.place.debugAssertions = false)
    (validationEq : options.limits.validation = fuel+1) (source : PreparedContracts.SourceComparator) :
    let cfg := config options (remaining+1) span
    let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,limits,fun _ _ => True⟩
    ∃ done, SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] frame machine) done ∧
      ExecutionMachine.step cfg limits () done = (done,.ok false) ∧ done.stack.frames = #[] ∧
      CallSafety.NoErrorsBeforeReturn safety 1 (Storage.withCurrent #[] frame machine) ∧
      CallSafety.NoUBBeforeReturn safety 1 (Storage.withCurrent #[] frame machine) := by
  let offset := address-p.argumentBase
  have addressEq : p.argumentBase+offset=address := by
    change p.argumentBase+(address-p.argumentBase)=address
    rw [UInt64.add_comm,UInt64.sub_add_cancel]
  have fits : p.argumentEntry.allocation.extra.tagMapping.mapping.size ≤ 4294967295 := by
    have accounting := p.argumentRuntime.formed.allocator.accounting
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    have room := p.argumentRoom
    omega
  let sourceInput := EmptyForestSharedPool.factory p.argumentEntry.allocation.extra p.zeroTag p.tracker.global.nextPointerTag
    p.zeroIndex p.zero.node (Classical.choice p.argumentRuntime.formed.depth) p.zero.tagged p.zero.present
    (GeneralBorrowParentTagInvariant.fresh _ _ p.argumentRuntime) p.argumentRuntime.formed.allocator.pool p.argumentRuntime.formed.allocator.accounting fits
    (DuplicatePrefixBorrowContract.vacant_clean p.argumentRuntime)
  have unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩ := by
    intro id valid lower upper
    have bounded : id < 25 := by rw [←p.frameSize];exact valid
    have slot := p.slots ⟨id,bounded⟩
    simpa only [Fin.val_mk,show ¬(14=id ∨ 13=id ∨ 6=id ∨ 0=id) by omega,
      show ¬2=id by omega,show ¬1=id by omega,↓reduceIte] using slot
  obtain ⟨result,current,tree,currentTracker,treeEq,prefixTrace,fb,fi,ff,fe,frp,frc,fva,fli,fsz,resultLocation,result0,allResult,
      argumentLive,memoryEq,currentTracked,sameMode,trackerEq,currentGhost,currentShallow,currentRace,currentFixed,currentUnchecked,currentNoGc,
      addressesEq,typesEq,backendEq,extrasEq,currentActive,returnLive,currentRuntime,⟨currentPositive⟩⟩ :=
    S03SeparateEmptyBody.to_return options limits remaining span source cmp precise implicitWrites debugOff dynamicFuel fuel dynamicEq validationEq
      frame machine p.zeroTag p.tracker.global.nextPointerTag p.argumentId p.argumentEntry p.argumentBase offset count
      (by rw [addressEq];exact nonnull) countNonzero sourceInput p.frameSize
      (by simpa [addressEq,ActualReferenceContext.config,CanonicalConfigFacts.actual_access_runtime] using
        congrArg (fun row => row.value) (p.slots ⟨1,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (p.slots ⟨1,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (p.slots ⟨2,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (p.slots ⟨2,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (p.slots ⟨3,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (p.slots ⟨3,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (p.slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (p.slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (p.slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (p.slots ⟨5,by decide⟩)) unused
      p.sourceBody p.identity p.callee p.location p.noLocalClocks p.immediateLocals
      p.tracker p.enabled p.defaultMode rfl p.fresh p.argumentCached p.argumentLive p.ghost p.shallow p.unchecked p.noGc p.fixed
      p.metadata p.notConstructed p.argumentRuntime budget dispatchEq p.tagRoomNext p.argumentRoom p.race p.backend p.thread p.active p.topZero
      (by simpa using congrArg (fun row => row.value) (p.slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (p.slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (p.slots ⟨13,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (p.slots ⟨13,by decide⟩))
      p.destination.id p.destination.entry p.separate p.destination.live p.runtime (some p.child) (some p.selected) p.maximum p.destination.offset 1 p.positive
  have zeroFacts := S03SeparateEmptyBody.argument_zero p.argumentEntry.allocation.extra p.tracker.global p.argumentRuntime p.zeroTag sourceInput
    p.fresh p.argumentRoom p.zeroTag p.zeroIndex p.zero.node p.zero.tagged p.zero.present p.zero.sameTag p.zero.hidden p.quiet
  rw [←treeEq] at zeroFacts
  obtain ⟨zeroTagged,⟨zeroNode,zeroPresent,zeroSame,zeroHidden⟩,zeroQuiet⟩ := zeroFacts
  let destination := S03EmptyPositiveDestination.concrete p.destination p.destination.entry.allocation.extra returnLive addressesEq rfl p.destination.tagged
  have argument : ArgumentProtection current.memory p.borrowFrame destination.id destination.entry p.returnTag :=
    .separate p.argumentId {p.argumentEntry with allocation := p.argumentEntry.allocation.setExtra tree} p.zeroTag p.zeroIndex zeroNode
      p.separate argumentLive p.owned zeroTagged zeroPresent zeroHidden zeroQuiet
  obtain ⟨currentThread,currentThreadActive⟩ := currentActive
  have valid0 : (0 : MIR.LocalId) < result.locals.size := by rw [fsz];decide
  have slot0 : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans result0)
  have currentExtras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == p.destination.id) =
      some (p.destination.id,⟨none,#[]⟩) := by rw [extrasEq];exact p.extras
  obtain ⟨updated,returned,_,_,_⟩ := S03FinalReturnBounds.step options limits remaining span result current currentTracker p.borrowFrame
    currentTracked (by rw [fe];exact p.frameTracked) place destination p.returnTag p.child p.selected p.maximum p.returnNode argument
    p.returnTagged p.returnPresent p.returnSame p.returnEdge p.returnHidden p.hiddenFrame currentRuntime currentPositive
    p.distinct (fun _ _ => p.order) p.short p.activity currentThread currentThreadActive currentRace (backendEq.trans p.backend)
    currentGhost currentShallow #[] currentExtras (by simp) false fuel debugOff validationEq
    (fb.trans p.sourceBody) resultLocation valid0 (by rw [slot0]) (by rw [slot0]) (by rw [fe];exact p.noLocalClocks)
    (by rw [frp];exact p.returnPlace) (frc.trans p.continuation) allResult (fva.trans p.varargs) currentUnchecked currentNoGc currentFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result current
  let released := (p.destination.entry.allocation.extra.releaseProtector p.returnTag currentTracker.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] result accounted currentTracker p.borrowFrame argument.priorMemory destination.id destination.entry released
    (currentThread.topUserRelevantFrame.getD 0)
  let done := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] result current) = (done,.ok true) := returned
  have trace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.Trace.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] frame machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 done := by change (0 : Nat)<1;decide
  exact ⟨done,trace,rfl,rfl,SuccessfulTrace.no_errors safety 1 _ done entry trace exited,
    SuccessfulTrace.no_ub safety 1 _ done entry trace exited⟩

end
end DuplicatePrefix.S03SeparatePositiveReturnBounds
