import duplicate_prefix.S05ZeroCellActualCallCopyEntry
import duplicate_prefix.S05ZeroCellActualCallCopy
import duplicate_prefix.S05ZeroCellActualCallReturn
import duplicate_prefix.CopyRootExitData
import duplicate_prefix.DuplicatePrefixCompletedCallResult
import duplicate_prefix.S05ZeroCellActualCallRootFields

/-! Strong call/return result for the one fixed diagnostic packet. All actual
operation and trace facts are derived from source-level component theorems;
metadata comparison conditions remain explicit. This is no ordinary-input
coverage theorem. -/
namespace DuplicatePrefix.S05ZeroCellActualCallResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open S05ZeroCellTypedGeneratedPrefix (tag)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem row_from_fields (frame : CompilerFrameContext.ActualFrame) (index : Nat)
    (valid : index < frame.locals.size) (value : LocalValue Provenance) (layout : Option LocalLayout)
    (live : frame.locals[index].value = value) (cached : frame.locals[index].layout = layout) :
    frame.locals[index]? = some ⟨value,layout⟩ := by
  rw [Array.getElem?_eq_getElem valid]
  have eta : frame.locals[index] = ⟨frame.locals[index].value,frame.locals[index].layout⟩ := by
    cases frame.locals[index];rfl
  rw [eta,live,cached]

/-- The restored copy caller has precisely the local fields consumed by the
root cleanup. The unused legacy slot13 capability is unnecessary. -/
theorem copy_output_shape (span : PreparedContracts.FixedSpanQuery)
    (before caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (input : CopyRootEntry.Input options limits remaining span #[] caller machine
      (S05ZeroCellActualCallCopy.sourcePointer span) (S05ZeroCellActualCallCopy.destinationPointer span) 1)
    (body : caller.body = before.body) (identity : caller.bodyIdentity = before.bodyIdentity)
    (callee : caller.functionInstance = before.functionInstance) (extra : caller.extra = before.extra)
    (destination : caller.returnPlace = before.returnPlace)
    (continuation : caller.returnContinuation = before.returnContinuation)
    (varargs : caller.vaList = before.vaList) (localsIdentity : caller.localsIdentity = before.localsIdentity)
    (trackedCaller : caller.trackCallerArg = before.trackCallerArg) (size : caller.locals.size = 25)
    (zero : caller.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (pointer : caller.locals[15]? = some ⟨.live (.immediate (.scalar (S05ZeroCellActualCallCopy.sourcePointer span))),some CopyCompilerFacts.destPointerLayout⟩)
    (seventeen : caller.locals[17]? = some ⟨.live (.immediate .uninit),none⟩)
    (immediate : CopyHelperCleanup.AllImmediate caller) :
    CopyRootSuccessShape.Shape before (CopyRootOutput.caller caller input.valid)
      (S05ZeroCellActualCallCopy.sourcePointer span) (S05ZeroCellActualCallCopy.destinationPointer span) 1 := by
  obtain ⟨rb,ri,rc,re,rrc,rrp,rva,rtc,rli,rsz,rloc⟩ := CopyRootOutput.metadata caller input.valid
  refine ⟨rb.trans body,ri.trans identity,rc.trans callee,re.trans extra,rrp.trans destination,
    rrc.trans continuation,rva.trans varargs,rli.trans localsIdentity,rtc.trans trackedCaller,
    rsz.trans size,rloc,?_,?_,?_,?_,?_,?_,?_,CopyRootOutput.all_immediate caller input.valid immediate⟩
  · exact (CopyRootOutput.other caller input.valid 0 (by decide)).trans zero
  · exact (CopyRootOutput.other caller input.valid 15 (by decide)).trans pointer
  · exact (CopyRootOutput.other caller input.valid 17 (by decide)).trans seventeen
  · exact (Array.getElem?_eq_getElem (by rw [rsz,size];decide)).trans
      (congrArg some (CopyRootOutput.slot18 caller input.valid))
  · exact (CopyRootOutput.other caller input.valid 19 (by decide)).trans
      (row_from_fields caller 19 input.valid19 _ _ input.live19 input.cache19)
  · exact (CopyRootOutput.other caller input.valid 21 (by decide)).trans
      (row_from_fields caller 21 input.valid21 _ _ input.live21 input.cache21)
  · exact (CopyRootOutput.other caller input.valid 24 (by decide)).trans
      (row_from_fields caller 24 input.valid24 _ _ input.live24 input.cache24)

/-- The exact closed caller initializes, executes the copy, physically returns
true, and satisfies the original strong all-prefix result. No execution result
or additional caller restriction is a premise. -/
theorem result (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (compare : PreparedContracts.SourceComparator) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 2 1 place := by
  obtain ⟨updated,finished,init,initialTrace,depth,finishedDepth,finishedLocation,finishedValue,
    finalCaller,finalValid,helperFrame,helperMachine,finalMemory,helperTracker,helperLoan,helperThread,
    finishedEq,helperPresent,helperTracked,helperTrackerEq,helperLoanEq,finalMemoryEq,
    helperCached,helperTypes,helperExtras,helperBackend,helperGhost,helperShallow,helperRace,
    helperUnchecked,helperNoGc,helperFixed,helperActive,helperTop,
    original,prepared,valid16,valid15,originalShape,finalCallerEq,preparedBody,preparedIdentity,
    preparedCallee,preparedExtra,preparedTrack,preparedSize,preparedCount,preparedKeep,preparedAll,
    helperOther,helperAddresses,helperRuntimeExtras,preparedReturn,preparedContinuation,
    preparedVarargs,preparedLocalsIdentity,preparedZero⟩ :=
    S05ZeroCellActualCallAsMutReturn.initializes_through_as_mut_with_frame span cmp compare
  have root := S05ZeroCellActualCallRootFields.of_shape span updated original originalShape
  let frame : CompilerFrameContext.ActualFrame :=
    {AsMutPtrReturn.writeFrame finalCaller 15 (.scalar (S05ZeroCellActualCallAsMutReturn.rawResult span)) finalValid with location := .mir ⟨7,0⟩}
  let accounted := AsMutPtrReturn.accountedMachine options remaining span helperMachine
  let released := ActualPopPlan.released accounted finalMemory helperTracker helperLoan
  let machine := AsMutPtrReturn.poppedMachine #[] finalCaller helperFrame released (helperThread.topUserRelevantFrame.getD 1)
  have initialTrace' : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (S05ZeroCellActualCallInit.installed span updated) (Storage.withCurrent #[] frame machine) := by
    simpa only [finishedEq,frame,machine,accounted,released] using initialTrace
  have frameExtra : frame.extra = original.extra := by
    simp only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
    exact preparedExtra
  have frameSize : frame.locals.size = 25 := by
    simp only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set]
    exact preparedSize
  have frameBody : frame.body = RootBody.reflected.body.body := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using preparedBody
  have frameIdentity : frame.bodyIdentity = RootBody.reflected.body.identity := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using preparedIdentity
  have frameCallee : frame.functionInstance = RootBody.reflected.functionInstance := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using preparedCallee
  have frameTrack : frame.trackCallerArg = none := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using preparedTrack.trans root.trackNone
  have frameReturn : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using
      (congrArg (fun place => place.toRuntimePlace) preparedReturn).trans root.destination
  have frameContinuation : frame.returnContinuation = .stop true := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using preparedContinuation.trans root.continuation
  have frameVarargs : frame.vaList = #[] := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using preparedVarargs.trans root.varargs
  have frameZero : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,
      show ¬(15=0) by decide,show ¬(16=0) by decide,ite_false] using preparedZero.trans root.zero
  have frameCount : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))),some RootCompilerFacts.usizeLayout⟩ := by
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,
      show ¬(15=2) by decide,show ¬(16=2) by decide,ite_false] using preparedCount.trans root.count
  have frameUnused : ∀ index,17 ≤ index → index ≤ 24 → frame.locals[index]? = some ⟨.dead,none⟩ := by
    intro index lower upper
    simpa only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,
      show ¬(15=index) by omega,show ¬(16=index) by omega,ite_false] using
      (preparedKeep index lower).trans (root.unused index lower upper)
  let temp16 := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId S05ZeroCellActualCallAsMutReturn.PureTree.returnedTracker.global.nextPointerTag)
      (Size.ofBytes 4096)) 2 (RootReferenceInfo.layout false)).imm
  have frame16 : frame.locals[16]?.map (·.value) = some (.live (.immediate temp16)) := by
    simp only [frame,finalCallerEq,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,
      show ¬(15=16) by decide,ite_false,ite_true,Option.map_some,temp16]
  have frame15 : frame.locals[15]? = some ⟨.live (.immediate (.scalar (S05ZeroCellActualCallAsMutReturn.rawResult span))),some CopyCompilerFacts.destPointerLayout⟩ := by
    simpa only [finishedEq,frame,machine,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,Option.bind_some] using finishedValue
  have frameAll : CopyHelperCleanup.AllImmediate frame := by
    let written := CopyHelperSteps.advance (ActualLocalCopy.written prepared 16 (RootReferenceInfo.layout false) valid16 temp16) ⟨6,7⟩
    have allWritten : CopyHelperCleanup.AllImmediate written :=
      CopyHelperCleanup.all_immediate_written prepared 16 (RootReferenceInfo.layout false) temp16 valid16 preparedAll
    have allCached : CopyHelperCleanup.AllImmediate (AsMutUncachedCall.cachedCaller written valid15) :=
      CopyHelperCleanup.all_immediate_cache written 15 CopyCompilerFacts.destPointerLayout valid15 allWritten
    have cachedEq : finalCaller = AsMutUncachedCall.cachedCaller written valid15 := by
      simpa only [written,temp16] using finalCallerEq
    have cachedValid : 15 < (AsMutUncachedCall.cachedCaller written valid15).locals.size := by
      rw [←cachedEq];exact finalValid
    have after := CopyHelperCleanup.all_immediate_set (AsMutUncachedCall.cachedCaller written valid15) 15
      ⟨.live (.immediate (.scalar (S05ZeroCellActualCallAsMutReturn.rawResult span))),
        ((AsMutUncachedCall.cachedCaller written valid15).locals[15]'cachedValid).layout⟩ cachedValid allCached (by intro memory;simp)
    simpa only [CopyHelperCleanup.AllImmediate,frame,cachedEq,AsMutPtrReturn.writeFrame,written,temp16] using after
  have account := RootZeroInvocationState.tick_fields options remaining span helperMachine
  change accounted.memory = helperMachine.memory ∧ accounted.borrowTracker = helperMachine.borrowTracker ∧
    accounted.dataRace = helperMachine.dataRace ∧ accounted.threads = helperMachine.threads ∧
    accounted.user.addresses = helperMachine.user.addresses ∧
    accounted.user.payload.payload.user.backend = helperMachine.user.payload.payload.user.backend ∧
    accounted.user.payload.payload.user.runtime.extras = helperMachine.user.payload.payload.user.runtime.extras at account
  have machineMemory : machine.memory = finalMemory := by
    unfold machine AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have machineTracked : machine.borrowTracker = some S05ZeroCellActualCallRepaired.copyTracker := by
    unfold machine AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> simp only [released,ActualPopPlan.released,helperTrackerEq,helperLoanEq,
      S05ZeroCellActualCallRepaired.copyTracker,S05ZeroCellActualCallRepaired.PureTree.tag] <;> rfl
  have machineUser : machine.user = accounted.user := AsMutPtrReturn.popped_user _ _ _ _ _
  have machineRace : machine.dataRace = none := by
    unfold machine AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact account.2.2.1.trans helperRace
  have machineBackend : machine.user.payload.payload.user.backend = .none := by
    rw [machineUser,account.2.2.2.2.2.1];exact helperBackend
  have machineGhost : machine.user.payload.ghost = false := by
    rw [machineUser]
    exact (AsMutPtrReturn.accounted_ghost options remaining span helperMachine).trans helperGhost
  have machineShallow : machine.user.payload.validation = .Shallow := by
    rw [machineUser]
    exact (AsMutPtrReturn.accounted_validation options remaining span helperMachine).trans helperShallow
  have machineCached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ := by
    rw [machineUser,account.2.2.2.2.1];exact helperCached
  have machinePresent : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,S05ZeroCellActualCallRepaired.copyEntry) := by
    rw [machineMemory,finalMemoryEq]
    exact StackPopRelease.lookup_commit_same _ _ _ _
  have machineExtras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == sourceId) = some (sourceId,⟨none,#[]⟩) := by
    rw [machineUser,account.2.2.2.2.2.2];exact helperExtras
  have machineControl : (config options (remaining+1) span).terminators.getControl machine.user =
      (config options (remaining+1) span).terminators.getControl accounted.user := by rw [machineUser]
  have machineUnchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false := by
    rw [machineControl];exact (RootZeroCompleteState.tick_flags options remaining span helperMachine).1.trans helperUnchecked
  have machineNoGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    rw [machineControl];exact (RootZeroCompleteState.tick_flags options remaining span helperMachine).2.trans helperNoGc
  have machineFixed : machine.threads.fixedScheduling = true := by
    unfold machine AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> simpa only [GenericPopFrame.afterRelevance,released,ActualPopPlan.released,account.2.2.2.1] using helperFixed
  obtain ⟨rootThread,rootActive,rootTop⟩ := S05ZeroCellActualCallCopyEntry.popped_root_active finalCaller helperFrame released helperThread
    (by change accounted.threads.activeThread? = some helperThread;rw [account.2.2.2.1];exact helperActive) helperTop
  obtain ⟨caller,input,addTrace,callerBody,callerIdentity,callerCallee,callerExtra,callerReturn,callerContinuation,
    callerVarargs,callerLocalsIdentity,callerTrack,callerSize,caller17,callerKeep,callerAll⟩ :=
    S05ZeroCellActualCallCopyEntry.from_block_seven span cmp compare frame machine frameSize frame15 temp16 frame16 frameCount
      frameUnused frameBody frameIdentity frameCallee rfl (frameExtra ▸ root.noClocks) machineTracked machineGhost machineShallow
      frameAll frameTrack (frameExtra ▸ root.relevance) rootThread rootActive rootTop machineBackend machineRace
      machineUnchecked machineNoGc machineFixed machineCached machinePresent

  let added := AddOutput.machine options remaining span machine
  have addedFields := AddOutput.preserved options remaining span machine
  have inputTracker : input.tracker = S05ZeroCellActualCallRepaired.copyTracker :=
    Option.some.inj (input.tracked.symm.trans (addedFields.2.1.trans machineTracked))
  obtain ⟨copied,finalMachine,copyTrace,copiedLookup,copiedSize,copiedLen,copiedTree,copiedMemory,
    copiedTracked,copiedRace,copiedGhost,copiedShallow,copiedUnchecked,copiedNoGc,copiedFixed,
    copiedAddresses,copiedTypes,copiedBackend,copiedExtras,finalThread,finalActive⟩ :=
    S05ZeroCellActualCallCopy.complete span #[] caller added input inputTracker
      (by rw [addedFields.1];exact machinePresent)
      (by rw [addedFields.2.2.2.2.2.2.2.2.1];exact machineExtras)
      (by rw [addedFields.2.2.2.2.1];exact machineCached)
  have restoredShape := copy_output_shape span frame caller added input callerBody callerIdentity callerCallee callerExtra
    callerReturn callerContinuation callerVarargs callerLocalsIdentity callerTrack callerSize
    ((callerKeep 0 (Or.inl (by decide))).trans frameZero)
    ((callerKeep 15 (Or.inl (by decide))).trans frame15) caller17 callerAll
  have helperSlot := helperOther destinationId ⟨destinationEntry.kind,updated⟩ (Ne.symm distinct_ids)
    (S05ZeroCellActualCallCopyEntry.shared_destination span updated)
  have machineSlot : machine.memory.live.find? (fun row => row.1 == destinationId) =
      some (destinationId,⟨destinationEntry.kind,updated⟩) := by
    rw [machineMemory,finalMemoryEq]
    exact StackPopRelease.lookup_commit_other _ sourceId destinationId _ _ _ (Ne.symm distinct_ids) helperSlot
  have copiedSlot : finalMachine.memory.live.find? (fun row => row.1 == destinationId) =
      some (destinationId,⟨destinationEntry.kind,updated⟩) := by
    rw [copiedMemory,CopyRootExitData.memory_after_eq_commit]
    exact StackPopRelease.lookup_commit_other _ sourceId destinationId _ _ _ (Ne.symm distinct_ids)
      (by rw [addedFields.1];exact machineSlot)
  have sharedAddresses : (S05ZeroCellActualCallSharedStmt.postMachine span updated).user.addresses = before.user.addresses := by
    change (S05ZeroCellActualCallSharedStmt.current span updated).user.addresses = before.user.addresses
    unfold S05ZeroCellActualCallSharedStmt.current
    rw [(RootZeroInvocationState.tick_fields options remaining span (S05ZeroCellActualCallInit.installed span updated).machine).2.2.2.2.1]
    rfl
  have sharedExtras : (S05ZeroCellActualCallSharedStmt.postMachine span updated).user.payload.payload.user.runtime.extras =
      before.user.payload.payload.user.runtime.extras := by
    change (S05ZeroCellActualCallSharedStmt.current span updated).user.payload.payload.user.runtime.extras = _
    unfold S05ZeroCellActualCallSharedStmt.current
    rw [(RootZeroInvocationState.tick_fields options remaining span (S05ZeroCellActualCallInit.installed span updated).machine).2.2.2.2.2.2]
    rfl
  have finalAddresses : finalMachine.user.addresses = before.user.addresses :=
    copiedAddresses.trans (addedFields.2.2.2.2.1.trans
      ((congrArg (fun user => user.addresses) machineUser).trans
        (account.2.2.2.2.1.trans (helperAddresses.trans sharedAddresses))))
  have finalExtras : finalMachine.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras :=
    copiedExtras.trans (addedFields.2.2.2.2.2.2.2.2.1.trans
      ((congrArg (fun user => user.payload.payload.user.runtime.extras) machineUser).trans
        (account.2.2.2.2.2.2.trans (helperRuntimeExtras.trans sharedExtras))))
  obtain ⟨slotTree,slotSize,slotLen,slotMask,slotProv,slotSnapshot,slotMutable⟩ :=
    S05ZeroCellActualCallInit.slot_of_initialization span cmp updated init
  obtain ⟨contexts⟩ := S05ZeroCellActualCallReturn.contexts span
  let returnInput : S05ZeroCellActualCallReturn.Input := {
    options := options, limits := limits, remaining := remaining, span := span,
    source := compare, fuel := remaining, debugOff := rfl, validationFuel := rfl,
    context := contexts.context,validationContext := contexts.validationContext,
    accessEq := contexts.accessEq,validationWidth := contexts.validationWidth,
    validationRuntimeSize := contexts.validationRuntimeSize,sameRuntime := contexts.sameRuntime,
    width := contexts.width,runtimeWidth := contexts.runtimeWidth,runtimeSize := contexts.runtimeSize,
    outerAccessEq := contexts.outerAccessEq,
    before := frame,after := CopyRootOutput.caller caller input.valid,
    pointer := S05ZeroCellActualCallCopy.sourcePointer span,
    destinationValue := S05ZeroCellActualCallCopy.destinationPointer span,count := 1,
    shape := restoredShape,body := frameBody,identity := frameIdentity,callee := frameCallee,
    noLocalClocks := frameExtra ▸ root.noClocks,continuation := frameContinuation,varargs := frameVarargs,
    machine := finalMachine,tracked := copiedTracked,noClocks := copiedRace,
    noBackend := copiedBackend.trans (addedFields.2.2.2.2.2.2.2.1.trans machineBackend),
    ghost := copiedGhost,shallow := copiedShallow,unchecked := copiedUnchecked,noGc := copiedNoGc,fixed := copiedFixed,
    thread := finalThread,active := finalActive,buffer := ⟨S05ZeroCellActualCallRepaired.copyEntry.kind,copied⟩,
    bufferPresent := copiedLookup,bufferTree := copiedTree,
    slot := ⟨destinationEntry.kind,updated⟩,slotPresent := copiedSlot,slotTree := slotTree,
    frameTracked := frameExtra ▸ root.tracked,
    slotSize := slotSize,slotStorage := slotLen,slotMask := slotMask,slotProvenance := slotProv,slotMutable := slotMutable,
    place := place,layout := rfl,slotBase := 8192,slotPointer := rfl,aligned := rfl,fits := by decide,
    cached := by rw [finalAddresses];exact destination_cached,
    extras := by change finalMachine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [finalExtras];exact destination_extras,
    destination := frameReturn }
  obtain ⟨returned,returnTrace,terminal,_,properties⟩ := S05ZeroCellActualCallReturn.complete returnInput
  let finalState := CanonicalCopy.replaceAllocation (S05ZeroCellActualCallReturn.popped returnInput)
    destinationId returnInput.slot.kind returned
  have fullTrace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (S05ZeroCellActualCallInit.installed span updated) finalState :=
    SuccessfulTrace.append initialTrace' (SuccessfulTrace.append addTrace (SuccessfulTrace.append copyTrace returnTrace))
  apply DuplicatePrefixCompletedCallResult.of_trace options limits remaining span before argument 2 1 place
    (S05ZeroCellActualCallInit.installed span updated) finalState
  · rw [←S05ZeroCellActualCallParameters.initializationResult_exact];exact init
  · simp [CallSafety.IsCallEntry,CallSafety.frameDepth,depth]
  · exact fullTrace
  · exact terminal

end
end DuplicatePrefix.S05ZeroCellActualCallResult
