import duplicate_prefix.S05DiagnosticAsMutBody
import duplicate_prefix.S05DiagnosticAsMutReturn
import duplicate_prefix.AsMutPushPreserves
namespace DuplicatePrefix.S05DiagnosticAsMutComplete
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess AsMutUncachedCall
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual diagnostic as_mut_ptr call, helper body, release and Return on one computed machine. -/
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (treeEq : entry.allocation.extra = S05DiagnosticAsMutRead.tree)
    (parentEq : parentTag = S05DiagnosticFnEntryRead.tag 12)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 13)
    (protectedEq : tracker.global.protectedTags = S05DiagnosticSharedRead.protections)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = AsMutPtrReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    let cfg := config options remaining span
    let before := Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine
    let destination := (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := S05DiagnosticAsMutInstall.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    ∃ (done : CompilerFrameContext.ActualFrame), ∃ (helperThread : ThreadRecord),
      resultMachine.threads.activeThread? = some helperThread ∧
      let sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
      let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
      let owned := ({} : FrameState).addProtector id (S05DiagnosticFnEntryRead.tag 13)
      let releasedMemory := StackPopRelease.commitTree resultMachine.memory id sourceEntry S05DiagnosticAsMutRelease.released
      let post := GenericAsMutReturnState.machine options remaining span #[] (cachedCaller caller destValid) done resultMachine releasedMemory held owned helperThread
      let pointer := Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 13)) (Size.ofBytes (base+offset)))
      let root := {AsMutPtrReturn.writeFrame (cachedCaller caller destValid) 15 (.scalar pointer) (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using destValid) with location := .mir ⟨7,0⟩}
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] caller beforeMachine) (Storage.withCurrent #[] root post) ∧
      root.locals[15]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      post.memory.live.find? (fun row => row.1 == id) = some (id,{sourceEntry with allocation := sourceEntry.allocation.setExtra S05DiagnosticAsMutRelease.released}) ∧
      ∃ finalTracker, post.borrowTracker = some finalTracker ∧ finalTracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 14 ∧
        finalTracker.global.protectedTags = S05DiagnosticSharedRead.protections := by
  dsimp only
  let cf := cachedCaller caller destValid
  let before := Storage.withCurrent #[] cf machine
  let destination := (LocalPlaces.localRuntimePlace 0 cf 15 CopyCompilerFacts.destPointerLayout).stackView
  let pushed := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := S05DiagnosticAsMutInstall.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine pushed tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory pushed.memory id entry finalTree}
  let sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let owned := ({} : FrameState).addProtector id (S05DiagnosticFnEntryRead.tag 13)
  obtain ⟨done,trace,doneBody,_doneIdentity,_doneCallee,size,location,ret,_source,_d2,_d3,_d4,_extra,owner,clocks,dest,cont,va,immediate⟩ :=
    S05DiagnosticAsMutBody.before_return options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag treeEq parentEq offsetEq lenEq positive nonzero signedFits bounds caller machine tracker enabled nextEq protectedEq
      defaultMode fresh body identity callee located source valid16 value16 cached16 destValid .uninit destLive uncached callerClocks ghost shallow
      cachedAddress present race backend metadata notConstructed thread index current active top topPresent beforeMachine machineEq unchecked noGc fixed
  have fields := AsMutPushPreserves.preserves options.userRelevantCrates before destination current
  have activePushed := AsMutPushPreserves.active_after_push (CallEntryFacts.freshRoot machine).1 thread active 1
    (AsMutFrame.rawFrame options.userRelevantCrates (CallEntryFacts.freshRoot machine).1 destination (CallEntryFacts.freshRoot machine).2).extra.userRelevance
    current.extra.userRelevance
  let helperThread := if (AsMutFrame.rawFrame options.userRelevantCrates (CallEntryFacts.freshRoot machine).1 destination (CallEntryFacts.freshRoot machine).2).extra.userRelevance >= current.extra.userRelevance
    then {thread with topUserRelevantFrame := some 1} else thread
  have helperActive : resultMachine.threads.activeThread? = some helperThread := activePushed
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [size];decide
  have retCell := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans ret)
  have valid15 : (15 : MIR.LocalId) < cf.locals.size := by simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout] using destValid
  have found : resultMachine.memory.live.find? (fun row => row.1 == id) = some (id,sourceEntry) :=
    StackPopRelease.lookup_commit_same pushed.memory id entry finalTree
  have finalTreeEq : sourceEntry.allocation.extra = (S05DiagnosticAsMutRead.afterRead.newChild Size.ZERO
      (.concrete (S05DiagnosticFnEntryRead.tag 12)) (S05DiagnosticFnEntryRead.tag 13)
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    change finalTree = _
    simp only [finalTree,S05DiagnosticAsMutInstall.finalTree,TypedBorrowSteps.registeredGlobal,treeEq,parentEq,offsetEq,lenEq,nextEq,protectedEq]
    change ((S05DiagnosticAsMutRead.tree.performBorrowAccessRange (.concrete (S05DiagnosticFnEntryRead.tag 12)) Size.ZERO (Size.ofBytes 2) .Read S05DiagnosticAsMutRead.protections .VisitChildrenOfAccessed).tree.newChild _ _ _ _ _ _).tree = _
    rw [S05DiagnosticAsMutRead.read.2]
    rfl
  have heldProtected : held.global.protectedTags = S05DiagnosticAsMutRelease.protections := by
    change tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector = _
    rw [protectedEq,nextEq];rfl
  have originalSettings :
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 ∧
      machine.threads.fixedScheduling = true := by
    rw [machineEq]
    unfold AsMutPtrReturn.accountedMachine SourceControl.accounted
    simp only [CanonicalConfigFacts.actual_term_get_set]
    exact ⟨unchecked,noGc,fixed⟩
  have controls : (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl resultMachine.user =
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    dsimp only [resultMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,pushed,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent]
    unfold GenericPushRelevance.afterPush
    split <;> rfl
  have settings :
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl resultMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl resultMachine.user).gcInterval = 0 ∧
      resultMachine.threads.fixedScheduling = true :=
    ⟨(congrArg (·.checkedArithmetic) controls).trans originalSettings.1,
      (congrArg (·.gcInterval) controls).trans originalSettings.2.1,fields.2.2.2.2.2.2.2.trans originalSettings.2.2⟩
  have returned := S05DiagnosticAsMutReturn.step options limits remaining span debugOff validityFuel validationEq #[] cf done resultMachine id (base+offset)
    doneBody location valid0 (by rw [retCell,nextEq]) (by rw [retCell]) clocks valid15
    (by simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using destLive)
    (by simp [cf,cachedCaller,LocalPlaces.cachePlaceLayout]) callerClocks
    (by rw [dest];rfl) cont immediate va held rfl sourceEntry found finalTreeEq heldProtected
    (by simpa only [nextEq] using owner) helperThread helperActive settings.1 settings.2.1 settings.2.2
    (fields.2.2.2.2.1.trans ghost) (fields.2.2.2.2.2.1.trans shallow)
  let finalTracker := {held with global := held.global.endCall owned}
  have tag14 : finalTracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 14 := by
    simp only [finalTracker,GlobalState.endCall,held,TypedBorrowSteps.registeredTracker,TypedBorrowSteps.registeredGlobal,
      ReferenceBorrowDriver.allocatedTracker,TypedRetagEmpty.successorTag,nextEq,S05DiagnosticFnEntryRead.tag]
    rfl
  have tags : finalTracker.global.protectedTags = S05DiagnosticSharedRead.protections := by
    change (held.global.endCall owned).protectedTags = _
    change ((tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).remove (S05DiagnosticFnEntryRead.tag 13)) = _
    rw [protectedEq,nextEq]
    decide +kernel
  refine ⟨done,helperThread,helperActive,SuccessfulTrace.append trace (.next returned.1 (.refl _)),?_,?_,finalTracker,returned.2.2.1,tag14,tags⟩
  · simp [AsMutPtrReturn.writeFrame,LocalPlaces.cachePlaceLayout,cachedCaller]
  · change (GenericAsMutReturnState.machine options remaining span #[] cf done resultMachine
      (StackPopRelease.commitTree resultMachine.memory id sourceEntry S05DiagnosticAsMutRelease.released) held owned helperThread).memory.live.find? (fun row => row.1 == id) = _
    rw [returned.2.1]
    exact StackPopRelease.lookup_commit_same resultMachine.memory id sourceEntry S05DiagnosticAsMutRelease.released
end
end DuplicatePrefix.S05DiagnosticAsMutComplete
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticAsMutComplete." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic as_mut_ptr complete dependency {dependency}"
