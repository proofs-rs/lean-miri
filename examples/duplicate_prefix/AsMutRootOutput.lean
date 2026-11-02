import duplicate_prefix.AsMutRootComplete
import duplicate_prefix.MetadataOutputFacts
import duplicate_prefix.PushThread
import duplicate_prefix.RootThreadCache
import duplicate_prefix.CopyHelperCleanup
namespace DuplicatePrefix.AsMutRootOutput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
noncomputable section
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def caller (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size) (value : Scalar Provenance) :=
  let cached := AsMutUncachedCall.cachedCaller frame valid
  {AsMutPtrReturn.writeFrame cached 15 (.scalar value) (by simpa [cached,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid)
    with location := .mir ⟨7,0⟩}

theorem caller_metadata (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size) (value : Scalar Provenance) :
    (caller frame valid value).body = frame.body ∧ (caller frame valid value).bodyIdentity = frame.bodyIdentity ∧
    (caller frame valid value).functionInstance = frame.functionInstance ∧ (caller frame valid value).extra = frame.extra ∧
    (caller frame valid value).returnContinuation = frame.returnContinuation ∧ (caller frame valid value).returnPlace = frame.returnPlace ∧
    (caller frame valid value).vaList = frame.vaList ∧ (caller frame valid value).localsIdentity = frame.localsIdentity ∧
    (caller frame valid value).locals.size = frame.locals.size ∧ (caller frame valid value).location = .mir ⟨7,0⟩ := by
  simp only [caller,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  repeat' constructor

theorem caller_slot (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size) (value : Scalar Provenance) :
    (caller frame valid value).locals[15]'(by simpa [caller,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid) =
    ⟨.live (.immediate (.scalar value)),some CopyCompilerFacts.destPointerLayout⟩ := by
  simp only [caller,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]

theorem caller_other (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size) (value : Scalar Provenance)
    (index : Nat) (different : index ≠ 15) : (caller frame valid value).locals[index]? = frame.locals[index]? := by
  simp [caller,AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set,different,Ne.symm different]

def held (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId) :=
  let registered := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  {registered with global := registered.global.endCall (({} : FrameState).addProtector id tracker.global.nextPointerTag)}

def machine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tags : Fin 6 → BorTag)
    (capacity offset len : UInt64) (done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :=
  let cached := AsMutUncachedCall.cachedCaller frame valid
  let next := AsMutPtrReturn.accountedMachine options remaining span before
  let state := Storage.withCurrent #[] cached next
  let dest := (LocalPlaces.localRuntimePlace 0 cached 15 CopyCompilerFacts.destPointerLayout).stackView
  let post := (AsMutPush.completed options.userRelevantCrates state dest cached).machine
  let tree := NestedBorrowAccess.nestedTree tags (BorrowRangeAccess.partitionWithInside capacity offset (offset+len) BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))
  let entered := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with memory := RetagEntry.updatedMemory post.memory id entry tree}
  let registered := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let updated := {entry with allocation := entry.allocation.setExtra tree}
  let helperThread := PushThread.after thread 1 (AsMutFrame.rank options.userRelevantCrates) frame.extra.userRelevance
  AsMutPtrReturn.poppedMachine #[] cached done
    (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span entered)
      (StackPopRelease.commitTree entered.memory id updated tree) registered (({} : FrameState).addProtector id tracker.global.nextPointerTag))
    (helperThread.topUserRelevantFrame.getD 1)

section
variable (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tags : Fin 6 → BorTag)
    (capacity offset len : UInt64) (done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord)

theorem preserved :
    let after := machine options remaining span frame valid before tracker fresh id entry tags capacity offset len done thread
    after.borrowTracker = some (held tracker fresh id) ∧ after.dataRace = before.dataRace ∧
    after.threads.fixedScheduling = before.threads.fixedScheduling ∧
    after.user.addresses = before.user.addresses ∧ after.user.payload.ghost = before.user.payload.ghost ∧
    after.user.payload.validation = before.user.payload.validation ∧
    after.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
    after.user.payload.payload.user.backend = before.user.payload.payload.user.backend ∧
    after.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras := by
  dsimp only
  unfold machine
  dsimp only
  unfold AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
  split <;> unfold AsMutPtrReturn.accountedMachine SourceControl.accounted AsMutPush.completed Storage.withCurrent
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals unfold GenericPushRelevance.afterPush
  all_goals dsimp only
  all_goals split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem control :
    (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (machine options remaining span frame valid before tracker fresh id entry tags capacity offset len done thread).user =
      TerminatorClock.advance (TerminatorClock.advance
        ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user)) := by
  unfold machine
  dsimp only
  unfold AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
  split <;> unfold AsMutPtrReturn.accountedMachine SourceControl.accounted AsMutPush.completed Storage.withCurrent
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals unfold GenericPushRelevance.afterPush
  all_goals dsimp only
  all_goals split <;> rfl

theorem memory_eq :
    let tree := NestedBorrowAccess.nestedTree tags (BorrowRangeAccess.partitionWithInside capacity offset (offset+len) BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))
    (machine options remaining span frame valid before tracker fresh id entry tags capacity offset len done thread).memory =
      StackPopRelease.commitTree (RetagEntry.updatedMemory before.memory id entry tree) id
        {entry with allocation := entry.allocation.setExtra tree} tree := by
  dsimp only
  unfold machine
  dsimp only
  unfold AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
  split <;> unfold AsMutPush.completed Storage.withCurrent GenericPushRelevance.afterPush
  all_goals dsimp only
  all_goals split <;> rfl

theorem active (source : before.threads.activeThread? = some thread) (cached : thread.topUserRelevantFrame = some 0) :
    (machine options remaining span frame valid before tracker fresh id entry tags capacity offset len done thread).threads.activeThread? = some thread := by
  unfold machine
  dsimp only [AsMutPtrReturn.poppedMachine]
  apply RootThreadCache.pop_active _ _ _ thread (AsMutFrame.rank options.userRelevantCrates) frame.extra.userRelevance ?_ cached
  exact PushThread.active_after _ thread 1 (AsMutFrame.rank options.userRelevantCrates) frame.extra.userRelevance source

theorem buffer_lookup :
    let tree := NestedBorrowAccess.nestedTree tags (BorrowRangeAccess.partitionWithInside capacity offset (offset+len) BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))
    (machine options remaining span frame valid before tracker fresh id entry tags capacity offset len done thread).memory.live.find? (fun row => row.1 == id) =
      some (id,{entry with allocation := entry.allocation.setExtra tree}) := by
  dsimp only
  unfold machine
  dsimp only
  unfold AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
  split <;> exact MemoryCopyBridge.live_lookup_replaced _ id _
theorem other_lookup (other : AllocId) (otherEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (different : other ≠ id) (present : before.memory.live.find? (fun row => row.1 == other) = some (other,otherEntry)) :
    (machine options remaining span frame valid before tracker fresh id entry tags capacity offset len done thread).memory.live.find? (fun row => row.1 == other) = some (other,otherEntry) := by
  rw [memory_eq]
  have first := StackPopRelease.lookup_commit_other before.memory id other entry otherEntry
    (NestedBorrowAccess.nestedTree tags (BorrowRangeAccess.partitionWithInside capacity offset (offset+len) BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))) different present
  exact StackPopRelease.lookup_commit_other _ id other _ otherEntry _ different first

end

theorem all_immediate (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size) (value : Scalar Provenance)
    (all : CopyHelperCleanup.AllImmediate frame) : CopyHelperCleanup.AllImmediate (caller frame valid value) := by
  exact CopyHelperCleanup.all_immediate_written frame 15 CopyCompilerFacts.destPointerLayout (.scalar value) valid all
theorem mask_after (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (next : tracker.global.nextPointerTag = tags 5)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false) :
    ProtectedBorrowAccess.SixMask tags (held tracker fresh id).global.protectedTags false := by
  intro i
  change ((TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).global.endCall
    (({} : FrameState).addProtector id tracker.global.nextPointerTag)).protectedTags.contains (tags i) = _
  rw [StackPopRelease.end_call_contains]
  by_cases last : i = 5
  · subst i
    simp [FrameState.addProtector,next]
  · have different : tags i ≠ tracker.global.nextPointerTag := by rw [next];exact fun h => last (distinct h)
    have notMember : tags i ∉ (({} : FrameState).addProtector id tracker.global.nextPointerTag).protectedTags.toList.map Prod.snd := by simp [FrameState.addProtector,different]
    rw [if_neg notMember]
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains (tags i) = _
    rw [ProtectorInsertion.contains_other _ _ _ _ different]
    have previous := mask i (by have bound := i.isLt;have ne5 : i.val ≠ 5 := fun h => last (Fin.ext h);omega)
    simpa only [Bool.false_and,Bool.or_false] using previous

theorem caller_track (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size) (value : Scalar Provenance) :
    (AsMutRootOutput.caller frame valid value).trackCallerArg = frame.trackCallerArg := rfl

theorem run
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree5 tags (partitionWithInside capacity offset (offset+len) rootLocation (location5 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : beforeMachine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag = tags 5)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : beforeMachine.user.payload.ghost = false) (shallow : beforeMachine.user.payload.validation = .Shallow)
    (cachedAddress : beforeMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : beforeMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : beforeMachine.dataRace = none)
    (backend : beforeMachine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller beforeMachine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller beforeMachine)).entries.any (·.value.ty == 4) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : beforeMachine.threads.activeThread? = some thread)
    (cachedThread : thread.topUserRelevantFrame = some 0) :
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] caller beforeMachine)
        (Storage.withCurrent #[]
          (AsMutRootOutput.caller caller destValid (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
            (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset)))))
          (AsMutRootOutput.machine options remaining span caller destValid beforeMachine tracker fresh id entry tags capacity offset len done thread)) := by
  let cached := AsMutUncachedCall.cachedCaller caller destValid
  let next := AsMutPtrReturn.accountedMachine options remaining span beforeMachine
  let state := Storage.withCurrent #[] cached next
  let dest := (LocalPlaces.localRuntimePlace 0 cached 15 CopyCompilerFacts.destPointerLayout).stackView
  have topKnown : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates state dest).stack thread.topUserRelevantFrame = some 0 := by
    simp only [FrameRelevance.top,cachedThread,Option.orElse_some]
  have presentKnown : (AsMutPush.pushed options.userRelevantCrates state dest).stack.frames[0]? = some cached := by simp [state,AsMutPush.pushed,Storage.withCurrent]
  obtain ⟨done,trace,extra⟩ := AsMutRootComplete.run_exact options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds #[] caller beforeMachine tracker enabled defaultMode mask nextTag fresh
    body identity callee located source valid16 value16 cached16 destValid destLive uncached callerClocks ghost shallow cachedAddress present race backend metadata notConstructed
    unchecked noGc fixed thread 0 cached active topKnown presentKnown
  refine ⟨done,?_⟩
  simpa only [AsMutRootOutput.machine,AsMutRootOutput.caller,PushThread.after,nextTag,cached,AsMutFrame.rawFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Storage.withCurrent,Array.size_push,Array.size_empty,Allocation.setExtra,Allocation.mapExtra,Nat.zero_add] using trace

end
end DuplicatePrefix.AsMutRootOutput

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.AsMutRootOutput." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual asmut output dependency {dependency}"
