import duplicate_prefix.AsMutCallTerminator
import duplicate_prefix.CallUncachedLocal
namespace DuplicatePrefix.AsMutUncachedCall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess AsMutEntry AsMutCallTerminator
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def cachedCaller (frame : CompilerFrameContext.ActualFrame) (valid : (15 : MIR.LocalId) < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 15 CopyCompilerFacts.destPointerLayout valid

theorem compute_local15 (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 15
      (Storage.withCurrent frames frame machine) = .ok CopyCompilerFacts.destPointerLayout (Storage.withCurrent frames frame machine) := by
  have normalized : CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 15 = .ok 8 := by
    unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
    rw [body,identity,callee]
    with_unfolding_all rfl
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 8 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent frames frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent frames frame machine)) = _
  rw [CopyCompilerFacts.dest_pointer_layout_eq]
  rfl
theorem call_uncached
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
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
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
    (destValid : 15 < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let initial := Storage.withCurrent frames caller machine
    let before := Storage.withCurrent frames (cachedCaller caller destValid) machine
    let destination := (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AsMutEvaluateCall.terminator initial =
      .ok () (Storage.withCurrent (frames.push (cachedCaller caller destValid))
        (initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let cachedFrame := cachedCaller caller destValid
  let cachedState := Storage.withCurrent frames cachedFrame machine
  let destination := (LocalPlaces.localRuntimePlace frames.size cachedFrame 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let postMachine := (AsMutPush.completed options.userRelevantCrates cachedState destination current).machine
  let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
  let after := Storage.withCurrent (frames.push cachedFrame) (initialized options cachedState destination value adjusted id tracker.global.nextPointerTag) resultMachine
  have valid15' : (15 : MIR.LocalId) < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using destValid
  have valid16' : (16 : MIR.LocalId) < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid16
  have value15' : cachedFrame.locals[15].value = .live (.immediate old) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using destLive
  have cache15' : cachedFrame.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have value16' : cachedFrame.locals[16].value = .live (.immediate value) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set,value] using value16
  have cache16' : cachedFrame.locals[16].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached16
  have evaluated := AsMutEvaluateCall.evaluate options limits (remaining+1) span debugOff source cmp frames cachedFrame machine value
    body identity callee located valid16' value16' cache16' callerClocks ghost
  have dest := CallUncachedLocal.uncached options limits (remaining+1) span debugOff frames caller machine 15
    CopyCompilerFacts.destPointerLayout destValid uncached (by decide +kernel) (compute_local15 frames caller machine body identity callee)
  have dispatched := AsMutDispatchEntry.actual_dispatch options limits remaining budget span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds frames cachedFrame machine tracker enabled
    defaultMode mask nextTag fresh 15 valid15' old value15' cache15' callerClocks ghost shallow cachedAddress present race backend
    metadata notConstructed thread index current active top topPresent
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.asMutPtrAbi = true := AsMutCallFacts.abi_flags.2.1
  have oldIndex : h.frameIndex state = .ok frames.size state := by
    change (do match (←get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) state = _
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have newIndex : h.frameIndex after = .ok (frames.size+1) after := by
    change (do match (←get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) after = _
    simp [after,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  dsimp only
  apply GenericCallStages.call_terminator h () limits.callDispatch AsMutEvaluateCall.terminator
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ 7 .Continue sourceKind fnSpan
    state cachedState cachedState after caller frames.size (frames.size+1) destination
    ⟨.Instance HelperCompilerFacts.asMutPtrCall.callee,#[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩],.Rust,some HelperCompilerFacts.asMutPtrAbi,false⟩
    source_call (CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine) oldIndex dest evaluated
  · simpa only [dispatchFuel,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega

#print axioms call_uncached
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``call_uncached) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved uncached asmut dependency {dependency}"
end
end DuplicatePrefix.AsMutUncachedCall
