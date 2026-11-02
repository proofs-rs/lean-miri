import duplicate_prefix.S05DiagnosticAsMutInstall
import duplicate_prefix.GenericAsMutCallFrontend
namespace DuplicatePrefix.S05DiagnosticAsMutCall
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess AsMutUncachedCall
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual root-caller as_mut_ptr frame entry and call terminator, deriving
all diagnostic borrow and installation operations internally. -/
theorem positive
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
    (destValid : 15 < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
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
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let initial := Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine
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
    (Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
      .ok () (Storage.withCurrent #[cachedCaller caller destValid]
        (AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine)) ∧
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AsMutEvaluateCall.terminator initial =
      .ok () (Storage.withCurrent ((#[] : Array CompilerFrameContext.ActualFrame).push (cachedCaller caller destValid))
        (AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) := by
  let frames : Array CompilerFrameContext.ActualFrame := #[]
  let cf := cachedCaller caller destValid
  let before := Storage.withCurrent frames cf machine
  let destination := (LocalPlaces.localRuntimePlace frames.size cf 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let frame := AsMutEntry.rawFrame options before destination
  let post := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let result := AsMutInstall.resultFrame frame (by rw [AsMutEntry.raw_size];decide) value adjusted {} id tracker.global.nextPointerTag
  let finalTree := S05DiagnosticAsMutInstall.finalTree entry.allocation.extra tracker parentTag offset len
  let afterMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry finalTree}
  have valid15 : 15 < cf.locals.size := by simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout] using destValid
  have live15 : cf.locals[15].value = .live (.immediate old) := by
    simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout] using destLive
  have cache15 : cf.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cf,cachedCaller,LocalPlaces.cachePlaceLayout]
  have installed : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (AsMutInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent (frames.push cf) frame post) = .ok (1,1) (Storage.withCurrent (frames.push cf) result afterMachine) := by
    have tracked : post.borrowTracker = some tracker := by
      simp only [post,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
      split <;> exact enabled
    have fg : frame.extra.borrowTracker = some ({} : FrameState) := by
      simp [frame,AsMutEntry.rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,enabled]
    have fc : frame.extra.dataRace = none := by
      simp [frame,AsMutEntry.rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,race]
    apply S05DiagnosticAsMutInstall.scoped_install_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits (frames.push cf) frame post tracker tracked {} fg fresh
      treeEq parentEq nextEq protectedEq offsetEq lenEq bounds (by rw [AsMutEntry.raw_size];decide) rfl rfl rfl rfl rfl fc
    all_goals
      simp only [post,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
      split
      all_goals first | exact ghost | exact shallow | exact cachedAddress | exact present | exact race | exact metadata | exact notConstructed
  have resultSize : result.locals.size = 5 := by
    simpa only [result,AsMutInstall.resultFrame,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame,
      RootArgumentEntry.liveFrame,AsMutPtrArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.size_set]
      using AsMutEntry.raw_size options before destination
  have resultDead : result.locals[0].value = .dead := by
    simp [result,AsMutInstall.resultFrame,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame,
      RootArgumentEntry.liveFrame,AsMutPtrArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      frame,AsMutEntry.rawFrame,AsMutFrame.rawFrame,Frame.create]
    with_unfolding_all rfl
  have resultClocks : result.extra.dataRace = none := by
    simp [result,AsMutInstall.resultFrame,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame,
      RootArgumentEntry.liveFrame,AsMutPtrArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      frame,AsMutEntry.rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,race]
  have tail : AsMutTail.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      value ⟨.immediate old,CopyCompilerFacts.destPointerLayout⟩ (Storage.withCurrent (frames.push cf) frame post) =
      .ok () (Storage.withCurrent (frames.push cf) (AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) afterMachine) := by
    have getframe := CallEntryLocals.get_frame options limits (remaining+1) span (frames.push cf) frame post
    have setframe := CallEntryLocals.set_frame options limits (remaining+1) span (frames.push cf) frame frame post
    have finished := AsMutFinish.finish options limits (remaining+1) span (frames.push cf) result afterMachine AsMutEntryFacts.asMutPreamble
      rfl rfl rfl (by rw [resultSize];decide) resultDead resultClocks
    unfold AsMutTail.action
    simp only [bind,EStateM.bind]
    rw [getframe]
    dsimp only
    have loc : frame.location = .unwinding AsMutEntryFacts.asMutPreamble := by rfl
    rw [loc]
    simp only [pure,Pure.pure,EStateM.pure,EStateM.bind]
    have same : {frame with trackCallerArg := none} = frame := by rfl
    rw [←loc,same,setframe]
    dsimp only
    rw [installed]
    exact finished
  have entryDone : Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
      .ok () (Storage.withCurrent (frames.push cf) (AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) afterMachine) := by
    have read := CallLocalRead.place_to_op_cached options limits (remaining+1) span debugOff frames cf machine 15
      CopyCompilerFacts.destPointerLayout old valid15 live15 cache15 (by decide +kernel) callerClocks ghost
    have pushed := AsMutPush.actual_push options () (remaining+1) span before destination thread index current active top topPresent
    rw [AsMutCallCore.actual_entry_eq,AsMutTail.core_eq]
    simp only [bind,EStateM.bind]
    rw [read]
    dsimp only
    have actualPush : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).pushRaw ()
        HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) before =
        .ok () (AsMutPush.completed options.userRelevantCrates before destination current) := by
      change CallMachine.pushRaw (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle
        (PreparedContracts.actualConfig options () (remaining+1) span).compiler.debugAssertions
        HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) before = _
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).debug,debugOff]
      exact pushed
    rw [actualPush]
    exact tail
  refine ⟨entryDone,?_⟩
  exact GenericAsMutCallFrontend.call_uncached options limits remaining budget dispatchFuel span debugOff source cmp
    caller _ machine afterMachine value body identity callee located valid16 value16 cached16 destValid old destLive uncached
    callerClocks ghost backend race entryDone

#print axioms positive
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticAsMutCall." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic as_mut call dependency {dependency}"
end
end DuplicatePrefix.S05DiagnosticAsMutCall
