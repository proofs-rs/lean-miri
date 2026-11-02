import duplicate_prefix.WildcardGapLenZeroEntry
import duplicate_prefix.LenUncachedCall
import duplicate_prefix.LenPositiveEntry
import duplicate_prefix.LenZeroEntry
import duplicate_prefix.LenUncachedFrontend
namespace DuplicatePrefix.WildcardGapLenUncachedCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem integer_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 11 < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[11].value = .live (.immediate old))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss machine.user.addresses machine.memory address)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none) :
    let cfg := config options remaining span
    let state := Storage.withCurrent frames (cachedCaller caller valid) machine
    let destination := (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
    let afterFrame := LenInstall.resultFrame frame frameValid output
    let resultMachine := ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch LenCallSource.callTerminator (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push (cachedCaller caller valid))
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine) := by
  let cachedFrame := cachedCaller caller valid
  have cachedValid : 11 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have cachedLive : cachedFrame.locals[11].value = .live (.immediate old) := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have cachedLayout : cachedFrame.locals[11].layout = some RootCompilerFacts.usizeLayout := by simp [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout]
  have initialized := WildcardGapLenZeroEntry.integer_zero options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq address nonzero frames cachedFrame machine tracker enabled fresh 11 cachedValid old cachedLive cachedLayout noClocks ghost shallow race thread index current active top presentFrame addressMode miss metadata notConstructed
  exact LenUncachedFrontend.call_uncached_of_entry options limits (remaining+1) budget dispatchFuel span debugOff frames caller machine _
    sourceBody identity callee located source cmp sourceValid sourceLive sourceCached valid uncached noClocks race backend ghost _ _ initialized

end
end DuplicatePrefix.WildcardGapLenUncachedCall
