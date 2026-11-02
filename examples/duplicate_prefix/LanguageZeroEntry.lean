import duplicate_prefix.LanguageZeroTail
import duplicate_prefix.LanguageZeroDispatch
import duplicate_prefix.CallLocalRead

/-! Complete actual initStackFrame for the zero-argument runtime guard, including
    caller return-place lookup, raw push, empty FnEntry scope, return-ABI check,
    and the real pushDone transition. -/
namespace DuplicatePrefix.LanguageZeroEntry
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory
open DuplicatePrefix
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def destination (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  (LocalPlaces.localRuntimePlace frames.size caller 5 RootCompilerFacts.boolLayout).stackView

noncomputable def rawFrame (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (dest : RuntimeStackPlace Provenance) :=
  let fresh := CallEntryFacts.freshRoot state.machine
  LanguageZeroEntryFacts.rawFrame options.userRelevantCrates fresh.1 dest fresh.2

noncomputable def pushedMachine (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (dest : RuntimeStackPlace Provenance) (current : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  (LanguageZeroEntryFacts.completed options.userRelevantCrates state dest current).machine

theorem actual_entry
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localValid : 5 < caller.locals.size)
    (localLive : caller.locals[5].value = .live (.immediate .uninit))
    (localCached : caller.locals[5].layout = some RootCompilerFacts.boolLayout)
    (noClock : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (destination frames caller)).stack thread.topUserRelevantFrame = some index)
    (present : (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (destination frames caller)).stack.frames[index]? = some current) :
    Call.initStackFrame
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      GuardCompilerFacts.languageCall.callee CopyPreconditions.Bodies.checkLanguage.loaded
      GuardCompilerFacts.languageAbi #[] false (destination frames caller) (.goto (some 1) .Continue)
      (Storage.withCurrent frames caller machine) =
    .ok () (Storage.withCurrent (frames.push caller)
      (LanguageZeroDone.doneFrame (rawFrame options (Storage.withCurrent frames caller machine)
        (destination frames caller)))
      (pushedMachine options (Storage.withCurrent frames caller machine) (destination frames caller) current)) := by
  let state := Storage.withCurrent frames caller machine
  let dest := destination frames caller
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let raw := rawFrame options state dest
  let post := pushedMachine options state dest current
  have placeRead := CallLocalRead.place_to_op_cached options limits (remaining+1) span debugOff
    frames caller machine 5 RootCompilerFacts.boolLayout .uninit localValid localLive localCached
    (by decide +kernel) noClock ghost
  have pushed := LanguageZeroEntryFacts.actual_push_raw options limits (remaining+1) span debugOff
    state dest thread index current active top present
  have pushRaw : h.pushRaw () GuardCompilerFacts.languageCall.callee
      CopyPreconditions.Bodies.checkLanguage.loaded dest (.goto (some 1) .Continue) state =
      .ok () (LanguageZeroEntryFacts.completed options.userRelevantCrates state dest current) := by
    change CallMachine.pushRaw (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle
      (PreparedContracts.actualConfig options () (remaining+1) span).compiler.debugAssertions
      GuardCompilerFacts.languageCall.callee CopyPreconditions.Bodies.checkLanguage.loaded dest
      (.goto (some 1) .Continue) state = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).debug, debugOff]
    exact pushed
  have pushRawDest : h.pushRaw () GuardCompilerFacts.languageCall.callee
      CopyPreconditions.Bodies.checkLanguage.loaded (destination frames caller)
      (.goto (some 1) .Continue) state =
      .ok () (LanguageZeroEntryFacts.completed options.userRelevantCrates state
        (destination frames caller) current) := by simpa [dest] using pushRaw
  have rawBody : raw.body = CopyPreconditions.Bodies.checkLanguage.loaded.body := rfl
  have rawIdentity : raw.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity := rfl
  have rawCallee : raw.functionInstance = GuardCompilerFacts.languageCall.callee := rfl
  have rawPreamble : raw.location = .unwinding GuardCompilerFacts.languagePreamble := by rfl
  have rawTrack : raw.trackCallerArg = none := by rfl
  have rawValid : 0 < raw.locals.size := by
    have size : raw.locals.size = 3 := by with_unfolding_all rfl
    rw [size]
    decide
  have rawDead : raw.locals[0].value = .dead := by with_unfolding_all rfl
  have rawNoClock : raw.extra.dataRace = none := by
    simp [raw, rawFrame, LanguageZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
      state, Storage.withCurrent, noRace]
  have postTracked : post.borrowTracker = some tracker := by
    simp [post, pushedMachine, LanguageZeroEntryFacts.completed, CallEntryFacts.freshRoot,
      Storage.withCurrent, GenericPushRelevance.afterPush]
    split <;> exact tracked
  have postNoRace : post.dataRace = none := by
    simp [post, pushedMachine, LanguageZeroEntryFacts.completed, CallEntryFacts.freshRoot,
      Storage.withCurrent, GenericPushRelevance.afterPush, CallEntryFacts.cacheTop]
    split <;> exact noRace
  have retEq : GuardCompilerFacts.languageAbi.ret = GuardCompilerFacts.languageAbi.ret := by decide +kernel
  have tail := LanguageZeroTail.action_actual options limits remaining span (frames.push caller) raw post
    GuardCompilerFacts.languagePreamble rawPreamble rawTrack rawBody rawIdentity rawCallee
    ⟨.immediate .uninit, RootCompilerFacts.boolLayout⟩ ⟨.uninit, rfl⟩ rawValid rawDead rawNoClock postNoRace
    tracker postTracked retEq
  rw [LanguageZeroCallCore.actual_entry_eq, LanguageZeroTail.core_eq]
  simp only [bind, EStateM.bind]
  have destEq : destination frames caller =
      (LocalPlaces.localRuntimePlace frames.size caller 5 RootCompilerFacts.boolLayout).stackView := rfl
  rw [destEq]
  rw [placeRead]
  simp only [bind, EStateM.bind]
  rw [← destEq]
  rw [pushRawDest]
  dsimp only [state, dest, raw, post]
  exact tail

end
end DuplicatePrefix.LanguageZeroEntry

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LanguageZeroEntry.actual_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual runtime zero-argument entry dependency {dependency}"
