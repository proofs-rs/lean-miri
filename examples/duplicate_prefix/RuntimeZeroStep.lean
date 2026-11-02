import duplicate_prefix.RuntimeZeroUncached
import duplicate_prefix.PtrMetadataReturn
namespace DuplicatePrefix.RuntimeZeroStep
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix RuntimeZeroUncached
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def accountedMachine := PtrMetadataReturn.accountedMachine
theorem step
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (original : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : original.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : original.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : original.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : original.location = .mir ⟨0,3⟩)
    (originalSize : 1 < original.locals.size)
    (originalLive : original.locals[1].value = .live (.immediate .uninit))
    (originalUncached : original.locals[1].layout = none)
    (originalNoClocks : original.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine)) (RuntimeZeroEntry.destination frames original)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine)) (RuntimeZeroEntry.destination frames original)).stack.frames[threadIndex]? = some current)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames original machine) =
      (Storage.withCurrent (frames.push (cachedCaller original originalSize))
        (RuntimeZeroDone.doneFrame (RuntimeZeroEntry.rawFrame options (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine))
          (RuntimeZeroEntry.destination frames original)))
        (RuntimeZeroEntry.pushedMachine options (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine))
          (RuntimeZeroEntry.destination frames original) current), .ok true) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent frames original machine
  let next := accountedMachine options remaining span machine
  let nextState := Storage.withCurrent frames original next
  have nextTracked : next.borrowTracker = some tracker := tracked
  have nextRace : next.dataRace = none := noRace
  have nextActive : next.threads.activeThread? = some thread := active
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    change (PtrMetadataReturn.accountedMachine options remaining span machine).user.payload.payload.user.backend = _
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextGhost : next.user.payload.ghost = false := by
    change (PtrMetadataReturn.accountedMachine options remaining span machine).user.payload.ghost = false
    rw [PtrMetadataReturn.accounted_ghost]; exact ghost
  have effect := RuntimeZeroUncached.call_uncached options limits remaining budget dispatchFuel span source cmp debugOff frames original next
    body identity callee location originalSize originalLive originalUncached originalNoClocks nextRace nextBackend nextGhost
    tracker nextTracked thread threadIndex current nextActive top present
  have accounting := SourceControl.before_terminator cfg limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () before = (nextState,.ok ()) := accounting
  let block := CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  have blockAt : original.body.basicBlocks[0]? = some block := by rw [body]; simp [block]
  have noStatement : block.statements[3]? = none := by with_unfolding_all rfl
  have sourceCall : block.terminator.kind = .Call RuntimeZeroCallStep.function #[] ⟨1,#[]⟩ (some 1) .Continue .Misc ⟨159⟩ := by
    with_unfolding_all rfl
  apply GenericCallStages.source_step cfg limits () before nextState _ original ⟨0,3⟩ block
    RuntimeZeroCallStep.function #[] ⟨1,#[]⟩ (some 1) .Continue .Misc ⟨159⟩
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement sourceCall accounting' effect
  simp [Storage.withCurrent,nextState]
end DuplicatePrefix.RuntimeZeroStep
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RuntimeZeroStep.step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved language actual step dependency {dependency}"
