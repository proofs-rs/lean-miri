import duplicate_prefix.CopyUncachedCall
import duplicate_prefix.PtrMetadataReturn
namespace DuplicatePrefix.CopyCallStep
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts CopyEntry CopyCallTerminator CopyUncachedCall
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def accountedMachine := PtrMetadataReturn.accountedMachine
 theorem step (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64) (valid : 18 < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[18].value = .live (.immediate old))
    (uncached : caller.locals[18].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨8,RootCallerLocation.statementCount 8⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size)
    (relevant : caller.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (valid19 : 19 < caller.locals.size) (valid21 : 21 < caller.locals.size) (valid24 : 24 < caller.locals.size)
    (live19 : caller.locals[19].value = .live (.immediate (.scalar sourcePointer)))
    (cache19 : caller.locals[19].layout = some CopyCompilerFacts.sourcePointerLayout)
    (live21 : caller.locals[21].value = .live (.immediate (.scalar destinationPointer)))
    (cache21 : caller.locals[21].layout = some CopyCompilerFacts.destPointerLayout)
    (live24 : caller.locals[24].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache24 : caller.locals[24].layout = some RootCompilerFacts.usizeLayout) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames caller machine) =
      ((Storage.withCurrent (frames.push (cachedCaller caller valid))
        (initialized (Storage.withCurrent frames (cachedCaller caller valid) (accountedMachine options remaining span machine))
          (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 18 CopyHelperUnit.layout).stackView (.goto (some 9) .Continue) noRace sourcePointer destinationPointer n)
        (CallEntryFacts.freshRoot (accountedMachine options remaining span machine)).1), .ok true) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent frames caller machine
  let next := accountedMachine options remaining span machine
  let nextState := Storage.withCurrent frames caller next
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
  have nextShallow : next.user.payload.validation = .Shallow := by
    change (PtrMetadataReturn.accountedMachine options remaining span machine).user.payload.validation = .Shallow
    rw [PtrMetadataReturn.accounted_validation]; exact shallow
  have effect := CopyUncachedCall.call_uncached options limits remaining span debug frames caller next tracker nextTracked sourcePointer destinationPointer n
    valid old live uncached noClocks nextRace body identity callee trackNone location fuel validationFuel nextGhost nextShallow
    thread nextActive top relevant budget budgetEq nextBackend source cmp valid19 valid21 valid24 live19 cache19 live21 cache21 live24 cache24
  have accounting := SourceControl.before_terminator cfg limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () before = (nextState,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[8]'(by with_unfolding_all decide +kernel)
  have blockAt : caller.body.basicBlocks[8]? = some block := by rw [body]; simp [block]
  have noStatement : block.statements[4]? = none := by with_unfolding_all rfl
  have count : RootCallerLocation.statementCount 8 = 4 := by with_unfolding_all rfl
  have located : caller.location = .mir ⟨8,4⟩ := by simpa only [count] using location
  apply GenericCallStages.source_step cfg limits () before nextState _ caller ⟨8,4⟩ block
    HelperCompilerFacts.copyCall.function #[CopyEvaluateCall.argument0,CopyEvaluateCall.argument1,CopyEvaluateCall.argument2] ⟨18,#[]⟩
    (some 9) .Continue .Normal ⟨28⟩
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement source_call accounting' effect
  simp [Storage.withCurrent,nextState]
end DuplicatePrefix.CopyCallStep
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CopyCallStep.step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual add call-step dependency {dependency}"
