import duplicate_prefix.AddUncachedCall
import duplicate_prefix.PtrMetadataReturn
namespace DuplicatePrefix.AddCallStep
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts AddEntry AddCallTerminator AddUncachedCall
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
    (pointer : Scalar Provenance) (n : UInt64) (valid : 21 < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[21].value = .live (.immediate old))
    (uncached : caller.locals[21].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨7,RootCallerLocation.statementCount 7⟩)
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
    (valid22 : 22 < caller.locals.size) (valid23 : 23 < caller.locals.size)
    (live22 : caller.locals[22].value = .live (.immediate (.scalar pointer)))
    (cache22 : caller.locals[22].layout = some CopyCompilerFacts.destPointerLayout)
    (live23 : caller.locals[23].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache23 : caller.locals[23].layout = some RootCompilerFacts.usizeLayout) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames caller machine) =
      ((Storage.withCurrent (frames.push (cachedCaller caller valid))
        (initialized (Storage.withCurrent frames (cachedCaller caller valid) (accountedMachine options remaining span machine))
          (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 21 CopyCompilerFacts.destPointerLayout).stackView (.goto (some 8) .Continue) noRace pointer n)
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
  have effect := AddUncachedCall.call_uncached options limits remaining span debug frames caller next tracker nextTracked pointer n
    valid old live uncached noClocks nextRace body identity callee trackNone location fuel validationFuel nextGhost nextShallow
    thread nextActive top relevant budget budgetEq nextBackend source cmp valid22 valid23 live22 cache22 live23 cache23
  have accounting := SourceControl.before_terminator cfg limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () before = (nextState,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[7]'(by with_unfolding_all decide +kernel)
  have blockAt : caller.body.basicBlocks[7]? = some block := by rw [body]; simp [block]
  have noStatement : block.statements[13]? = none := by with_unfolding_all rfl
  have count : RootCallerLocation.statementCount 7 = 13 := by with_unfolding_all rfl
  have located : caller.location = .mir ⟨7,13⟩ := by simpa only [count] using location
  apply GenericCallStages.source_step cfg limits () before nextState _ caller ⟨7,13⟩ block
    HelperCompilerFacts.addCall.function #[AddEvaluateCall.argument0,AddEvaluateCall.argument1] ⟨21,#[]⟩
    (some 8) .Continue .Normal ⟨34⟩
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement source_call accounting' effect
  simp [Storage.withCurrent,nextState]
end DuplicatePrefix.AddCallStep
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddCallStep.step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual add call-step dependency {dependency}"
