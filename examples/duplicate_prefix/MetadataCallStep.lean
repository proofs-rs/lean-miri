import duplicate_prefix.MetadataUncachedCall
namespace DuplicatePrefix.MetadataCallStep
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts MetadataEntry MetadataCallTerminator MetadataUncachedCall
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem step (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (body : caller.body = HelperCompilerFacts.lenBody.body)
    (identity : caller.bodyIdentity = HelperCompilerFacts.lenBody.identity)
    (callee : caller.functionInstance = HelperCompilerFacts.lenCall.callee)
    (located : caller.location = .mir ⟨0,2⟩)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (valid2 : 2 < caller.locals.size)
    (value2 : caller.locals[2].value = .live (.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached2 : caller.locals[2].layout = some PtrMetadataHelper.rawLayout)
    (valid : 0 < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[0].value = .live (.immediate old))
    (uncached : caller.locals[0].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) (PtrMetadataReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) (PtrMetadataReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames caller machine) =
      ((Storage.withCurrent (frames.push (cachedCaller caller valid))
        (initialized options (Storage.withCurrent frames (cachedCaller caller valid) (PtrMetadataReturn.accountedMachine options remaining span machine))
          (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView
          (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len))
        (MetadataPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) (PtrMetadataReturn.accountedMachine options remaining span machine))
          (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView current).machine), .ok true) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent frames caller machine
  let next := PtrMetadataReturn.accountedMachine options remaining span machine
  let nextState := Storage.withCurrent frames caller next
  have nextTracked : next.borrowTracker = some tracker := tracked
  have nextRace : next.dataRace = none := noRace
  have nextActive : next.threads.activeThread? = some thread := active
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    change (PtrMetadataReturn.accountedMachine options remaining span machine).user.payload.payload.user.backend = _
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextGhost : next.user.payload.ghost = false := by rw [PtrMetadataReturn.accounted_ghost];exact ghost
  have nextShallow : next.user.payload.validation = .Shallow := by rw [PtrMetadataReturn.accounted_validation];exact shallow
  have effect := MetadataUncachedCall.call_uncached options limits remaining budget dispatchFuel span debug frames caller next
    tracker nextTracked carrier len body identity callee located source cmp valid2 value2 cached2 valid old live uncached
    noClocks nextRace nextBackend fuel validationFuel nextGhost nextShallow thread index current nextActive top present
  have accounting := SourceControl.before_terminator cfg limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () before = (nextState,.ok ()) := accounting
  let block := HelperCompilerFacts.lenBody.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  have blockAt : caller.body.basicBlocks[0]? = some block := by rw [body];simp [block]
  have noStatement : block.statements[2]? = none := by with_unfolding_all rfl
  apply GenericCallStages.source_step cfg limits () before nextState _ caller ⟨0,2⟩ block
    PtrMetadataHelper.resolved.function #[MetadataEvaluateCall.argument] ⟨0,#[]⟩ (some 1) .Continue sourceKind fnSpan
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement source_call accounting' effect
  simp [Storage.withCurrent,nextState]
end
end DuplicatePrefix.MetadataCallStep
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataCallStep.step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual metadata call-step dependency {dependency}"
