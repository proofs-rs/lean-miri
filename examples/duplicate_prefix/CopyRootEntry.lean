import duplicate_prefix.CopyCallStep
import duplicate_prefix.CopyEntryShape
import duplicate_prefix.CopyPushPreserves
import duplicate_prefix.SuccessfulTrace
namespace DuplicatePrefix.CopyRootEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
structure Input
    (options : EvalConfigurationCore.Options)
    (limits : ExecutionMachine.Limits)
    (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourcePointer destinationPointer : Scalar Provenance)
    (n : UInt64) where
  debug : options.place.debugAssertions = false
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker = some tracker
  valid : 18 < caller.locals.size
  old : Immediate Provenance
  live : caller.locals[18].value = .live (.immediate old)
  uncached : caller.locals[18].layout = none
  noClocks : caller.extra.dataRace = none
  noRace : machine.dataRace = none
  body : caller.body = RootBody.reflected.body.body
  identity : caller.bodyIdentity = RootBody.reflected.body.identity
  callee : caller.functionInstance = RootBody.reflected.functionInstance
  trackNone : caller.trackCallerArg = none
  location : caller.location = .mir ⟨8,RootCallerLocation.statementCount 8⟩
  fuel : Nat
  validationFuel : options.limits.validation = fuel+1
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  thread : Miri.Concurrency.ThreadRecord
  active : machine.threads.activeThread? = some thread
  top : thread.topUserRelevantFrame = some frames.size
  relevant : caller.extra.userRelevance > 0
  budget : Nat
  budgetEq : limits.callDispatch = budget+1
  backend : machine.user.payload.payload.user.backend = .none
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  source : PreparedContracts.SourceComparator
  cmp : ProjectionMetadataFacts.NullComparator
  valid19 : 19 < caller.locals.size
  valid21 : 21 < caller.locals.size
  valid24 : 24 < caller.locals.size
  live19 : caller.locals[19].value = .live (.immediate (.scalar sourcePointer))
  cache19 : caller.locals[19].layout = some CopyCompilerFacts.sourcePointerLayout
  live21 : caller.locals[21].value = .live (.immediate (.scalar destinationPointer))
  cache21 : caller.locals[21].layout = some CopyCompilerFacts.destPointerLayout
  live24 : caller.locals[24].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n))))
  cache24 : caller.locals[24].layout = some RootCompilerFacts.usizeLayout

variable
    (options : EvalConfigurationCore.Options)
    (limits : ExecutionMachine.Limits)
    (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourcePointer destinationPointer : Scalar Provenance)
    (n : UInt64)

noncomputable def cachedCaller (input : Input options limits remaining span frames caller machine sourcePointer destinationPointer n) := CopyUncachedCall.cachedCaller caller input.valid
noncomputable def enteredFrame (input : Input options limits remaining span frames caller machine sourcePointer destinationPointer n) :=
  CopyEntry.initialized (Storage.withCurrent frames (cachedCaller _ _ _ _ _ _ _ _ _ _ input) (CopyCallStep.accountedMachine options remaining span machine))
    (LocalPlaces.localRuntimePlace frames.size (cachedCaller _ _ _ _ _ _ _ _ _ _ input) 18 CopyHelperUnit.layout).stackView (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
noncomputable def entered (input : Input options limits remaining span frames caller machine sourcePointer destinationPointer n) := Storage.withCurrent
  (frames.push (cachedCaller _ _ _ _ _ _ _ _ _ _ input)) (enteredFrame _ _ _ _ _ _ _ _ _ _ input) (CopyPushPreserves.post options remaining span machine)
theorem step (input : Input options limits remaining span frames caller machine sourcePointer destinationPointer n) :
  ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () (Storage.withCurrent frames caller machine) =
    (entered _ _ _ _ _ _ _ _ _ _ input,.ok true) := by
  exact CopyCallStep.step options limits remaining span input.debug frames caller machine input.tracker input.tracked sourcePointer destinationPointer n input.valid input.old input.live input.uncached input.noClocks input.noRace input.body input.identity input.callee input.trackNone input.location input.fuel input.validationFuel input.ghost input.shallow input.thread input.active input.top input.relevant input.budget input.budgetEq input.backend input.unchecked input.noGc input.fixed input.source input.cmp input.valid19 input.valid21 input.valid24 input.live19 input.cache19 input.live21 input.cache21 input.live24 input.cache24
theorem trace (input : Input options limits remaining span frames caller machine sourcePointer destinationPointer n) : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent frames caller machine) (entered _ _ _ _ _ _ _ _ _ _ input) :=
  .next (step _ _ _ _ _ _ _ _ _ _ input) (.refl _)
end DuplicatePrefix.CopyRootEntry
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyRootEntry.step, ``DuplicatePrefix.CopyRootEntry.trace] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved copy root entry {dependency}"
