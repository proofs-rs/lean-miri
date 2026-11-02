import duplicate_prefix.CopyEntry
import duplicate_prefix.CopyDispatch
import duplicate_prefix.CopyFunctionFacts
import duplicate_prefix.CallItemDispatch
namespace DuplicatePrefix.CopyDispatchEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts CopyEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
 theorem actual_dispatch (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64) (callerId : MIR.LocalId) (valid : callerId < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[callerId].value = .live (.immediate old))
    (cached : caller.locals[callerId].layout = some CopyHelperUnit.layout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨8,RootCallerLocation.statementCount 8⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (index : Nat) (top : thread.topUserRelevantFrame = some index)
    (cachedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (indexValid : index < (frames.push caller).size) (lookup : (frames.push caller)[index]? = some cachedFrame)
    (relevant : cachedFrame.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (target : Option BasicBlockId) (unwind : UnwindAction) (dispatchBudget : Nat) :
    Call.initFnCall (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (dispatchBudget+1)
      ⟨.Instance HelperCompilerFacts.copyCall.callee, .Rust, some HelperCompilerFacts.copyAbi,
       #[.Copy (CopyInstall.first sourcePointer),.Copy (CopyInstall.second destinationPointer),.Copy (CopyInstall.third n)],true,
       (LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout).stackView,target,unwind⟩
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout).stackView (.goto target unwind) noRace sourcePointer destinationPointer n)
        (CallEntryFacts.freshRoot machine).1) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let dest := (LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout).stackView
  let args := #[FnArg.Copy (CopyInstall.first sourcePointer),FnArg.Copy (CopyInstall.second destinationPointer),.Copy (CopyInstall.third n)]
  have entry := CopyEntry.actual_entry options limits remaining span debug frames caller machine tracker tracked sourcePointer destinationPointer n callerId valid
    old live cached noClocks noRace body identity callee trackNone location fuel validationFuel ghost shallow
    thread active index top cachedFrame indexValid lookup relevant budget budgetEq (.goto target unwind)
  have found := CopyDispatch.find_mir options limits (remaining+1) span state args dest target unwind backend noRace
  have rust : h.isRustCall .Rust = false := by
    change (PreparedContracts.actualConfig options () (remaining+1) span).calls.compiler.isRustCall .Rust = false
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).callCompiler]
    rfl
  apply CallItemDispatch.dispatch_one h _ state _ dispatchBudget
  rw [CallItemDispatch.item_step h HelperCompilerFacts.copyCall.callee HelperCompilerFacts.copyCall.callee.defId
    HelperCompilerFacts.copyAbi args true dest target unwind .Rust
    (congrArg (·.kind) CopyFunctionFacts.function_kind_matches_call) CopyCallFacts.abi_flags.2.1 rust]
  unfold CallItemDispatch.itemStage
  simp only [bind,EStateM.bind]
  rw [found]
  simp only [EStateM.bind]
  rw [entry]
  rfl
end DuplicatePrefix.CopyDispatchEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CopyDispatchEntry.actual_dispatch) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual add dispatch dependency {dependency}"
