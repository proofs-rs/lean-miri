import duplicate_prefix.MetadataEntry
import duplicate_prefix.MetadataDispatch
import duplicate_prefix.CallItemDispatch
namespace DuplicatePrefix.MetadataDispatchEntry
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts MetadataEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem actual_dispatch (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (valid : 0 < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[0].value = .live (.immediate old))
    (cached : caller.locals[0].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current) :
    Call.initFnCall (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (budget+1) ⟨.Instance PtrMetadataHelper.resolved.callee,.Rust,some PtrMetadataHelper.abi,
      #[.Copy ⟨.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len),PtrMetadataHelper.rawLayout⟩],
      false,(LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView,some 1,.Continue⟩
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized options (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView
          (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len))
        (MetadataPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView current).machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView
  let args : Array (FnArg Provenance) := #[.Copy ⟨.immediate (PtrMetadataComplete.rawImmediate carrier
    (PreparedContracts.actualConfig options () remaining span).access.runtime.base len),PtrMetadataHelper.rawLayout⟩]
  have entry := MetadataEntry.actual_entry options limits remaining span debug frames caller machine tracker tracked carrier len
    valid old live cached noClocks noRace fuel validationFuel ghost shallow thread index current active top present
  have find := MetadataDispatch.find_mir options limits (remaining+1) span state args destination (some 1) .Continue backend noRace
  have rust : h.isRustCall .Rust = false := by
    change (PreparedContracts.actualConfig options () (remaining+1) span).calls.compiler.isRustCall .Rust = false
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).callCompiler]
    rfl
  apply CallItemDispatch.dispatch_one h _ state _ budget
  rw [CallItemDispatch.item_step h PtrMetadataHelper.resolved.callee 10 PtrMetadataHelper.abi args false destination
    (some 1) .Continue .Rust PtrMetadataHelper.callee_kind MetadataCallFacts.abi_flags.2.1 rust]
  unfold CallItemDispatch.itemStage
  simp only [bind,EStateM.bind]
  rw [find]
  simp only [bind,EStateM.bind]
  dsimp only [h,args,destination,state]
  rw [entry]
  rfl
end
end DuplicatePrefix.MetadataDispatchEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataDispatchEntry.actual_dispatch) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved complete actual metadata dispatch dependency {dependency}"
