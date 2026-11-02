import duplicate_prefix.RuntimeZeroDispatch
import duplicate_prefix.GenericPushRelevance
namespace DuplicatePrefix.RuntimeZeroEntryFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open DuplicatePrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

open Lean Elab Tactic in
elab "unfold_frame_meta_runtime" : tactic => do
  let env ← getEnv
  let names ← ([".CompilerFrameMetadata.lift", ".CompilerFrameMetadata.definitionCrate"] : List String).mapM
    fun (suffix : String) => do
      let candidates := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match candidates with
      | [name] => pure name
      | _ => throwError s!"expected unique frame metadata helper {suffix}"
  evalTactic (← `(tactic| simp only [$[$(names.toArray):ident],*]))

theorem inline_attr : CompilerVirtualFacts.inlineAttribute
    PreparedReflection.actual.compiler.lifecycle.frames.calls.scopes GuardCompilerFacts.runtimeCall.callee =
    .ok none := by decide +kernel

theorem runtime_frame_caller_location : CompilerRuntimeQueries.requiresCallerLocation
    PreparedReflection.actual.compiler.lifecycle.frames.calls.runtime GuardCompilerFacts.runtimeCall.callee =
    .ok false := by with_unfolding_all rfl

def definitionQuery := PreparedReflection.actual.compiler.lifecycle.frames.calls.calls.program.compilerTables.definitions[
  GuardCompilerFacts.runtimeCall.callee.defId]?
theorem definition_supported : definitionQuery.isSome = true := by decide +kernel
def definition := definitionQuery.get (by simpa using definition_supported)
theorem definition_eq : definitionQuery = some definition := Option.eq_some_of_isSome definition_supported

def rank (crates : Array Nat) : UInt8 :=
  if definition.crateIndex == PreparedReflection.actual.compiler.lifecycle.frames.localCrate then 255
  else if crates.contains definition.crateIndex then 255 else 1

theorem runtime_user_relevance {K User Extra : Type} (crates : Array Nat)
    (frame : Frame Provenance LocalLayout Extra) (state : MachineHooks.State K User)
    (callee : frame.functionInstance = GuardCompilerFacts.runtimeCall.callee) :
    FrameMetadata.userRelevance
      (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates)
      frame state = .ok (rank crates) state := by
  unfold FrameMetadata.userRelevance
  rw [callee]
  simp only [CompilerFrameMetadata.hooks]
  rw [inline_attr]
  unfold_frame_meta_runtime
  rw [runtime_frame_caller_location]
  rw [show PreparedReflection.actual.compiler.lifecycle.frames.calls.calls.program.compilerTables.definitions[
      GuardCompilerFacts.runtimeCall.callee.defId]? = some definition from definition_eq]
  simp [rank, bind, EStateM.bind, pure, EStateM.pure, Except.pure]
  split <;> simp_all [bind, EStateM.bind, pure, EStateM.pure]
  split <;> rfl

def rawFrame (crates : Array Nat) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  let frame : Frame Provenance LocalLayout Unit := Frame.create
    CopyPreconditions.Bodies.languageRuntime.loaded GuardCompilerFacts.runtimeCall.callee ()
    (.goto (some 1) .Continue) destination GuardCompilerFacts.runtimePreamble identity
  { body := frame.body, bodyIdentity := frame.bodyIdentity, functionInstance := frame.functionInstance
    extra := {borrowTracker := machine.borrowTracker.map (fun _ => {}), catchUnwind := none, userRelevance := rank crates, dataRace := machine.dataRace.map (fun _ => {})}
    returnContinuation := frame.returnContinuation, returnPlace := frame.returnPlace
    localsIdentity := frame.localsIdentity, locals := frame.locals, vaList := frame.vaList
    trackCallerArg := frame.trackCallerArg, location := frame.location }

theorem init_frame (crates : Array Nat)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    MachineHooks.initFrame (FrameMetadata.userRelevance
      (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates))
      (Frame.create CopyPreconditions.Bodies.languageRuntime.loaded GuardCompilerFacts.runtimeCall.callee ()
        (.goto (some 1) .Continue) destination GuardCompilerFacts.runtimePreamble identity) state =
      .ok (rawFrame crates state.machine destination identity) state := by
  unfold MachineHooks.initFrame
  have relevance := runtime_user_relevance crates
    (Frame.create CopyPreconditions.Bodies.languageRuntime.loaded GuardCompilerFacts.runtimeCall.callee ()
      (.goto (some 1) .Continue) destination GuardCompilerFacts.runtimePreamble identity :
      Frame Provenance LocalLayout Unit) state rfl
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure] at relevance ⊢
  rw [relevance]
  rfl

def pushed (crates : Array Nat) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) :=
  let fresh := CallEntryFacts.freshRoot state.machine
  Storage.withCurrent state.stack.frames (rawFrame crates fresh.1 destination fresh.2) fresh.1

def completed (crates : Array Nat) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  let fresh := CallEntryFacts.freshRoot state.machine
  let frame := rawFrame crates fresh.1 destination fresh.2
  Storage.withCurrent state.stack.frames frame
    (GenericPushRelevance.afterPush fresh.1 state.stack.frames.size frame.extra.userRelevance current.extra.userRelevance)

theorem actual_required_constants
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity)
    (callee : frame.functionInstance = GuardCompilerFacts.runtimeCall.callee) :
    CompilerLifecycle.requiredConstants PreparedReflection.actual.compiler.lifecycle.lifecycle
      CopyPreconditions.Bodies.languageRuntime.loaded (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore frame machine) := by
  have callee' : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance :=
    callee.trans GuardCompilerFacts.runtime_callee
  exact GuardCompilerFacts.runtime_required_constants framesBefore frame machine identity callee'

theorem actual_push_raw
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : state.machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (pushed options.userRelevantCrates state destination).stack
      thread.topUserRelevantFrame = some index)
    (present : (pushed options.userRelevantCrates state destination).stack.frames[index]? = some current) :
    CallMachine.pushRaw (PreparedContracts.actualConfig options () remaining span).lifecycle false
      GuardCompilerFacts.runtimeCall.callee CopyPreconditions.Bodies.languageRuntime.loaded
      destination (.goto (some 1) .Continue) state =
      .ok () (completed options.userRelevantCrates state destination current) := by
  unfold CallMachine.pushRaw
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  rw [fields.freshLocalsIdentity, fields.preambleSpan, fields.frameCompiler, fields.requiredConstants]
  simp only [Bool.false_and, Bool.false_eq_true, ite_false,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [GuardCompilerFacts.runtime_preamble]
  simp only [pure, EStateM.pure]
  rw [init_frame]
  simp only [bind, EStateM.bind]
  let fresh := CallEntryFacts.freshRoot state.machine
  have checks := actual_required_constants state.stack.frames
    (rawFrame options.userRelevantCrates fresh.1 destination fresh.2) fresh.1 rfl rfl
  dsimp only [fresh, CallEntryFacts.freshRoot, Storage.withCurrent] at checks
  rw [checks]
  have freshActive : fresh.1.threads.activeThread? = some thread := active
  simpa only [completed, pushed, fresh, CallEntryFacts.freshRoot, Storage.withCurrent] using
    GenericPushRelevance.after_push state.stack.frames
      (rawFrame options.userRelevantCrates fresh.1 destination fresh.2)
      current fresh.1 thread index freshActive top present

end
end DuplicatePrefix.RuntimeZeroEntryFacts

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RuntimeZeroEntryFacts.actual_push_raw) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved runtime zero entry dependency {dependency}"
