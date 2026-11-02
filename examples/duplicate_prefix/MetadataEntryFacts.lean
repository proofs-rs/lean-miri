import duplicate_prefix.MetadataCallFacts
namespace DuplicatePrefix.MetadataEntryFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
private def checkedOk {Error Value : Type} :
    (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
theorem metadata_preamble_supported : (GuardCompilerFacts.preambleQuery PtrMetadataHelper.body).isOk = true := by decide +kernel

def metadataPreamble := checkedOk (GuardCompilerFacts.preambleQuery PtrMetadataHelper.body) metadata_preamble_supported

theorem metadata_preamble : CompilerLifecycle.preambleSpan
    PreparedReflection.actual.compiler.lifecycle.lifecycle PtrMetadataHelper.body =
      (pure metadataPreamble : MachineHooks.M MiriMemoryKind Machine.RootUser MIR.SpanRef) := by
  with_unfolding_all rfl


theorem metadata_required_constants
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    CompilerLifecycle.requiredConstants PreparedReflection.actual.compiler.lifecycle.lifecycle
      PtrMetadataHelper.body (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore frame machine) := by
  with_unfolding_all change ((do
    let frame ← MachineHooks.currentFrame
    unless frame.bodyIdentity == PtrMetadataHelper.body.identity &&
      frame.functionInstance == PtrMetadataHelper.resolved.callee do
      throw (StepError.invalidProgram "required-constant current frame identity/instance mismatch")
    pure () : MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
      (Storage.withCurrent framesBefore frame machine)) = _
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure, identity, callee]
  with_unfolding_all rfl


theorem always_live : CallMachine.alwaysLiveVarsAndTemps PtrMetadataHelper.body.body = .ok #[] := by with_unfolding_all rfl

theorem return_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget PtrMetadataHelper.abi.ret PtrMetadataHelper.abi.ret state = .ok true state := by
  with_unfolding_all rfl

theorem argument_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget
      (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret)
      (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret) state = .ok true state := by
  with_unfolding_all rfl
open Lean Elab Tactic in
elab "unfold_frame_meta" : tactic => do
  let env ← getEnv
  let names ← ([".CompilerFrameMetadata.lift", ".CompilerFrameMetadata.definitionCrate"] : List String).mapM fun (suffix : String) => do
    let names := env.constants.toList.filterMap fun (name, _) => if name.toString.endsWith suffix then some (mkIdent name) else none
    match names with
    | [name] => pure name
    | _ => throwError "expected private frame metadata helper {suffix}"
  evalTactic (← `(tactic| simp only [$[$(names.toArray):ident],*]))
theorem inline_attr : CompilerVirtualFacts.inlineAttribute
    PreparedReflection.actual.compiler.lifecycle.frames.calls.scopes PtrMetadataHelper.resolved.callee = .ok none := by decide +kernel

def definitionQuery := PreparedReflection.actual.compiler.lifecycle.frames.calls.calls.program.compilerTables.definitions[PtrMetadataHelper.resolved.callee.defId]?
theorem definition_supported : definitionQuery.isSome = true := by decide +kernel
def definition := definitionQuery.get (by simpa using definition_supported)
theorem definition_eq : definitionQuery = some definition := Option.eq_some_of_isSome definition_supported

theorem user_relevance {K User Extra : Type} (crates : Array Nat)
    (frame : Frame Provenance LocalLayout Extra) (state : MachineHooks.State K User)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    FrameMetadata.userRelevance
      (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates)
      frame state = .ok (if definition.crateIndex == PreparedReflection.actual.compiler.lifecycle.frames.localCrate then 255 else if crates.contains definition.crateIndex then 255 else 1) state := by
  unfold FrameMetadata.userRelevance
  rw [callee]
  simp only [CompilerFrameMetadata.hooks, inline_attr]
  unfold_frame_meta
  have caller : CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.frames.calls.runtime PtrMetadataHelper.resolved.callee = .ok false := MetadataCallFacts.metadata_caller_location
  rw [caller]
  rw [show PreparedReflection.actual.compiler.lifecycle.frames.calls.calls.program.compilerTables.definitions[PtrMetadataHelper.resolved.callee.defId]? = some definition from definition_eq]
  simp [bind, EStateM.bind, pure, EStateM.pure, Except.pure]
  split <;> simp_all [bind, EStateM.bind, pure, EStateM.pure]
  split <;> rfl
end
end DuplicatePrefix.MetadataEntryFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.MetadataEntryFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata entry dependency {dependency}"
