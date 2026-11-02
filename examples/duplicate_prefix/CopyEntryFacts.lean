import duplicate_prefix.CopyCallFacts
import duplicate_prefix.MetadataEntryFacts
namespace DuplicatePrefix.CopyEntryFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
private def checkedOk {Error Value : Type} :
    (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
theorem copy_preamble_supported : (GuardCompilerFacts.preambleQuery HelperCompilerFacts.copyBody).isOk = true := by decide +kernel

noncomputable def copyPreamble := checkedOk (GuardCompilerFacts.preambleQuery HelperCompilerFacts.copyBody) copy_preamble_supported

theorem copy_preamble : CompilerLifecycle.preambleSpan
    PreparedReflection.actual.compiler.lifecycle.lifecycle HelperCompilerFacts.copyBody =
      (pure copyPreamble : MachineHooks.M MiriMemoryKind Machine.RootUser MIR.SpanRef) := by
  with_unfolding_all rfl


theorem copy_required_constants
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerLifecycle.requiredConstants PreparedReflection.actual.compiler.lifecycle.lifecycle
      HelperCompilerFacts.copyBody (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore frame machine) := by
  with_unfolding_all change ((do
    let frame ← MachineHooks.currentFrame
    unless frame.bodyIdentity == HelperCompilerFacts.copyBody.identity &&
      frame.functionInstance == HelperCompilerFacts.copyCall.callee do
      throw (StepError.invalidProgram "required-constant current frame identity/instance mismatch")
    pure () : MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
      (Storage.withCurrent framesBefore frame machine)) = _
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure, identity, callee]
  with_unfolding_all rfl


theorem always_live : CallMachine.alwaysLiveVarsAndTemps HelperCompilerFacts.copyBody.body = .ok #[] := by with_unfolding_all rfl

theorem return_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget HelperCompilerFacts.copyAbi.ret HelperCompilerFacts.copyAbi.ret state = .ok true state := by
  with_unfolding_all rfl

theorem argument_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget
      (HelperCompilerFacts.copyAbi.args.getD 0 HelperCompilerFacts.copyAbi.ret)
      (HelperCompilerFacts.copyAbi.args.getD 0 HelperCompilerFacts.copyAbi.ret) state = .ok true state := by
  with_unfolding_all rfl
theorem inline_attr : CompilerVirtualFacts.inlineAttribute
    PreparedReflection.actual.compiler.lifecycle.frames.calls.scopes HelperCompilerFacts.copyCall.callee = .ok none := by decide +kernel

theorem argument1_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget
      (HelperCompilerFacts.copyAbi.args.getD 1 HelperCompilerFacts.copyAbi.ret)
      (HelperCompilerFacts.copyAbi.args.getD 1 HelperCompilerFacts.copyAbi.ret) state = .ok true state := by
  with_unfolding_all rfl

end
end DuplicatePrefix.CopyEntryFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CopyEntryFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata entry dependency {dependency}"
