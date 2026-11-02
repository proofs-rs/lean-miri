import duplicate_prefix.AddCallFacts
import duplicate_prefix.MetadataEntryFacts
namespace DuplicatePrefix.AddEntryFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
private def checkedOk {Error Value : Type} :
    (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
theorem add_preamble_supported : (GuardCompilerFacts.preambleQuery HelperCompilerFacts.addBody).isOk = true := by decide +kernel

noncomputable def addPreamble := checkedOk (GuardCompilerFacts.preambleQuery HelperCompilerFacts.addBody) add_preamble_supported

theorem add_preamble : CompilerLifecycle.preambleSpan
    PreparedReflection.actual.compiler.lifecycle.lifecycle HelperCompilerFacts.addBody =
      (pure addPreamble : MachineHooks.M MiriMemoryKind Machine.RootUser MIR.SpanRef) := by
  with_unfolding_all rfl


theorem add_required_constants
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerLifecycle.requiredConstants PreparedReflection.actual.compiler.lifecycle.lifecycle
      HelperCompilerFacts.addBody (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore frame machine) := by
  with_unfolding_all change ((do
    let frame ← MachineHooks.currentFrame
    unless frame.bodyIdentity == HelperCompilerFacts.addBody.identity &&
      frame.functionInstance == HelperCompilerFacts.addCall.callee do
      throw (StepError.invalidProgram "required-constant current frame identity/instance mismatch")
    pure () : MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
      (Storage.withCurrent framesBefore frame machine)) = _
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure, identity, callee]
  with_unfolding_all rfl


theorem always_live : CallMachine.alwaysLiveVarsAndTemps HelperCompilerFacts.addBody.body = .ok #[] := by with_unfolding_all rfl

theorem return_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget HelperCompilerFacts.addAbi.ret HelperCompilerFacts.addAbi.ret state = .ok true state := by
  with_unfolding_all rfl

theorem argument_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget
      (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret)
      (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret) state = .ok true state := by
  with_unfolding_all rfl
theorem inline_attr : CompilerVirtualFacts.inlineAttribute
    PreparedReflection.actual.compiler.lifecycle.frames.calls.scopes HelperCompilerFacts.addCall.callee = .ok none := by decide +kernel

theorem argument1_compat {State : Type} (queries : LayoutCompat.Queries MIR.TyId State)
    (budget : Nat) (state : State) :
    LayoutCompat.checkArgumentCompat queries budget
      (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret)
      (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret) state = .ok true state := by
  with_unfolding_all rfl

end
end DuplicatePrefix.AddEntryFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.AddEntryFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata entry dependency {dependency}"
