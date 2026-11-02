import duplicate_prefix.RootCallCore
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.RootEntryFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
noncomputable def finish (h : RootCallCore.RootHooks) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  RootCallCore.spanAt h ⟨559⟩
  RootCallCore.require (2 == RootCompilerFacts.rootAbi.args.size) "mismatch between callee ABI and callee body arguments"
  if 2 < 2 then throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()
theorem actual_finish (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body) (size : frame.locals.size = 25)
    (dead0 : (frame.locals[0]'(by omega)).value = .dead)
    (dead6 : (frame.locals[6]'(by omega)).value = .dead)
    (dead13 : (frame.locals[13]'(by omega)).value = .dead)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    finish (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame {frame with location := .unwinding ⟨559⟩}) machine) := by
  let next := {frame with location := FrameLocation.unwinding ⟨559⟩}
  have getFrame := CallEntryLocals.get_frame options limits remaining span frames frame machine
  have setFrame := CallEntryLocals.set_frame options limits remaining span frames frame next machine
  have push := CallEntryFacts.actual_call_hooks_push_done options () remaining span limits frames next machine body size dead0 dead6 dead13 dead14 noClocks
  have count : (2 == RootCompilerFacts.rootAbi.args.size) = true := by rw [CallEntryFacts.root_abi_entry_flags.2.2.1]; rfl
  unfold finish RootCallCore.spanAt
  simp only [bind, EStateM.bind]
  rw [getFrame]
  simp only [bind, EStateM.bind]
  dsimp only [next] at setFrame
  rw [setFrame]
  simp only [bind, EStateM.bind, count, RootCallCore.require, Bool.not_true, ite_false, EStateM.pure]
  change (do pure (); (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).pushDone ()) _ = _
  simpa only [pure_bind, next, CallEntryFacts.config] using push
end DuplicatePrefix.RootEntryFinish
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootEntryFinish.actual_finish) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved root entry finish dependency {dependency}"
