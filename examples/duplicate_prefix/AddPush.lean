import duplicate_prefix.TrackedFrame
import duplicate_prefix.AddEntryFacts
namespace DuplicatePrefix.AddPush
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable def pushed (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) :=
  TrackedFrame.pushed state.stack.frames state.machine HelperCompilerFacts.addCall.callee HelperCompilerFacts.addBody
    AddEntryFacts.addPreamble destination cont
 theorem actual_push (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation)
    (thread : Miri.Concurrency.ThreadRecord) (active : state.machine.threads.activeThread? = some thread)
    (index : Nat) (cached : thread.topUserRelevantFrame = some index)
    (cachedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid : index < state.stack.frames.size) (lookup : state.stack.frames[index]? = some cachedFrame)
    (positive : cachedFrame.extra.userRelevance > 0) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).pushRaw ()
      HelperCompilerFacts.addCall.callee HelperCompilerFacts.addBody destination cont state =
      .ok () (pushed state destination cont) := by
  exact TrackedFrame.push_raw_of_metadata options limits remaining span debug
    HelperCompilerFacts.addCall.callee HelperCompilerFacts.addBody AddEntryFacts.addPreamble
    AddEntryFacts.inline_attr AddCallFacts.add_caller_location AddEntryFacts.add_preamble
    (fun frames frame machine identity callee => AddEntryFacts.add_required_constants frames frame machine identity callee)
    state destination cont thread active index cached cachedFrame valid lookup positive
end DuplicatePrefix.AddPush
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddPush.actual_push) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved add push dependency {dependency}"
