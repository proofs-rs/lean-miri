import duplicate_prefix.AddCallStep
namespace DuplicatePrefix.AddPushPreserves
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable def post (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  (CallEntryFacts.freshRoot (AddCallStep.accountedMachine options remaining span machine)).1
 theorem fields (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (post options remaining span machine).memory = machine.memory ∧
    (post options remaining span machine).borrowTracker = machine.borrowTracker ∧
    (post options remaining span machine).threads = machine.threads ∧
    (post options remaining span machine).dataRace = machine.dataRace ∧
    (post options remaining span machine).user.addresses = machine.user.addresses ∧
    (post options remaining span machine).user.payload.ghost = machine.user.payload.ghost ∧
    (post options remaining span machine).user.payload.validation = machine.user.payload.validation ∧
    (post options remaining span machine).user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
    (post options remaining span machine).user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
    (post options remaining span machine).user.payload.payload.user.types = machine.user.payload.payload.user.types := by
  unfold post CallEntryFacts.freshRoot AddCallStep.accountedMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  repeat' constructor
 theorem control (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (post options remaining span machine).user =
      TerminatorClock.advance ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user) := by
  unfold post CallEntryFacts.freshRoot AddCallStep.accountedMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl
end DuplicatePrefix.AddPushPreserves
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AddPushPreserves.fields,``DuplicatePrefix.AddPushPreserves.control] do
    for dependency in (← collectAxioms name) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved add push preservation dependency {dependency}"
