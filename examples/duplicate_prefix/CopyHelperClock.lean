import duplicate_prefix.PtrMetadataReturn
namespace DuplicatePrefix.CopyHelperClock
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

noncomputable abbrev advance (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  PtrMetadataReturn.accountedMachine options remaining span machine

theorem addresses (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (advance options remaining span machine).user.addresses = machine.user.addresses := by
  unfold advance PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

theorem runtime (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (advance options remaining span machine).user.payload.payload.user.runtime = machine.user.payload.payload.user.runtime := by
  unfold advance PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

theorem backend (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (advance options remaining span machine).user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
  unfold advance PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

theorem control (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    config.terminators.getControl (advance options remaining span machine).user =
      TerminatorClock.advance (config.terminators.getControl machine.user) := by
  exact CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _

open Lean Elab Command in
run_cmd do
  for declaration in [``addresses, ``runtime, ``backend, ``control] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperClock
