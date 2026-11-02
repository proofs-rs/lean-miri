import duplicate_prefix.RootZeroCompleteState

namespace DuplicatePrefix.S02SeparateDestinationTickLedger
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
noncomputable section

/-- The pure nonzero-count prefix performs one accounting tick. It preserves
the physical borrow and metadata ledger used by the following shared Ref. -/
theorem preserved
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let post := RootZeroCompleteState.tick options remaining span machine
    post.memory = machine.memory ∧ post.borrowTracker = machine.borrowTracker ∧
    post.dataRace = machine.dataRace ∧ post.threads = machine.threads ∧
    post.user.addresses = machine.user.addresses ∧
    post.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
    post.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
    post.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  dsimp only
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.S02SeparateDestinationTickLedger

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationTickLedger.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved positive tick ledger dependency {dependency}"
