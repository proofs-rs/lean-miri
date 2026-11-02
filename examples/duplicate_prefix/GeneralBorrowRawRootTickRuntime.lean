import duplicate_prefix.GeneralBorrowRawRootToLen
namespace DuplicatePrefix.GeneralBorrowRawRootTickRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial
/-- One actual accounting step preserves the whole physical/runtime ledger. -/
theorem preserves (s : Initial) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (before : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before machine) :
    GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before
      (RootZeroCompleteState.tick s.options s.remaining s.span machine) := by
  let after := RootZeroCompleteState.tick s.options s.remaining s.span machine
  have data : after.dataRace = machine.dataRace ∧ after.threads = machine.threads ∧
      after.user.addresses = machine.user.addresses ∧ after.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
    unfold after RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have flags := RootZeroCompleteState.tick_flags s.options s.remaining s.span machine
  refine ⟨(RootZeroCompleteState.tick_ghost s.options s.remaining s.span machine).trans before.ghost,
    (RootZeroCompleteState.tick_shallow s.options s.remaining s.span machine).trans before.shallow,
    data.1.trans before.race,data.2.2.1.trans before.addresses,data.2.2.2.1.trans before.types,
    data.2.2.2.2.1.trans before.extras,data.2.2.2.2.2.trans before.backend,
    flags.1.trans before.unchecked,flags.2.trans before.noGc,?_,?_⟩
  · change after.threads.fixedScheduling = true
    rw [data.2.1];exact before.fixed
  · obtain ⟨thread,active,top⟩ := before.active
    refine ⟨thread,?_,top⟩
    change after.threads.activeThread? = some thread
    rw [data.2.1];exact active
end
end DuplicatePrefix.GeneralBorrowRawRootTickRuntime
