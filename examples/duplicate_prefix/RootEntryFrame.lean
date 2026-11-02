import duplicate_prefix.CallEntryFacts

namespace DuplicatePrefix.RootEntryFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem raw_locals (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    (CallEntryFacts.rawRootFrame machine destination identity).locals =
      Array.replicate 25 (⟨.dead, none⟩ : LocalState Provenance LocalLayout) := by
  with_unfolding_all rfl

theorem raw_body (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    (CallEntryFacts.rawRootFrame machine destination identity).body = RootBody.reflected.body.body ∧
    (CallEntryFacts.rawRootFrame machine destination identity).bodyIdentity = RootBody.reflected.body.identity ∧
    (CallEntryFacts.rawRootFrame machine destination identity).functionInstance = RootBody.reflected.functionInstance := by
  exact ⟨rfl, rfl, rfl⟩

theorem raw_control (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    (CallEntryFacts.rawRootFrame machine destination identity).location = .unwinding ⟨559⟩ ∧
    (CallEntryFacts.rawRootFrame machine destination identity).trackCallerArg = none ∧
    (CallEntryFacts.rawRootFrame machine destination identity).returnContinuation = .stop true ∧
    (CallEntryFacts.rawRootFrame machine destination identity).returnPlace = destination ∧
    (CallEntryFacts.rawRootFrame machine destination identity).localsIdentity = identity := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem raw_no_race (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity)
    (race : machine.dataRace = none) :
    (CallEntryFacts.rawRootFrame machine destination identity).extra.dataRace = none := by
  simp only [CallEntryFacts.rawRootFrame, race, Option.map_none]

theorem raw_borrow (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker) :
    (CallEntryFacts.rawRootFrame machine destination identity).extra.borrowTracker = some {} := by
  simp only [CallEntryFacts.rawRootFrame, tracked, Option.map_some]

end DuplicatePrefix.RootEntryFrame
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RootEntryFrame.raw_locals,
      ``DuplicatePrefix.RootEntryFrame.raw_body, ``DuplicatePrefix.RootEntryFrame.raw_control,
      ``DuplicatePrefix.RootEntryFrame.raw_no_race, ``DuplicatePrefix.RootEntryFrame.raw_borrow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved raw root frame dependency {dependency}"
