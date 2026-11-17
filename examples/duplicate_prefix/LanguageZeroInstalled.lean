import duplicate_prefix.LanguageZeroEntry
namespace DuplicatePrefix.LanguageZeroInstalled
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory
open DuplicatePrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
noncomputable def frame (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (dest : RuntimeStackPlace Provenance) :=
  LanguageZeroDone.doneFrame (LanguageZeroEntry.rawFrame options state dest)
theorem locals_size (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (dest : RuntimeStackPlace Provenance) : (frame options state dest).locals.size = 3 := by
  with_unfolding_all rfl
theorem slots (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (dest : RuntimeStackPlace Provenance) :
    ((frame options state dest).locals[0]?.map (·.value)) = some (.live (.immediate .uninit)) ∧
    ((frame options state dest).locals[0]?.map (·.layout)) = some none ∧
    ((frame options state dest).locals[1]?.map (·.value)) = some .dead ∧
    ((frame options state dest).locals[1]?.map (·.layout)) = some none ∧
    ((frame options state dest).locals[2]?.map (·.value)) = some .dead ∧
    ((frame options state dest).locals[2]?.map (·.layout)) = some none := by
  with_unfolding_all exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
theorem metadata (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (dest : RuntimeStackPlace Provenance) :
    (frame options state dest).body = CopyPreconditions.Bodies.checkLanguage.loaded.body ∧
    (frame options state dest).bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity ∧
    (frame options state dest).functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance ∧
    (frame options state dest).location = .mir ⟨0,0⟩ ∧
    (frame options state dest).trackCallerArg = none ∧
    (frame options state dest).returnContinuation = .goto (some 1) .Continue ∧
    (frame options state dest).vaList = #[] := by
  with_unfolding_all exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end DuplicatePrefix.LanguageZeroInstalled
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.LanguageZeroInstalled.locals_size, ``DuplicatePrefix.LanguageZeroInstalled.slots, ``DuplicatePrefix.LanguageZeroInstalled.metadata] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved installed guard metadata dependency {dependency}"
