import duplicate_prefix.MetadataEntry
namespace DuplicatePrefix.MetadataEntryShape
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open MetadataEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

theorem raw_locals (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) :
    (rawFrame options state destination).locals = Array.replicate 3 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
  with_unfolding_all rfl

theorem locals (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance) :
    (initialized options state destination value).locals =
      #[⟨.live (.immediate .uninit),none⟩,⟨.live (.immediate value),some PtrMetadataHelper.rawLayout⟩,⟨.dead,none⟩] := by
  with_unfolding_all rfl

theorem control (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance) :
    (initialized options state destination value).body = PtrMetadataHelper.body.body ∧
    (initialized options state destination value).bodyIdentity = PtrMetadataHelper.body.identity ∧
    (initialized options state destination value).functionInstance = PtrMetadataHelper.resolved.callee ∧
    (initialized options state destination value).location = .mir ⟨0,0⟩ ∧
    (initialized options state destination value).returnPlace = destination ∧
    (initialized options state destination value).returnContinuation = .goto (some 1) .Continue ∧
    (initialized options state destination value).vaList = #[] := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem no_clocks (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
    (race : state.machine.dataRace = none) :
    (initialized options state destination value).extra.dataRace = none := by
  simp [initialized,MetadataDone.doneFrame,CallEntryFacts.liveSlot,
    MetadataInstall.resultFrame,RootArgumentEntry.liveFrame,MetadataInstall.cacheFrame,
    MetadataInstall.spanFrame,LocalOperands.cachedLayoutFrame,rawFrame,MetadataFrame.rawFrame,
    MetadataPush.fresh,CallEntryFacts.freshRoot,race]

theorem borrow (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
    (tracker : MachineHooks.BorrowState) (tracked : state.machine.borrowTracker = some tracker) :
    (initialized options state destination value).extra.borrowTracker = some {} := by
  simp [initialized,MetadataDone.doneFrame,CallEntryFacts.liveSlot,
    MetadataInstall.resultFrame,RootArgumentEntry.liveFrame,MetadataInstall.cacheFrame,
    MetadataInstall.spanFrame,LocalOperands.cachedLayoutFrame,rawFrame,MetadataFrame.rawFrame,
    MetadataPush.fresh,CallEntryFacts.freshRoot,tracked]
end
end DuplicatePrefix.MetadataEntryShape
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.MetadataEntryShape.locals, ``DuplicatePrefix.MetadataEntryShape.control, ``DuplicatePrefix.MetadataEntryShape.no_clocks, ``DuplicatePrefix.MetadataEntryShape.borrow] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata entry shape dependency {dependency}"
