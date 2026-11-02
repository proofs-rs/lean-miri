import duplicate_prefix.GeneralBorrowRawAsMutEntry
import duplicate_prefix.AsMutPtrFacts
namespace DuplicatePrefix.GeneralBorrowRawAsMutShape
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem locals (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value adjusted : Immediate Provenance) (id : AllocId) (tag : BorTag) :
    (GeneralBorrowRawAsMutEntry.initialized options state destination value adjusted id tag).locals =
      #[⟨.live (.immediate .uninit),none⟩,⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩,
        ⟨.dead,none⟩,⟨.dead,none⟩,⟨.dead,none⟩] := by
  simp only [GeneralBorrowRawAsMutEntry.initialized,AsMutDone.doneFrame,CallEntryFacts.liveSlot,
    GeneralBorrowRawAsMutInstall.resultFrame,GeneralBorrowRawAsMutInstall.cacheFrame,GeneralBorrowRawAsMutInstall.spanFrame,
    LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,GeneralBorrowRawFnEntryArgument.copiedFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
    GeneralBorrowRawAsMutEntry.rawFrame,AsMutFrame.rawFrame,Frame.create,AsMutPtrFacts.body_locals]
  rfl

theorem fixed (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value adjusted : Immediate Provenance) (id : AllocId) (tag : BorTag) :
    let frame := GeneralBorrowRawAsMutEntry.initialized options state destination value adjusted id tag
    frame.body = HelperCompilerFacts.asMutPtrBody.body ∧
    frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity ∧
    frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee ∧
    frame.location = .mir ⟨0,0⟩ ∧
    frame.returnPlace = destination ∧ frame.returnContinuation = .goto (some 7) .Continue ∧
    frame.vaList = #[] ∧ frame.extra.borrowTracker = some (({} : FrameState).addProtector id tag) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

open Lean Elab Command in
run_cmd do
  for declaration in [``locals,``fixed] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved initialized asmut frame dependency {dependency}"
end
end DuplicatePrefix.GeneralBorrowRawAsMutShape
