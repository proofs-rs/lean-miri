import duplicate_prefix.LenEntry
namespace DuplicatePrefix.LenEntryShape
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def initialized (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
    (held : Bool) (id : AllocId) (tag : BorTag) :=
  let frame := LenEntry.rawFrame options state destination
  let valid : 1 < frame.locals.size := by rw [LenEntry.raw_size];decide
  let initialized := LenInstall.resultFrame frame valid value
  let loanFrame := if held then TypedBorrowSteps.registeredFrame initialized {} id tag else initialized
  LenDone.doneFrame {loanFrame with location := .unwinding LenEntryFacts.lenPreamble}

theorem locals (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
    (held : Bool) (id : AllocId) (tag : BorTag) :
    (initialized options state destination value held id tag).locals =
      #[⟨.live (.immediate .uninit),none⟩,⟨.live (.immediate value),some SharedReferenceMetadata.sharedLayout⟩,⟨.dead,none⟩] := by
  cases held <;> with_unfolding_all rfl

theorem control (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
    (held : Bool) (id : AllocId) (tag : BorTag) :
    let frame := initialized options state destination value held id tag
    frame.body = LenHelper.body.body ∧ frame.bodyIdentity = LenHelper.body.identity ∧
    frame.functionInstance = LenHelper.resolved.callee ∧ frame.location = .mir ⟨0,0⟩ ∧
    frame.returnPlace = destination ∧ frame.returnContinuation = .goto (some 3) .Continue ∧ frame.vaList = #[] := by
  cases held <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem no_clocks (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
    (held : Bool) (id : AllocId) (tag : BorTag) (race : state.machine.dataRace = none) :
    (initialized options state destination value held id tag).extra.dataRace = none := by
  cases held <;>
    simp [initialized,LenDone.doneFrame,CallEntryFacts.liveSlot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      LenInstall.resultFrame,RootArgumentEntry.liveFrame,LenInstall.cacheFrame,LenInstall.spanFrame,
      LocalOperands.cachedLayoutFrame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,race]

theorem borrow (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
    (held : Bool) (id : AllocId) (tag : BorTag)
    (tracker : MachineHooks.BorrowState) (tracked : state.machine.borrowTracker = some tracker) :
    (initialized options state destination value held id tag).extra.borrowTracker =
      some (if held then ({} : FrameState).addProtector id tag else {}) := by
  cases held <;>
    simp [initialized,LenDone.doneFrame,CallEntryFacts.liveSlot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      LenInstall.resultFrame,RootArgumentEntry.liveFrame,LenInstall.cacheFrame,LenInstall.spanFrame,
      LocalOperands.cachedLayoutFrame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,tracked]
end
end DuplicatePrefix.LenEntryShape
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.LenEntryShape.locals, ``DuplicatePrefix.LenEntryShape.control,
      ``DuplicatePrefix.LenEntryShape.no_clocks, ``DuplicatePrefix.LenEntryShape.borrow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved len entry shape {dependency}"
