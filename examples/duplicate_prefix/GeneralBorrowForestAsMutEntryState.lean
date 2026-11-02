import duplicate_prefix.GeneralBorrowForestAsMutEntry
import duplicate_prefix.PushThread

namespace DuplicatePrefix.GeneralBorrowForestAsMutEntryState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

def tracker (before : MachineHooks.BorrowState)
    (fresh : before.global.nextPointerTag.value < 18446744073709551615) :=
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker before fresh) before.global.nextPointerTag

def machine (pushed : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (before : MachineHooks.BorrowState) (fresh : before.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag) (offset len : UInt64) :=
  {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine pushed before fresh)
    (ReferenceBorrowDriver.allocatedTracker before fresh) before.global.nextPointerTag with
    memory := RetagEntry.updatedMemory pushed.memory id entry
      (GeneralBorrowForestArgumentCopy.finalTree entry.allocation.extra before parentTag offset len)}

/-- Machine fields of the real FnEntry result, with the fresh tag allocated
and registered. Memory changes only by the actual buffer tree replacement. -/
theorem fields (pushed : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (before : MachineHooks.BorrowState) (fresh : before.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag) (offset len : UInt64) :
    let after := machine pushed before fresh id entry parentTag offset len
    after.borrowTracker = some (tracker before fresh) ∧
    (tracker before fresh).retagMode = before.retagMode ∧
    (tracker before fresh).global.protectedTags =
      (TypedBorrowSteps.registeredGlobal before before.global.nextPointerTag).protectedTags ∧
    after.memory = RetagEntry.updatedMemory pushed.memory id entry
      (GeneralBorrowForestArgumentCopy.finalTree entry.allocation.extra before parentTag offset len) ∧
    after.dataRace = pushed.dataRace ∧ after.threads = pushed.threads ∧
    after.user = pushed.user := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The actual raw helper push preserves payload/address/tracker fields and
updates thread relevance exactly as used by the initialized-helper client. -/
theorem push_fields (crates : Array Nat) (caller : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread) :
    let pushed := (AsMutPush.completed crates (Storage.withCurrent #[] caller before) destination caller).machine
    pushed.memory = before.memory ∧ pushed.borrowTracker = before.borrowTracker ∧
    pushed.dataRace = before.dataRace ∧ pushed.user.payload.ghost = before.user.payload.ghost ∧
    pushed.user.payload.validation = before.user.payload.validation ∧
    pushed.user.payload.payload.user = before.user.payload.payload.user ∧
    pushed.user.addresses = before.user.addresses ∧
    pushed.threads.fixedScheduling = before.threads.fixedScheduling ∧
    pushed.threads.activeThread? = some (PushThread.after thread 1 (AsMutFrame.rank crates) caller.extra.userRelevance) := by
  let supplied := (AsMutPush.fresh before).1
  have suppliedActive : supplied.threads.activeThread? = some thread := active
  have threadAfter := PushThread.active_after supplied thread 1 (AsMutFrame.rank crates) caller.extra.userRelevance suppliedActive
  have preserved :
      (GenericPushRelevance.afterPush supplied 1 (AsMutFrame.rank crates) caller.extra.userRelevance).memory = before.memory ∧
      (GenericPushRelevance.afterPush supplied 1 (AsMutFrame.rank crates) caller.extra.userRelevance).borrowTracker = before.borrowTracker ∧
      (GenericPushRelevance.afterPush supplied 1 (AsMutFrame.rank crates) caller.extra.userRelevance).dataRace = before.dataRace ∧
      (GenericPushRelevance.afterPush supplied 1 (AsMutFrame.rank crates) caller.extra.userRelevance).user.payload.ghost = before.user.payload.ghost ∧
      (GenericPushRelevance.afterPush supplied 1 (AsMutFrame.rank crates) caller.extra.userRelevance).user.payload.validation = before.user.payload.validation ∧
      (GenericPushRelevance.afterPush supplied 1 (AsMutFrame.rank crates) caller.extra.userRelevance).user.payload.payload.user = before.user.payload.payload.user ∧
      (GenericPushRelevance.afterPush supplied 1 (AsMutFrame.rank crates) caller.extra.userRelevance).user.addresses = before.user.addresses ∧
      (GenericPushRelevance.afterPush supplied 1 (AsMutFrame.rank crates) caller.extra.userRelevance).threads.fixedScheduling = before.threads.fixedScheduling := by
    unfold GenericPushRelevance.afterPush
    split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  exact ⟨preserved.1,preserved.2.1,preserved.2.2.1,preserved.2.2.2.1,preserved.2.2.2.2.1,
    preserved.2.2.2.2.2.1,preserved.2.2.2.2.2.2.1,preserved.2.2.2.2.2.2.2,threadAfter⟩

end
end DuplicatePrefix.GeneralBorrowForestAsMutEntryState
