import duplicate_prefix.GeneralBorrowRawRootEntryResources
import duplicate_prefix.GeneralBorrowRawFnEntryScope
import duplicate_prefix.ReturnProtection
import duplicate_prefix.CanonicalCopy
import duplicate_prefix.StackPopRelease
namespace DuplicatePrefix.GeneralBorrowRawRootInstalledBuffer
open Miri Miri.Input Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The exact ROOT initializer's return-slot retag and uninitialized slot write
leave the buffer argument's newly constructed allocation installed. -/
theorem installed
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer slot : AllocId) (entry slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parent : BorTag) (offset len : UInt64) (borrowFrame : FrameState)
    (separate : slot ≠ buffer)
    (slotRoom : (TypedRetagGeneric.protectedGlobal tracker.global room).nextPointerTag.value < 18446744073709551615)
    (slotTree : BorrowTree) (updated : Allocation Provenance BorrowTree) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree entry.allocation.extra tracker parent offset len
    let arguments := GeneralBorrowRawFnEntryScope.resultMachine machine tracker room buffer entry parent offset len
    let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global room,tracker.retagMode⟩
    let borrowed := ReturnProtection.borrowedState frames frame borrowFrame arguments next slotRoom slot slotEntry slotTree
    let actual := CanonicalCopy.replaceAllocation borrowed slot slotEntry.kind updated
    actual.machine.memory.live.find? (fun row => row.1 == buffer) =
      some (buffer,{entry with allocation := entry.allocation.setExtra finalTree}) ∧
    actual.machine.borrowTracker = some ⟨TypedRetagGeneric.protectedGlobal next.global slotRoom,tracker.retagMode⟩ := by
  dsimp only
  constructor
  · let finalTree := GeneralBorrowRawFnEntryArgument.finalTree entry.allocation.extra tracker parent offset len
    let arguments := GeneralBorrowRawFnEntryScope.resultMachine machine tracker room buffer entry parent offset len
    let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global room,tracker.retagMode⟩
    let borrowed := ReturnProtection.borrowedState frames frame borrowFrame arguments next slotRoom slot slotEntry slotTree
    have first := StackPopRelease.lookup_commit_same machine.memory buffer entry finalTree
    have second := StackPopRelease.lookup_commit_other
      (StackPopRelease.commitTree machine.memory buffer entry finalTree) slot buffer slotEntry
      {entry with allocation := entry.allocation.setExtra finalTree} slotTree separate.symm first
    change borrowed.machine.memory.live.find? (fun row => row.1 == buffer) = _ at second
    have final := StackPopRelease.lookup_commit_other borrowed.machine.memory slot buffer
      (⟨slotEntry.kind,updated⟩ : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      {entry with allocation := entry.allocation.setExtra finalTree} updated.extra separate.symm second
    have same : updated.setExtra updated.extra = updated := by cases updated;rfl
    simpa only [StackPopRelease.commitTree,same,CanonicalCopy.replaceAllocation] using final
  · rfl
end DuplicatePrefix.GeneralBorrowRawRootInstalledBuffer
