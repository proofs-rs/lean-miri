import duplicate_prefix.NonliveEmptyRootInvocationEntry
import duplicate_prefix.PositiveRootInvocationState
import duplicate_prefix.ProtectorInsertion
namespace DuplicatePrefix.NonliveEmptyRootInvocationState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
abbrev next := PositiveRootInvocationState.next
abbrev held := PositiveRootInvocationState.held

def enteredMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  let args := NonliveEmptyRootArgumentScope.resultMachine machine tracker fresh
  let borrowed := {registeredMachine (allocatedMachine args (next tracker fresh) fresh2)
    (allocatedTracker (next tracker fresh) fresh2) (next tracker fresh).global.nextPointerTag with
    memory := RetagEntry.updatedMemory args.memory slot slotEntry (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false)}
  {borrowed with memory := {borrowed.memory with live := (borrowed.memory.live.filter (fun row => row.1 != slot)).push (slot,{slotEntry with allocation := updated})}}

theorem entered_eq (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) :
    (CanonicalCopy.replaceAllocation (ReturnProtection.borrowedState #[] frame borrowFrame
      (NonliveEmptyRootArgumentScope.resultMachine machine tracker fresh)
      (next tracker fresh) fresh2 slot slotEntry (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false))
      slot slotEntry.kind updated).machine =
      enteredMachine machine tracker fresh fresh2 slot slotEntry slotRoot updated := rfl

theorem allocation_info_other (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) (other : AllocId) (separate : other ≠ slot) :
    (enteredMachine machine tracker fresh fresh2 slot slotEntry slotRoot updated).memory.getAllocInfo other =
      machine.memory.getAllocInfo other := by
  change (StackPopRelease.commitTree
    (StackPopRelease.commitTree machine.memory slot slotEntry
      (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false))
    slot {slotEntry with allocation := updated} updated.extra).getAllocInfo other = _
  rw [StackPopRelease.metadata_commit_other _ slot other _ _ separate,
    StackPopRelease.metadata_commit_other _ slot other _ _ separate]


end
end DuplicatePrefix.NonliveEmptyRootInvocationState

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.NonliveEmptyRootInvocationState.entered_eq,``DuplicatePrefix.NonliveEmptyRootInvocationState.allocation_info_other] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved nonlive empty root invocation post-state dependency {dependency}"
