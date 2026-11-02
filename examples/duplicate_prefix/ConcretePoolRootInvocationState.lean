import duplicate_prefix.ConcretePoolRootInvocationEntry
import duplicate_prefix.PositiveRootInvocationState
import duplicate_prefix.ProtectorInsertion
namespace DuplicatePrefix.ConcretePoolRootInvocationState
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
    (buffer : AllocId) (bufferEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag) (entryInput : ConcreteEmptyPoolEntry.Input bufferEntry.allocation.extra parentTag tracker.global.nextPointerTag)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  let args := ConcretePoolRootArgumentScope.resultMachine machine tracker fresh buffer bufferEntry parentTag entryInput
  let borrowed := {registeredMachine (allocatedMachine args (next tracker fresh) fresh2)
    (allocatedTracker (next tracker fresh) fresh2) (next tracker fresh).global.nextPointerTag with
    memory := RetagEntry.updatedMemory args.memory slot slotEntry (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false)}
  {borrowed with memory := {borrowed.memory with live := (borrowed.memory.live.filter (fun row => row.1 != slot)).push (slot,{slotEntry with allocation := updated})}}

theorem entered_eq (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (bufferEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag) (entryInput : ConcreteEmptyPoolEntry.Input bufferEntry.allocation.extra parentTag tracker.global.nextPointerTag)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) :
    (CanonicalCopy.replaceAllocation (ReturnProtection.borrowedState #[] frame borrowFrame
      (ConcretePoolRootArgumentScope.resultMachine machine tracker fresh buffer bufferEntry parentTag entryInput)
      (next tracker fresh) fresh2 slot slotEntry (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false))
      slot slotEntry.kind updated).machine =
      enteredMachine machine tracker fresh buffer bufferEntry parentTag entryInput fresh2 slot slotEntry slotRoot updated := rfl

theorem buffer_lookup (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (bufferEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parentTag : BorTag) (entryInput : ConcreteEmptyPoolEntry.Input bufferEntry.allocation.extra parentTag tracker.global.nextPointerTag)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) (separate : buffer ≠ slot) :
    (enteredMachine machine tracker fresh buffer bufferEntry parentTag entryInput fresh2 slot slotEntry slotRoot updated).memory.live.find? (fun row => row.1 == buffer) =
      some (buffer,{bufferEntry with allocation := bufferEntry.allocation.setExtra entryInput.after}) := by
  let args := ConcretePoolRootArgumentScope.resultMachine machine tracker fresh buffer bufferEntry parentTag entryInput
  let changed := {bufferEntry with allocation := bufferEntry.allocation.setExtra entryInput.after}
  have present : args.memory.live.find? (fun row => row.1 == buffer) = some (buffer,changed) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory buffer changed
  have first := StackPopRelease.lookup_commit_other args.memory slot buffer slotEntry changed
    (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false) separate present
  have second := StackPopRelease.lookup_commit_other
    (RetagEntry.updatedMemory args.memory slot slotEntry (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false))
    slot buffer {slotEntry with allocation := updated} changed updated.extra separate first
  exact second

end
end DuplicatePrefix.ConcretePoolRootInvocationState

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.ConcretePoolRootInvocationState.entered_eq,``DuplicatePrefix.ConcretePoolRootInvocationState.buffer_lookup] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved concrete empty root invocation post-state dependency {dependency}"
