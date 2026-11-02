import duplicate_prefix.PositiveRootInvocationEntry
import duplicate_prefix.ProtectorInsertion
namespace DuplicatePrefix.PositiveRootInvocationState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
abbrev next (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.BorrowState :=
  ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
abbrev held (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615) :=
  registeredTracker (allocatedTracker (next tracker fresh) fresh2) (next tracker fresh).global.nextPointerTag

def enteredMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (bufferEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (root : BorTag)
    (capacity offset len : UInt64)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  let args := PositiveRootArgumentScope.resultMachine machine tracker fresh buffer bufferEntry root capacity offset len
  let borrowed := {registeredMachine (allocatedMachine args (next tracker fresh) fresh2)
    (allocatedTracker (next tracker fresh) fresh2) (next tracker fresh).global.nextPointerTag with
    memory := RetagEntry.updatedMemory args.memory slot slotEntry (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false)}
  {borrowed with memory := {borrowed.memory with live := (borrowed.memory.live.filter (fun row => row.1 != slot)).push (slot,{slotEntry with allocation := updated})}}

theorem entered_eq (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (bufferEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (root : BorTag)
    (capacity offset len : UInt64)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) :
    (CanonicalCopy.replaceAllocation (ReturnProtection.borrowedState #[] frame borrowFrame
      (PositiveRootArgumentScope.resultMachine machine tracker fresh buffer bufferEntry root capacity offset len)
      (next tracker fresh) fresh2 slot slotEntry (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false))
      slot slotEntry.kind updated).machine =
      enteredMachine machine tracker fresh buffer bufferEntry root capacity offset len fresh2 slot slotEntry slotRoot updated := rfl

theorem buffer_lookup (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (bufferEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (root : BorTag)
    (capacity offset len : UInt64)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) (separate : buffer ≠ slot) :
    (enteredMachine machine tracker fresh buffer bufferEntry root capacity offset len fresh2 slot slotEntry slotRoot updated).memory.live.find? (fun row => row.1 == buffer) =
      some (buffer,{bufferEntry with allocation := bufferEntry.allocation.setExtra (TypedRetagGeneric.childTree root tracker.global.nextPointerTag capacity offset len)}) := by
  let args := PositiveRootArgumentScope.resultMachine machine tracker fresh buffer bufferEntry root capacity offset len
  let changed := {bufferEntry with allocation := bufferEntry.allocation.setExtra (TypedRetagGeneric.childTree root tracker.global.nextPointerTag capacity offset len)}
  have present : args.memory.live.find? (fun row => row.1 == buffer) = some (buffer,changed) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory buffer changed
  have first := StackPopRelease.lookup_commit_other args.memory slot buffer slotEntry changed
    (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false) separate present
  have second := StackPopRelease.lookup_commit_other
    (RetagEntry.updatedMemory args.memory slot slotEntry (PhysicalMachineWrite.slotTree slotRoot (next tracker fresh).global.nextPointerTag 1 false))
    slot buffer {slotEntry with allocation := updated} changed updated.extra separate first
  exact second

theorem buffer_root_free (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (root : BorTag) (different : root ≠ tracker.global.nextPointerTag)
    (different2 : root ≠ (next tracker fresh).global.nextPointerTag)
    (free : tracker.global.protectedTags.contains root = false) :
    (held tracker fresh fresh2).global.protectedTags.contains root = false := by
  change ((tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert
    (next tracker fresh).global.nextPointerTag .StrongProtector).contains root = false
  rw [ProtectorInsertion.contains_other _ _ _ _ different2,ProtectorInsertion.contains_other _ _ _ _ different]
  exact free

theorem buffer_child_held (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615) :
    (held tracker fresh fresh2).global.protectedTags.contains tracker.global.nextPointerTag = true := by
  change ((tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert
    (next tracker fresh).global.nextPointerTag .StrongProtector).contains tracker.global.nextPointerTag = true
  by_cases same : tracker.global.nextPointerTag = (next tracker fresh).global.nextPointerTag
  · rw [same];simp [ProtectedTags.contains]
  · rw [ProtectorInsertion.contains_other _ _ _ _ same];simp [ProtectedTags.contains]
end
end DuplicatePrefix.PositiveRootInvocationState

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.PositiveRootInvocationState.entered_eq,``DuplicatePrefix.PositiveRootInvocationState.buffer_lookup,
      ``DuplicatePrefix.PositiveRootInvocationState.buffer_root_free,``DuplicatePrefix.PositiveRootInvocationState.buffer_child_held] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved positive root invocation post-state dependency {dependency}"
