import duplicate_prefix.RootZeroInvocationEntry
import duplicate_prefix.RootZeroComplete
import duplicate_prefix.PushThread
import duplicate_prefix.ProtectedTagsFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace DuplicatePrefix.RootZeroInvocationState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open TypedBorrowSteps ReferenceBorrowDriver PhysicalMachineWrite
abbrev next (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615) := allocatedTracker tracker fresh
abbrev child (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615) := (next tracker fresh).global.nextPointerTag
abbrev held (tracker : MachineHooks.BorrowState) (fresh1 : tracker.global.nextPointerTag.value<18446744073709551615)
    (fresh2 : (child tracker fresh1).value<18446744073709551615) :=
  registeredTracker (allocatedTracker (next tracker fresh1) fresh2) (child tracker fresh1)

def enteredMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh1 : tracker.global.nextPointerTag.value<18446744073709551615)
    (fresh2 : (child tracker fresh1).value<18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (root : BorTag)
    (updated : Allocation Provenance BorrowTree) : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  let allocated := allocatedMachine (allocatedMachine machine tracker fresh1) (next tracker fresh1) fresh2
  let registered := registeredMachine allocated (allocatedTracker (next tracker fresh1) fresh2) (child tracker fresh1)
  let memory := RetagEntry.updatedMemory machine.memory id entry (slotTree root (child tracker fresh1) 1 false)
  {registered with memory := {memory with live := (memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push (id,{entry with allocation := updated})}}

theorem entered_eq (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh1 : tracker.global.nextPointerTag.value<18446744073709551615)
    (fresh2 : (child tracker fresh1).value<18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (root : BorTag)
    (updated : Allocation Provenance BorrowTree)
    (frame : CompilerFrameContext.ActualFrame) :
    (CanonicalCopy.replaceAllocation (ReturnProtection.borrowedState #[] frame {} (allocatedMachine machine tracker fresh1)
      (next tracker fresh1) fresh2 id entry (slotTree root (child tracker fresh1) 1 false)) id entry.kind updated).machine =
    enteredMachine machine tracker fresh1 fresh2 id entry root updated := rfl

theorem entered_lookup (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh1 : tracker.global.nextPointerTag.value<18446744073709551615)
    (fresh2 : (child tracker fresh1).value<18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (root : BorTag)
    (updated : Allocation Provenance BorrowTree) :
    (enteredMachine machine tracker fresh1 fresh2 id entry root updated).memory.live.find? (fun row => row.1 == id) =
      some (id,{entry with allocation:=updated}) :=
  MemoryCopyBridge.live_lookup_replaced _ id _

theorem held_root_free (tracker : MachineHooks.BorrowState)
    (fresh1 : tracker.global.nextPointerTag.value<18446744073709551615)
    (fresh2 : (child tracker fresh1).value<18446744073709551615)
    (root : BorTag) (distinct : root≠child tracker fresh1)
    (free : tracker.global.protectedTags.contains root=false) :
    (held tracker fresh1 fresh2).global.protectedTags.contains root=false := by
  change (tracker.global.protectedTags.insert (child tracker fresh1) .StrongProtector).contains root=false
  unfold ProtectedTags.contains
  rw [ProtectedTagsFacts.insert_preserves_other _ root _ _ distinct]
  exact free

theorem held_child (tracker : MachineHooks.BorrowState)
    (fresh1 : tracker.global.nextPointerTag.value<18446744073709551615)
    (fresh2 : (child tracker fresh1).value<18446744073709551615) :
    (held tracker fresh1 fresh2).global.protectedTags.contains (child tracker fresh1)=true := by
  change (tracker.global.protectedTags.insert (child tracker fresh1) .StrongProtector).contains (child tracker fresh1)=true
  simp [ProtectedTags.contains]

theorem tick_fields (options remaining span machine) :
    let after := RootZeroCompleteState.tick options remaining span machine
    after.memory=machine.memory ∧ after.borrowTracker=machine.borrowTracker ∧ after.dataRace=machine.dataRace ∧
    after.threads=machine.threads ∧ after.user.addresses=machine.user.addresses ∧
    after.user.payload.payload.user.backend=machine.user.payload.payload.user.backend ∧
    after.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras := by
  dsimp only
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem raw_control (options remaining span before) :
    let hooks := (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    hooks.getControl (RawRootInvocation.machine #[] before).user = hooks.getControl before.user := by
  dsimp only
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

#print axioms entered_lookup
#print axioms held_root_free
end DuplicatePrefix.RootZeroInvocationState

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RootZeroInvocationState.entered_eq,
      ``DuplicatePrefix.RootZeroInvocationState.entered_lookup, ``DuplicatePrefix.RootZeroInvocationState.held_root_free,
      ``DuplicatePrefix.RootZeroInvocationState.held_child, ``DuplicatePrefix.RootZeroInvocationState.tick_fields,
      ``DuplicatePrefix.RootZeroInvocationState.raw_control] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved root invocation state dependency {dependency}"
