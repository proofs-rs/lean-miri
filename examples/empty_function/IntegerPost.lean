import empty_function.CanonicalInit
import empty_function.TerminatorStep
import empty_function.FrameExit
import empty_function.ReturnContinuation
import empty_function.IntegerThreads
namespace EmptyFunction.IntegerPost
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def machine (s : Static) (p : Packet) (frame previous : LocalUnit.F)
    (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat) :=
  FrameExit.afterRelevanceAt p.before.stack.frames frame
    (TerminatorStep.after (LocalUnit.current p.before.stack.frames frame
      (CanonicalInit.initializedMachine s p frame previous tracker room))).machine index

theorem memory_eq (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat) :
    (machine s p frame previous tracker room index).memory = p.before.machine.memory := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold machine FrameExit.afterRelevanceAt FrameExit.afterRelevance
    TerminatorStep.after CanonicalInit.initializedMachine UnitRetag.allocatedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split <;> split <;> rfl

theorem addresses_eq (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat) :
    (machine s p frame previous tracker room index).user.addresses = p.before.machine.user.addresses := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold machine FrameExit.afterRelevanceAt FrameExit.afterRelevance
    TerminatorStep.after CanonicalInit.initializedMachine UnitRetag.allocatedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split <;> split <;> rfl

theorem tracker_eq (s : Static) (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat) :
    (machine s p frame previous tracker room index).borrowTracker = some (UnitRetag.allocatedTracker tracker room) := by
  unfold machine FrameExit.afterRelevanceAt FrameExit.afterRelevance
    TerminatorStep.after CanonicalInit.initializedMachine UnitRetag.allocatedMachine
  split <;> rfl

 theorem runtime_eq (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat) :
    Preservation.RuntimeContext p.before (⟨p.before.stack,machine s p frame previous tracker room index⟩ : State) := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold Preservation.RuntimeContext machine FrameExit.afterRelevanceAt FrameExit.afterRelevance
    TerminatorStep.after TerminatorStep.setControl TerminatorStep.advanced
    CanonicalInit.initializedMachine UnitRetag.allocatedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split <;> split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

 theorem protectors (s : Static) (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat)
    (enabled : p.before.machine.borrowTracker = some tracker) :
    Preservation.ExistingProtectors p.before (⟨p.before.stack,machine s p frame previous tracker room index⟩ : State) := by
  intro old found
  have same : old = tracker := Option.some.inj (found.symm.trans enabled)
  subst old
  exact ⟨UnitRetag.allocatedTracker tracker room,tracker_eq s p frame previous tracker room index,rfl⟩

 theorem roots (s : Static) (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat)
    (enabled : p.before.machine.borrowTracker = some tracker) :
    Preservation.ExistingRoots p.before (⟨p.before.stack,machine s p frame previous tracker room index⟩ : State) := by
  intro old found
  have same : old = tracker := Option.some.inj (found.symm.trans enabled)
  subst old
  refine ⟨UnitRetag.allocatedTracker tracker room,tracker_eq s p frame previous tracker room index,?_⟩
  intro id tag found
  exact found

private theorem old_rights_refl (tree : BorrowTree) : Preservation.OldNodeRights tree tree := by
  refine ⟨?_,?_,?_⟩
  · intro tag index found; exact found
  · intro root member; exact member
  · intro index old found
    refine ⟨old,found,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · intro child member; exact member
    · intro byte segment member contains
      exact ⟨segment,member,contains,rfl,rfl⟩

 theorem preserves (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat)
    (older : Array LocalUnit.F) (caller : LocalUnit.F)
    (original : p.before.stack.frames = older.push caller)
    (enabled : p.before.machine.borrowTracker = some tracker)
    (place : MPlaceTy Provenance) (destination : p.destination = .memory place) :
    Preservation.Preserves s p (ReturnContinuation.resume older caller
      (machine s p frame previous tracker room index) p.returnBlock) := by
  let finish := ReturnContinuation.resume older caller (machine s p frame previous tracker room index) p.returnBlock
  have threads := IntegerThreads.projections s metadata capacity p frame previous tracker room index finish rfl
  refine ⟨?_,?_,protectors s p frame previous tracker room index enabled,threads.1,?_,?_,?_,threads.2,?_,
    runtime_eq s metadata capacity p frame previous tracker room index,
    roots s p frame previous tracker room index enabled⟩
  · simp [Returned,ReturnContinuation.resume,original,Stack.currentFrame?]
  · intro id old found
    refine ⟨old,?_,rfl,rfl,old_rights_refl _⟩
    change (machine s p frame previous tracker room index).memory.live.find? (fun row => row.1 == id) = _
    rw [memory_eq s metadata capacity]
    exact found
  · intro old current oldEq currentEq
    simp only [Stack.currentFrame?,original,ReturnContinuation.resume,Array.back?_push,Option.some.injEq] at oldEq currentEq
    subst old
    subst current
    exact ⟨rfl,by intro slot permitted; rfl⟩
  · simp [Preservation.SelectedProjectedContents,destination]
  · intro old current oldEq currentEq
    simp only [Stack.currentFrame?,original,ReturnContinuation.resume,Array.back?_push,Option.some.injEq] at oldEq currentEq
    subst old
    subst current
    rfl
  · unfold Preservation.ExistingAddressFacts
    simp only [ReturnContinuation.resume,addresses_eq s metadata capacity]
    refine ⟨True.intro,True.intro,?_,?_,?_⟩
    · intro id row found; exact found
    · intro row member; exact ⟨row,member,rfl,rfl⟩
    · intro id member; exact Array.contains_iff_mem.mpr member
end EmptyFunction.IntegerPost
