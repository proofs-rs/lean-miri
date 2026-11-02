import empty_function.LocalIndirectEndpoint
import empty_function.LocalPost
namespace EmptyFunction.LocalIndirectPost
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.WildcardInit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private theorem old_rights_refl (tree : BorrowTree) : Preservation.OldNodeRights tree tree := by
  refine ⟨?_,?_,?_⟩
  · intro tag index found;exact found
  · intro root member;exact member
  · intro index old found
    refine ⟨old,found,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · intro child member;exact member
    · intro byte segment member contains;exact ⟨segment,member,contains,rfl,rfl⟩

def taggedMachine (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :=
  UnitRetag.allocatedMachine (LocalModel.machine s p tracker destination older bound frame previous index) tracker room

theorem finished_eq (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (choice : Case p tracker room) :
    LocalIndirectEndpoint.finishedMachine s p tracker destination older bound frame previous room choice index =
      WildcardEndpoint.released choice (taggedMachine s p tracker destination older bound frame previous index room) := by
  cases choice <;> by_cases popped : index = (older.push (LocalModel.caller s p tracker destination bound)).size
  all_goals
    simp only [LocalIndirectEndpoint.finishedMachine,LocalIndirectEndpoint.initializedMachine,
      taggedMachine,LocalModel.machine,WildcardEndpoint.released,FrameExit.afterRelevanceAt,popped,↓reduceIte]
    simp only [FrameExit.afterRelevance,TerminatorStep.after,UnitRetag.allocatedMachine,LocalUnit.current]
  all_goals rfl

private theorem tagged_preserves (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (original : p.before.stack.frames = older.push destination.caller)
    (whole : destination.offset = none) (enabled : p.before.machine.borrowTracker = some tracker) :
    Preservation.Preserves s p (ReturnContinuation.resume older (LocalModel.caller s p tracker destination bound)
      (taggedMachine s p tracker destination older bound frame previous index room) p.returnBlock) := by
  obtain ⟨returned,allocations,protectors,threads,slots,selected,context,threadContext,addresses,runtime,roots⟩ :=
    LocalPost.preserves s metadata capacity p tracker destination older bound frame previous index original whole
  refine ⟨returned,allocations,?_,threads,slots,selected,context,threadContext,addresses,runtime,?_⟩
  · intro old wasEnabled
    have same : old = tracker := Option.some.inj (wasEnabled.symm.trans enabled)
    subst old
    exact ⟨UnitRetag.allocatedTracker tracker room,rfl,rfl⟩
  · intro old wasEnabled
    have same : old = tracker := Option.some.inj (wasEnabled.symm.trans enabled)
    subst old
    exact ⟨UnitRetag.allocatedTracker tracker room,rfl,fun _ _ found => found⟩

theorem preserves (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (choice : Case p tracker room)
    (original : p.before.stack.frames = older.push destination.caller)
    (whole : destination.offset = none) (enabled : p.before.machine.borrowTracker = some tracker) :
    Preservation.Preserves s p (ReturnContinuation.resume older (LocalModel.caller s p tracker destination bound)
      (LocalIndirectEndpoint.finishedMachine s p tracker destination older bound frame previous room choice index) p.returnBlock) := by
  rw [finished_eq]
  have baseline := tagged_preserves s metadata capacity p tracker destination older bound frame previous index room original whole enabled
  cases choice with
  | miss => exact baseline
  | nondata id registry => exact baseline
  | live id entry live tree release rights =>
    obtain ⟨returned,allocations,protectors,threads,slots,selected,context,threadContext,addresses,runtime,roots⟩ := baseline
    refine ⟨returned,?_,protectors,threads,slots,?_,context,threadContext,addresses,runtime,roots⟩
    · intro selected old found
      have memory : (taggedMachine s p tracker destination older bound frame previous index room).memory = p.before.machine.memory :=
        (LocalPost.fields s metadata capacity p tracker destination older bound frame previous index).1
      change ∃ current, (UnitRetag.replaceTree (taggedMachine s p tracker destination older bound frame previous index room).memory id entry tree).live.find?
        (fun row => row.1 == selected) = some (selected,current) ∧ _
      rw [memory]
      by_cases same : selected = id
      · subst selected
        have sameEntry : old = entry := congrArg Prod.snd (Option.some.inj (found.symm.trans live))
        subst old
        refine ⟨{entry with allocation := entry.allocation.setExtra tree},
          UnitRetag.replace_lookup p.before.machine.memory id entry tree,rfl,?_,rights⟩
        rfl
      · refine ⟨old,?_,rfl,rfl,old_rights_refl _⟩
        simp only [UnitRetag.replaceTree,Array.find?_push,Array.find?_filter]
        have predicate : (fun row : AllocId × InputDraft.Entry => decide ((row.1 != id) = true ∧ (row.1 == selected) = true)) =
            (fun row => row.1 == selected) := by
          funext row
          by_cases matched : row.1 = selected
          · simp [matched,same]
          · simp [matched]
        rw [predicate,found]
        rfl
    · simp [Preservation.SelectedProjectedContents,destination.encoding,whole]
end EmptyFunction.LocalIndirectPost
