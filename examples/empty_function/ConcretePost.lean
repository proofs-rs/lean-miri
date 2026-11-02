import empty_function.ConcreteEndpoint
import empty_function.IntegerPost
namespace EmptyFunction.ConcretePost
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def machine (s : Static) (p : Packet) (frame previous : LocalUnit.F)
    (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree) :=
  let baseline := IntegerPost.machine s p frame previous tracker room index
  {baseline with memory := UnitRetag.replaceTree baseline.memory id entry tree}

theorem finished_eq (s : Static) (p : Packet) (frame previous : LocalUnit.F)
    (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree) :
    ConcreteEndpoint.finishedMachine s p frame previous tracker room id entry tree index =
      machine s p frame previous tracker room index id entry tree := by
  unfold ConcreteEndpoint.finishedMachine ConcreteEndpoint.releasedPost machine IntegerPost.machine
    FrameExit.afterRelevanceAt FrameExit.afterRelevance
  split <;> rfl

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
    (place : MPlaceTy Provenance) (destination : p.destination = .memory place)
    (id : AllocId) (entry : InputDraft.Entry)
    (live : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : BorrowTree) (rights : Preservation.OldNodeRights entry.allocation.extra tree) :
    Preservation.Preserves s p (ReturnContinuation.resume older caller
      (machine s p frame previous tracker room index id entry tree) p.returnBlock) := by
  obtain ⟨returned,_,protectors,other,slots,_,context,threads,addresses,runtime,roots⟩ :=
    IntegerPost.preserves s metadata capacity p frame previous tracker room index older caller original enabled place destination
  refine ⟨returned,?_,protectors,other,slots,?_,context,threads,addresses,runtime,roots⟩
  · intro selected old found
    change ∃ current : InputDraft.Entry,
      (UnitRetag.replaceTree (IntegerPost.machine s p frame previous tracker room index).memory id entry tree).live.find?
        (fun row => row.1 == selected) = some (selected,current) ∧
      current.kind = old.kind ∧ current.allocation.mapExtra (fun _ => ()) = old.allocation.mapExtra (fun _ => ()) ∧
      Preservation.OldNodeRights old.allocation.extra current.allocation.extra
    rw [IntegerPost.memory_eq s metadata capacity]
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
  · simp [Preservation.SelectedProjectedContents,destination]
end EmptyFunction.ConcretePost
