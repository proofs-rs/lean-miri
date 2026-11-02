import duplicate_prefix.CurrentCallEmptyEntryNonzeroDispatch

namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroHeap
open Miri.Interpreter Miri.Input
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallEmptyEntryNonzeroDispatch
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

variable {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}

theorem initial_live (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) :
    (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory.live.find? (fun row=>row.1==out.physical.id)=
      some (out.physical.id,{out.physical.entry with allocation:=out.updated}) := by
  unfold CurrentCallEmptyEntryNonzeroDispatchState.machine
  exact MemoryCopyBridge.live_lookup_replaced _ out.physical.id {out.physical.entry with allocation:=out.updated}

/-- Preserve the exact post-helper Bool row; the same-allocation alternative
retains the real helper tree rather than identifying it with the entry tree. -/
theorem bool_live (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (result : CompilerFrameContext.ActualFrame) (post : Before) (body : BodyResult out count result post) :
    (post.memory.live.find? (fun row=>row.1==out.physical.id)=
      some (out.physical.id,{out.physical.entry with allocation:=out.updated})) ∨
    ∃ heap : LiveHeap out count post,heap.id=out.physical.id ∧
      heap.entry={out.physical.entry with allocation:=out.updated} ∧
      post.memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,
        {out.physical.entry with allocation:=(out.updated.setExtra
          (S03EmptyNextLenInput.form heap.entry.allocation.extra (CurrentCallEmptyEntryNonzeroDispatchState.held out).global
            heap.runtime tracker.global.nextPointerTag heap.first heap.fresh heap.room).after)}) := by
  rcases body.heap with unchanged | existing
  · left
    rw [unchanged]
    exact initial_live out count
  · obtain ⟨heap⟩ := existing
    by_cases same : heap.id=out.physical.id
    · right
      have found := heap.live
      rw [same,initial_live] at found
      have entryEq : heap.entry={out.physical.entry with allocation:=out.updated} :=
        (Prod.mk.inj (Option.some.inj found)).2.symm
      refine ⟨heap,same,entryEq,?_⟩
      rw [heap.memory,←same]
      have lookup := MemoryCopyBridge.live_lookup_replaced
        (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory heap.id
        {heap.entry with allocation:=(heap.entry.allocation.setExtra
          (S03EmptyNextLenInput.form heap.entry.allocation.extra (CurrentCallEmptyEntryNonzeroDispatchState.held out).global
            heap.runtime tracker.global.nextPointerTag heap.first heap.fresh heap.room).after)}
      simpa only [RetagEntry.updatedMemory,entryEq] using lookup
    · left
      rw [heap.memory]
      exact StackPopRelease.lookup_commit_other _ heap.id out.physical.id heap.entry
        {out.physical.entry with allocation:=out.updated} _ (Ne.symm same) (initial_live out count)
end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroHeap

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroHeap" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty post-helper heap dependency {dependency}"
