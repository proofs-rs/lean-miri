import duplicate_prefix.CurrentCallEmptyEntryNonzeroDispatch
import duplicate_prefix.CurrentCallEmptyEntryLenZeroTransport

namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroSourceRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallEmptyEntryNonzeroDispatch
open CurrentCallEmptyEntryNonzeroDispatchState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
variable {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}

private theorem memory_eq (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) :
    (machine out count).memory = {(sourceMachine out).memory with live := ((sourceMachine out).memory.live.filter (fun row => row.1 != out.physical.id)).push (out.physical.id,{out.physical.entry with allocation:=out.updated})} := by
  exact MemoryCopyBridge.live_update_twice (sourceMachine out).memory out.physical.id
    {out.physical.entry with allocation:=out.physical.entry.allocation.setExtra out.certificate.output.child.tree}
    {out.physical.entry with allocation:=out.updated}

private theorem initial_data (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (q : AllocId) (allocated : out.effect.allocation = some q) :
    (∃ info,(machine out count).memory.getAllocInfo q = .ok info ∧ info.kind ≠ .liveData) ∨
      ∃ source,(machine out count).memory.live.find? (fun row => row.1 == q) = some (q,source) ∧
        CurrentCallEmptyEntrySourceData.Leaf source.allocation.extra tracker.global.nextPointerTag := by
  by_cases same : q = out.physical.id
  · subst q
    have leaf := out.certificate.qLeaf allocated
    have updated := facts.2.2.2.2.2.2.1
    rw [←updated] at leaf
    refine .inr ⟨{out.physical.entry with allocation:=out.updated},?_,leaf⟩
    rw [memory_eq]
    exact MemoryCopyBridge.live_lookup_replaced _ out.physical.id {out.physical.entry with allocation:=out.updated}
  · have known := CurrentCallEmptyEntrySourceData.of_effect (CurrentCallPush.prepared_input input #[]) out.effect #[]
      (EmptyRootArguments.firstLive (root input)).frame {} 1 ((EmptyRootArguments.firstLive (root input)).valid EmptyRootArguments.i1)
    change CurrentCallEmptyEntrySourceData.Data out.effect (sourceMachine out) at known
    simp only [CurrentCallEmptyEntrySourceData.Data,allocated] at known
    rcases known with ⟨info,lookup,notLive⟩ | ⟨source,found,leaf⟩
    · left
      refine ⟨info,?_,notLive⟩
      rw [memory_eq]
      simpa only [StackPopRelease.commitTree,RetagEntry.updatedMemory,Allocation.setExtra,Allocation.mapExtra] using
        (StackPopRelease.metadata_commit_other (sourceMachine out).memory out.physical.id q
          {out.physical.entry with allocation:=out.updated} out.updated.extra same).trans lookup
    · right
      refine ⟨source,?_,leaf⟩
      rw [memory_eq]
      simpa only [StackPopRelease.commitTree,RetagEntry.updatedMemory,Allocation.setExtra,Allocation.mapExtra] using
        StackPopRelease.lookup_commit_other (sourceMachine out).memory out.physical.id q
          {out.physical.entry with allocation:=out.updated} source out.updated.extra same found

private theorem quiescent {tree : BorrowTree} {tag : BorTag}
    (leaf : CurrentCallEmptyEntrySourceData.Leaf tree tag) :
    ∃ index node,tree.indexOfTag tag = some index ∧ tree.nodeAt index = some node ∧
      node.isExposed = false ∧ S04ReturnReleaseInactive.Quiescent tree index := by
  obtain ⟨index,node,mapped,present,_,_,hidden,inactive⟩ := leaf
  refine ⟨index,node,mapped,present,hidden,?_⟩
  intro cursor valid state stored
  left
  have active := inactive cursor valid
  simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using active

/-- The actual post-body q row is either nonlive or releases unchanged, even
when both real zero-helper children have been attached to it. No source-live
premise or post-helper leaf assumption is supplied. -/
theorem source_release (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (result : CompilerFrameContext.ActualFrame) (post : Before) (body : BodyResult out count result post)
    (q : AllocId) (allocated : out.effect.allocation = some q) (protections : ProtectedTags) :
    (∃ info,post.memory.getAllocInfo q = .ok info ∧ info.kind ≠ .liveData) ∨
      ∃ source,post.memory.live.find? (fun row => row.1 == q) = some (q,source) ∧
        source.allocation.extra.releaseProtector tracker.global.nextPointerTag protections = ⟨source.allocation.extra,.Released⟩ := by
  have original := initial_data out count facts q allocated
  rcases body.heap with unchanged | changed
  · rw [unchanged]
    rcases original with nonlive | ⟨source,live,leaf⟩
    · exact .inl nonlive
    · obtain ⟨index,node,mapped,present,hidden,quiet⟩ := quiescent leaf
      exact .inr ⟨source,live,S04ReturnReleaseInactive.release _ _ index node mapped present hidden quiet protections⟩
  · obtain ⟨heap⟩ := changed
    have same : q = heap.id := Option.some.inj (allocated.symm.trans heap.allocation)
    subst q
    rcases original with ⟨info,lookup,notLive⟩ | ⟨source,live,leaf⟩
    · rw [MemoryState.getAllocInfo,heap.live] at lookup
      cases lookup
      exact False.elim (notLive rfl)
    · have equal : source = heap.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans heap.live))).2
      subst source
      obtain ⟨index,node,mapped,present,hidden,quiet⟩ := quiescent leaf
      let second := S03EmptyNextLenInput.form heap.entry.allocation.extra (held out).global heap.runtime
        tracker.global.nextPointerTag heap.first heap.fresh heap.room
      obtain ⟨middle,middleAt,_,_,middleHidden⟩ := S03EmptySharedFrame.old_node heap.first index node present
      have released := CurrentCallEmptyEntryLenZeroTransport.quiet_release heap.first.after
        (held out).global.nextPointerTag _ second tracker.global.nextPointerTag index middle
        (S03EmptySharedFrame.tagged heap.first tracker.global.nextPointerTag index mapped) middleAt
        (middleHidden.trans hidden) (S03EmptySharedFrame.quiescent heap.first index quiet) protections
      refine .inr ⟨{heap.entry with allocation:=heap.entry.allocation.setExtra second.after},?_,released⟩
      rw [heap.memory]
      exact StackPopRelease.lookup_commit_same _ heap.id heap.entry second.after

end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroSourceRelease

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroSourceRelease" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved source release dependency {dependency}"
