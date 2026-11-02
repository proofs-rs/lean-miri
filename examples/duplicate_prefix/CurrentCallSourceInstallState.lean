import duplicate_prefix.DuplicatePrefixRuntimeInput
import duplicate_prefix.CandidateStableCallOwnership
import duplicate_prefix.CandidateCurrentJointCall
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.MemoryCopyBridge

namespace DuplicatePrefix.CurrentCallSourceInstallState
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

private theorem keys_apart {α β : Type} (rows : List α) (keys : α→List β)
    (unique : (rows.flatMap keys).Nodup) (first second : α)
    (firstMem : first∈rows) (secondMem : second∈rows) (different : first≠second)
    (key : β) (firstKey : key∈keys first) (secondKey : key∈keys second) : False := by
  induction rows with
  | nil => cases firstMem
  | cons head tail ih =>
    have parts := List.nodup_append.mp (show (keys head++tail.flatMap keys).Nodup from unique)
    rcases List.mem_cons.mp firstMem with sameFirst | firstTail
    · subst first
      rcases List.mem_cons.mp secondMem with sameSecond | secondTail
      · exact different sameSecond.symm
      · exact parts.2.2 key firstKey key (List.mem_flatMap.mpr ⟨second,secondTail,secondKey⟩) rfl
    · rcases List.mem_cons.mp secondMem with sameSecond | secondTail
      · subst second
        exact parts.2.2 key secondKey key (List.mem_flatMap.mpr ⟨first,firstTail,firstKey⟩) rfl
      · exact ih parts.2.1 firstTail secondTail

/-- Actual tree-only heap installation retains the finite state and global
high-water facts. Key origin and root distinctness are constructor metadata,
not operation success or a new caller validity domain. -/
theorem install (before final : Before) (tracker next : MachineHooks.BorrowState)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (global : next.global=(registered tracker.global frame id room).1)
    (tree : BorrowTree) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree next.global)
    (distinct : tree.roots.toList.Nodup) (capacity : tree.locations.size=entry.allocation.extra.locations.size)
    (keyOrigin : ∀ key index,(key,index)∈tree.tagMapping.mapping → key=tracker.global.nextPointerTag ∨
      ∃ oldIndex,(key,oldIndex)∈entry.allocation.extra.tagMapping.mapping)
    (tracked : final.borrowTracker=some next)
    (memory : final.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push
      (id,{entry with allocation:=entry.allocation.setExtra tree})) :
    DuplicatePrefixRuntimeInput.State final next ∧
    ∀ row∈final.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      next.global.protectedTags next.global.nextPointerTag := by
  let keys := fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
    row.2.allocation.extra.tagMapping.mapping.toList.map Prod.fst
  let kept := before.memory.live.toList.filter (fun row=>row.1!=id)
  have originalMem : (id,entry)∈before.memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have oldRuntime (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) (member : row∈before.memory.live.toList) :
      DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra tracker.global :=
    ⟨state.formed row member,state.coherent row member,state.possible row member,highwater row member⟩
  have nextRuntime (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) (member : row∈before.memory.live.toList) :
      DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra next.global := by
    rw [global]
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare _ tracker.global frame id room (oldRuntime row member)).2.2.2.1
  have rows : final.memory.live.toList=kept++[(id,{entry with allocation:=entry.allocation.setExtra tree})] := by
    simp only [memory,Array.toList_push,Array.toList_filter,kept]
  have memberCases (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) (member : row∈final.memory.live.toList) :
      (row∈before.memory.live.toList ∧ row.1≠id) ∨ row=(id,{entry with allocation:=entry.allocation.setExtra tree}) := by
    rw [rows,List.mem_append,List.mem_singleton] at member
    rcases member with old | same
    · exact Or.inl ⟨(List.mem_filter.mp old).1,by simpa using (List.mem_filter.mp old).2⟩
    · exact Or.inr same
  have idsKept : (kept.map Prod.fst).Nodup := by
    simpa only [List.Nodup,List.filter_map,Function.comp_def,kept] using state.allocationIds.filter (fun key=>key != id)
  have ids : (final.memory.live.toList.map Prod.fst).Nodup := by
    rw [rows,List.map_append]
    apply List.nodup_append.mpr
    refine ⟨idsKept,by simp,?_⟩
    intro key member other singleton same
    have otherEq : other=id := by simpa using singleton
    subst other
    subst key
    obtain ⟨row,rowMem,rowId⟩ := List.mem_map.mp member
    have different := (List.mem_filter.mp rowMem).2
    simp only [rowId,bne_self_eq_false,Bool.false_eq_true] at different
  have parts : (∀ row∈before.memory.live.toList,(keys row).Nodup) ∧
      List.Pairwise (fun left right=>∀ key∈keys left,∀ other∈keys right,key≠other) before.memory.live.toList :=
    List.pairwise_flatMap.mp state.tags
  have keptTags : (kept.flatMap keys).Nodup := by
    apply List.pairwise_flatMap.mpr
    exact ⟨fun row member=>parts.1 row (List.mem_filter.mp member).1,parts.2.filter _⟩
  have tags : (final.memory.live.toList.flatMap keys).Nodup := by
    rw [rows,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    apply List.nodup_append.mpr
    refine ⟨keptTags,runtime.formed.allocator.unique,?_⟩
    intro key member other otherMem same
    subst other
    obtain ⟨row,rowMem,keyMem⟩ := List.mem_flatMap.mp member
    obtain ⟨pair,pairMem,pairKey⟩ := List.mem_map.mp otherMem
    rcases keyOrigin pair.1 pair.2 (Array.mem_toList_iff.mp pairMem) with fresh | ⟨oldIndex,oldMem⟩
    · have oldKey : ∃ index,(key,index)∈row.2.allocation.extra.tagMapping.mapping := by
        obtain ⟨pair,member,equal⟩ := List.mem_map.mp keyMem
        exact ⟨pair.2,by simpa only [←equal] using Array.mem_toList_iff.mp member⟩
      obtain ⟨index,oldKey⟩ := oldKey
      have bound := (highwater row (List.mem_filter.mp rowMem).1).mapping (key,index) oldKey
      have equal : key=tracker.global.nextPointerTag := pairKey.symm.trans fresh
      rw [equal] at bound
      exact Nat.lt_irrefl _ bound
    · have originalKey : key∈keys (id,entry) := by
        apply List.mem_map.mpr
        exact ⟨(key,oldIndex),by simpa only [pairKey] using Array.mem_toList_iff.mpr oldMem,rfl⟩
      have different : row≠(id,entry) := by
        intro equal
        have notId := (List.mem_filter.mp rowMem).2
        simp only [equal,bne_self_eq_false,Bool.false_eq_true] at notId
      exact keys_apart _ keys state.tags row (id,entry) (List.mem_filter.mp rowMem).1 originalMem different key keyMem originalKey
  have sourceLength := state.treeLength (id,entry) originalMem
  refine ⟨{ enabled:=tracked
            allocationIds:=ids
            cachedRootIds:=?_
            cachedRootTags:=?_
            tags:=tags
            formed:=?_
            roots:=?_
            coherent:=?_
            possible:=?_
            byteLength:=?_
            maskValid:=?_
            maskLength:=?_
            provenance:=?_
            treeLength:=?_ },?_⟩
  · rw [global];exact state.cachedRootIds
  · rw [global];exact state.cachedRootTags
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact (nextRuntime row old).formed
    · subst row;exact runtime.formed
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact state.roots row old
    · subst row;exact distinct
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact (nextRuntime row old).coherent
    · subst row;exact runtime.coherent
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact (nextRuntime row old).possible
    · subst row;exact runtime.possible
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact state.byteLength row old
    · subst row;exact state.byteLength (id,entry) originalMem
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact state.maskValid row old
    · subst row;exact state.maskValid (id,entry) originalMem
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact state.maskLength row old
    · subst row;exact state.maskLength (id,entry) originalMem
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact state.provenance row old
    · subst row;exact state.provenance (id,entry) originalMem
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact state.treeLength row old
    · subst row;exact capacity.trans sourceLength
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact (nextRuntime row old).below
    · subst row;exact runtime.below

end
end DuplicatePrefix.CurrentCallSourceInstallState
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallSourceInstallState" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual source-install state dependency {dependency}"
