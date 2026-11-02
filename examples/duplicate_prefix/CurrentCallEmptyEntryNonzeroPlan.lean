import duplicate_prefix.CurrentCallEmptyEntryPopPlan

namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroPlan
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Assemble the actual source-then-Bool scan on the post-helper heap. A
source with real zero-helper children is released quietly, without a leaf test. -/
theorem construct (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (allocation : Option AllocId)
    (sourceTag : BorTag) (protections : ProtectedTags) (id : AllocId) (tag : BorTag)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (released : BorrowTree)
    (live : memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (boolRelease : entry.allocation.extra.releaseProtector tag protections=⟨released,.Released⟩)
    (sameRelease : allocation=some id → entry.allocation.extra.releaseProtector sourceTag protections=⟨entry.allocation.extra,.Released⟩)
    (otherRelease : ∀ q,allocation=some q → q≠id →
      (∃ info,memory.getAllocInfo q=.ok info ∧ info.kind≠.liveData) ∨
      ∃ source,memory.live.find? (fun row=>row.1==q)=some (q,source) ∧
        source.allocation.extra.releaseProtector sourceTag protections=⟨source.allocation.extra,.Released⟩) :
    ∃ final,StackPopRelease.Plan protections
      ((allocation.toList.map fun q=>(q,sourceTag))++[(id,tag)]) memory final ∧
      final.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra released}) := by
  have finish : ∀ (current : MemoryState Provenance BorrowTree MiriMemoryKind),current.live.find? (fun row=>row.1==id)=some (id,entry) →
      ∃ final,StackPopRelease.Plan protections [(id,tag)] current final ∧
        final.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra released}) := by
    intro current found
    exact ⟨StackPopRelease.commitTree current id entry released,
      .live id tag entry released [] current _ found boolRelease (.nil _),
      StackPopRelease.lookup_commit_same current id entry released⟩
  cases allocated : allocation with
  | none => simpa only [allocated,Option.toList_none,List.map_nil,List.nil_append] using finish memory live
  | some q =>
    by_cases same : q=id
    · subst q
      let middle := StackPopRelease.commitTree memory id entry entry.allocation.extra
      obtain ⟨final,tail,last⟩ := finish middle (StackPopRelease.lookup_commit_same memory id entry entry.allocation.extra)
      refine ⟨final,?_,last⟩
      simpa only [allocated,Option.toList_some,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using
        StackPopRelease.Plan.live id sourceTag entry entry.allocation.extra [(id,tag)] memory final live (sameRelease allocated) tail
    · rcases otherRelease q allocated same with ⟨info,lookup,notLive⟩ | ⟨source,found,quiet⟩
      · obtain ⟨final,tail,last⟩ := finish memory live
        refine ⟨final,?_,last⟩
        simpa only [allocated,Option.toList_some,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using
          StackPopRelease.Plan.skip q sourceTag info [(id,tag)] memory final lookup notLive tail
      · let middle := StackPopRelease.commitTree memory q source source.allocation.extra
        have stillLive := StackPopRelease.lookup_commit_other memory q id source entry source.allocation.extra (Ne.symm same) live
        obtain ⟨final,tail,last⟩ := finish middle stillLive
        refine ⟨final,?_,last⟩
        simpa only [allocated,Option.toList_some,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using
          StackPopRelease.Plan.live q sourceTag source source.allocation.extra [(id,tag)] memory final found quiet tail
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroPlan

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroPlan" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty post-helper plan dependency {dependency}"
