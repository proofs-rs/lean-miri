import duplicate_prefix.CurrentCallEmptyEntrySourceData
import duplicate_prefix.CurrentCallEmptyEntryQuietRelease
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.CurrentCallEmptyEntryPopPlan
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- The actual source row is released before Bool, with one unchanged held set.
The finite source data is derived from the original empty argument Effect. -/
theorem construct {options before tracker argument}
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (machine : Before) (data : CurrentCallEmptyEntrySourceData.Data effect machine)
    (protections : ProtectedTags) (id : AllocId) (tag : BorTag)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (written released : BorrowTree)
    (sourceRelease : effect.allocation = some id →
      written.releaseProtector tracker.global.nextPointerTag protections = ⟨written,.Released⟩)
    (boolRelease : written.releaseProtector tag protections = ⟨released,.Released⟩) :
    ∃ final, StackPopRelease.Plan protections
      ((effect.allocation.toList.map fun q => (q,tracker.global.nextPointerTag)) ++ [(id,tag)])
      (StackPopRelease.commitTree machine.memory id entry written) final ∧
      final.live.find? (fun row => row.1 == id) =
        some (id,{entry with allocation := entry.allocation.setExtra released}) := by
  let initial := StackPopRelease.commitTree machine.memory id entry written
  let boolEntry := {entry with allocation := entry.allocation.setExtra written}
  have boolLive : initial.live.find? (fun row => row.1 == id) = some (id,boolEntry) :=
    StackPopRelease.lookup_commit_same machine.memory id entry written
  have finish : ∀ memory, memory.live.find? (fun row => row.1 == id) = some (id,boolEntry) →
      ∃ final, StackPopRelease.Plan protections [(id,tag)] memory final ∧
        final.live.find? (fun row => row.1 == id) =
          some (id,{entry with allocation := entry.allocation.setExtra released}) := by
    intro memory found
    refine ⟨StackPopRelease.commitTree memory id boolEntry released,
      .live id tag boolEntry released [] memory _ found boolRelease (.nil _),?_⟩
    exact StackPopRelease.lookup_commit_same memory id boolEntry released
  cases allocation : effect.allocation with
  | none =>
    simpa only [allocation,Option.toList_none,List.map_nil,List.nil_append] using finish initial boolLive
  | some q =>
    by_cases same : q=id
    · subst q
      obtain ⟨final,tail,last⟩ := finish (StackPopRelease.commitTree initial id boolEntry written)
        (StackPopRelease.lookup_commit_same initial id boolEntry written)
      refine ⟨final,?_,last⟩
      simpa only [allocation,Option.toList_some,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using
        StackPopRelease.Plan.live id tracker.global.nextPointerTag boolEntry written [(id,tag)] initial final
          boolLive (sourceRelease allocation) tail
    · have sourceData : (∃ info,machine.memory.getAllocInfo q=.ok info ∧ info.kind≠.liveData) ∨
          ∃ source,machine.memory.live.find? (fun row=>row.1==q)=some (q,source) ∧
            CurrentCallEmptyEntrySourceData.Leaf source.allocation.extra tracker.global.nextPointerTag := by
        simpa only [CurrentCallEmptyEntrySourceData.Data,allocation] using data
      rcases sourceData with ⟨info,lookup,notLive⟩ | ⟨source,found,leaf⟩
      · obtain ⟨final,tail,last⟩ := finish initial boolLive
        have lookup' : initial.getAllocInfo q=.ok info :=
          (StackPopRelease.metadata_commit_other machine.memory id q entry written same).trans lookup
        refine ⟨final,?_,last⟩
        simpa only [allocation,Option.toList_some,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using
          StackPopRelease.Plan.skip q tracker.global.nextPointerTag info [(id,tag)] initial final lookup' notLive tail
      · have sourceLive := StackPopRelease.lookup_commit_other machine.memory id q entry source written same found
        obtain ⟨query,node,mapped,present,_,_,hidden,inactive⟩ := leaf
        have quiet := CurrentCallEmptyEntryQuietRelease.release source.allocation.extra tracker.global.nextPointerTag
          query node mapped present hidden inactive protections
        let middle := StackPopRelease.commitTree initial q source source.allocation.extra
        have boolLive' : middle.live.find? (fun row=>row.1==id)=some (id,boolEntry) :=
          StackPopRelease.lookup_commit_other initial q id source boolEntry source.allocation.extra (Ne.symm same) boolLive
        obtain ⟨final,tail,last⟩ := finish middle boolLive'
        refine ⟨final,?_,last⟩
        simpa only [allocation,Option.toList_some,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using
          StackPopRelease.Plan.live q tracker.global.nextPointerTag source source.allocation.extra [(id,tag)] initial final sourceLive quiet tail

end
end DuplicatePrefix.CurrentCallEmptyEntryPopPlan
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEmptyEntryPopPlan." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty pop dependency {dependency}"
