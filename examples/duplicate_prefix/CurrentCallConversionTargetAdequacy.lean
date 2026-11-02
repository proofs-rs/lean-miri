import duplicate_prefix.CurrentCallOrdinaryInput

namespace DuplicatePrefix.CurrentCallConversionTargetAdequacy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

private theorem keyed_member {K V : Type} [BEq K] [Hashable K] {keyFn : V→K}
    (table : KeyedArray K V keyFn) (key : K) (value : V) (found : table.find? key=some value) :
    value∈table.toArray.toList := by
  simp only [KeyedArray.find?,bind,Option.bind] at found
  split at found
  · contradiction
  · dsimp only at found
    split at found
    · contradiction
    · obtain ⟨valid,equal⟩:=Array.getElem?_eq_some_iff.mp found
      have member:=Array.getElem_mem valid
      rw [equal] at member
      exact Array.mem_toList_iff.mpr member

/-- Actual selected global lookup returns a member of the CURRENT ordered
metadata rows, independently of imported-catalog identity or lookup keys. -/
theorem global_member {before : Before} {id : AllocId} {descriptor : GlobalAllocation}
    (found : before.memory.findGlobal? id=some descriptor) : descriptor∈before.memory.globals.toList := by
  unfold MemoryState.findGlobal? at found
  exact keyed_member _ _ _ found

/-- Every selected CURRENT conversion payload is included in the declarative
finite conversion-input bound. Static payloads use the actual initializer row. -/
theorem input_member {before : Before} {id : AllocId} {source : Allocation CtfeProvenance Unit}
    (payload : CurrentPayload before id source) :
    source∈currentConversionInputs before ++ PreparedReflection.actual.image.initializers.toList.map Prod.snd := by
  cases payload with
  | memory descriptor =>
    apply List.mem_append_left
    apply List.mem_filterMap.mpr
    exact ⟨_,global_member descriptor,rfl⟩
  | internalStatic definition descriptor initializer =>
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨(definition,source),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some initializer),rfl⟩

/-- This is the target of the actual adjustFromTcx pointer callback for any
member of its source ptrs iteration. No target root/address cache is assumed. -/
theorem current {before : Before} {id : AllocId} {source : Allocation CtfeProvenance Unit}
    (payload : CurrentPayload before id source) (row : Size × CtfeProvenance)
    (member : row∈source.provenanceMap.ptrs) : row.2.allocId∈conversionTargets before := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨source,input_member payload,?_⟩
  exact List.mem_map.mpr ⟨row,Array.mem_toList_iff.mpr member,rfl⟩

/-- Fixed-source relocation decoding uses this SAME runtime-ID correspondence;
its target is already included in the domain's conservative finite bound. -/
theorem fixed {before : Before} (row : Relocation) (member : row∈fixedRelocations)
    (id : AllocId) (mapping : before.memory.runtimeIdForExport? row.target=some id) :
    id∈conversionTargets before := by
  apply List.mem_append_right
  exact List.mem_filterMap.mpr ⟨row,member,mapping⟩

end DuplicatePrefix.CurrentCallConversionTargetAdequacy
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionTargetAdequacy" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current conversion-target dependency {dependency}"
