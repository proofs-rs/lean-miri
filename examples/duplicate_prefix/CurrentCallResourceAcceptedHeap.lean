import duplicate_prefix.CurrentCallResourceAcceptedCopy
import duplicate_prefix.CurrentCallResourceLenPhysical

namespace DuplicatePrefix.CurrentCallResourceAcceptedHeap
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)
    (copied : CurrentCallResourceAcceptedCopy.Result done fresh valid15 seed returned)

private theorem replace_ids (rows : Array (AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind))
    (ids : (rows.toList.map Prod.fst).Nodup) (key : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) :
    (((rows.filter (fun row=>row.1!=key)).push (key,entry)).toList.map Prod.fst).Nodup := by
  let kept:=rows.toList.filter (fun row=>row.1!=key)
  have idsKept : (kept.map Prod.fst).Nodup := by
    simpa only [List.Nodup,List.filter_map,Function.comp_def,kept] using ids.filter (fun id=>id != key)
  simp only [Array.toList_push,Array.toList_filter,List.map_append]
  apply List.nodup_append.mpr
  refine ⟨idsKept,by simp,?_⟩
  intro a member b singleton same
  have equal : b=key:=by simpa using singleton
  subst b
  subst a
  obtain ⟨row,hit,rowId⟩:=List.mem_map.mp member
  have different:=(List.mem_filter.mp hit).2
  simp only [rowId,bne_self_eq_false,Bool.false_eq_true] at different

/-- The actual accepted copy retains unique live allocation IDs through every
real source replacement, without any provenance well-formedness assumption. -/
theorem ids : (copied.machine.memory.live.toList.map Prod.fst).Nodup := by
  have lenIds : (result.machine.memory.live.toList.map Prod.fst).Nodup := by
    rw [CurrentCallResourceLenPhysical.memory result]
    exact replace_ids _ out.finalIds _ _
  have defaultMemory:=congrArg (fun machine : Before=>machine.memory) done.machineEq
  dsimp only [CurrentCallResourceAsMutInvoke.defaultMachine,ReferenceBorrowDriver.allocatedMachine] at defaultMemory
  have beforeIds : ((CurrentCallResourceAsMutInvoke.beforeDefault result).memory.live.toList.map Prod.fst).Nodup := lenIds
  have defaultIds : (done.machine.memory.live.toList.map Prod.fst).Nodup := by
    rw [defaultMemory]
    exact replace_ids _ beforeIds _ _
  have returnIds : (returned.machine.memory.live.toList.map Prod.fst).Nodup := by
    rw [returned.memory]
    exact replace_ids _ defaultIds _ _
  have memory:=congrArg MemoryState.live copied.memory
  dsimp only [CanonicalCopy.replaceAllocation,Storage.withCurrent] at memory
  rw [(AddOutput.preserved options remaining span returned.machine).1] at memory
  rw [memory]
  exact replace_ids _ returnIds _ _

end
end DuplicatePrefix.CurrentCallResourceAcceptedHeap
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedHeap" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted heap dependency {dependency}"
