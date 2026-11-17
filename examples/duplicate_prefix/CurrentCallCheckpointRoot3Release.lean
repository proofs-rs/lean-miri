import duplicate_prefix.CurrentCallCheckpointRoot3
import duplicate_prefix.CurrentCallCheckpointRootRelease

namespace DuplicatePrefix.CurrentCallCheckpointRoot3Release
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint CurrentCallCheckpointRoot3
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem replace_ids (rows : Array (AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind))
    (ids : (rows.toList.map Prod.fst).Nodup) (key : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) :
    (((rows.filter (fun row=>row.1!=key)).push (key,entry)).toList.map Prod.fst).Nodup:=by
  let kept:=rows.toList.filter (fun row=>row.1!=key)
  have idsKept : (kept.map Prod.fst).Nodup:=by
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

variable {options remaining span len count place limits}
    {checkpoint : Checkpoint options remaining span len count place} (out : Output checkpoint limits)

theorem ids : (out.machine.memory.live.toList.map Prod.fst).Nodup:=by
  change (out.result.machine.memory.live.toList.map Prod.fst).Nodup
  rw [out.result.memory]
  apply replace_ids
  change (((checkpoint.machine.memory.live.filter (fun row=>row.1!=checkpoint.source.role.backing.id)).push
    (checkpoint.source.role.backing.id,{checkpoint.sourceEntry with allocation:=(checkpoint.sourceEntry.allocation.setExtra
      (CurrentCallCheckpointShared.tree checkpoint))})).toList.map Prod.fst).Nodup
  exact replace_ids checkpoint.machine.memory.live checkpoint.ids _ _

/-- The same spatial release consumer is applied to the joint actual root3
resources. It keeps the original Bool destination and one fixed source bank. -/
theorem release : Nonempty (CurrentCallResourceCurrentRelease.Released out.target.current.window checkpoint.borrowFrame
    out.target.current.original.grant out.target.current.physical.offset out.target.current.physical.entry):=by
  have separate : out.target.current.id=out.source.role.backing.id →∀byte,
      Window out.source.role.backing.id checkpoint.offset len.toNat byte →Window out.target.current.id out.target.current.offset 1 byte →False:=by
    intro same byte first second
    have original : checkpoint.output.id=checkpoint.source.role.backing.id:=by simpa only [out.target.id,out.source.id] using same
    exact checkpoint.separate original byte (by simpa only [out.source.id] using first)
      (by simpa only [out.target.id,out.target.offset] using second)
  have absent : out.target.current.id≠out.source.role.backing.id →∀index node,
      out.target.current.window.allocation.extra.nodes.get index=some node →node.tag≠out.source.node.tag:=by
    intro different index node present
    have original : checkpoint.output.id≠checkpoint.source.role.backing.id:=by simpa only [out.target.id,out.source.id] using different
    rw [out.target.allocated,CurrentCallCheckpointSharedBoolFrame.allocation,ite_eq_right original] at present
    rw [out.source.nodeTag]
    exact checkpoint.sourceTagAbsentBool original index node present
  exact CurrentCallCheckpointRootRelease.of_resources out.source.role out.target.current (ids out) out.source.runtime
    out.source.distinct (by have bound:=out.source.nodes;omega) checkpoint.source.positive checkpoint.source.grant out.source.node
    (by rw [out.source.nodeTag];exact out.source.concrete) out.source.nodeAt out.source.hidden
    (by rw [out.source.nodeTag,out.target.tag];exact checkpoint.sourceBoolTags) absent checkpoint.borrowFrame out.ledger separate
    out.source.activity
    {CurrentCallCheckpointLenControl.entry checkpoint with allocation:=
      ((CurrentCallCheckpointLenControl.entry checkpoint).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree checkpoint))}
    (by simpa only [out.source.id] using out.result.sourceLive) out.source.allocation.symm

end
end DuplicatePrefix.CurrentCallCheckpointRoot3Release
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointRoot3Release" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved joint root3 release dependency {dependency}"
