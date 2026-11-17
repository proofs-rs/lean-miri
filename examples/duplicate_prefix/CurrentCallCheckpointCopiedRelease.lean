import duplicate_prefix.CurrentCallCheckpointCopiedQ
import duplicate_prefix.CurrentCallCheckpointCopiedBoolCurrent
import duplicate_prefix.CurrentCallCheckpointRoot3Release
namespace DuplicatePrefix.CurrentCallCheckpointCopiedRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallPostEntryCheckpoint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem replace_ids (rows : Array (AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind))
    (ids : (rows.toList.map Prod.fst).Nodup) (key : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) :
    (((rows.filter (fun row=>row.1 != key)).push (key,entry)).toList.map Prod.fst).Nodup:=by
  let kept:=rows.toList.filter (fun row=>row.1 != key)
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
private theorem setExtra_self (allocation : Allocation Provenance BorrowTree) : allocation.setExtra allocation.extra=allocation:=by cases allocation;rfl
private theorem lookup_id {memory : MemoryState Provenance BorrowTree MiriMemoryKind} {oldId newId : AllocId}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind} (eq : newId=oldId)
    (live : memory.live.find? (fun row=>row.1==oldId)=some (oldId,entry)) :
    memory.live.find? (fun row=>row.1==newId)=some (newId,entry):=by cases eq;exact live
variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits) (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done) (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (copied : CurrentCallCheckpointCopyPrefix.Copied out done seed returned)
  (Q : CurrentCallCheckpointCopiedQ.Data out done seed returned copied)
  (oldB : CurrentCallCheckpointAcceptedBoolCurrent.Packet out done seed returned)
  (B : CurrentCallCheckpointCopiedBoolCurrent.Packet out done seed returned oldB copied)

theorem ids : (copied.machine.memory.live.toList.map Prod.fst).Nodup:=by
  have initial:=CurrentCallCheckpointRoot3Release.ids out
  have afterP : ((CurrentCallCheckpointDefaultControl.machine out).memory.live.toList.map Prod.fst).Nodup:=by
    exact replace_ids out.machine.memory.live initial _ _
  have afterS : (returned.machine.memory.live.toList.map Prod.fst).Nodup:=by
    rw [returned.memory]
    exact replace_ids _ afterP _ _
  rw [copied.memory]
  exact replace_ids _ afterS _ _

theorem bool_tag : B.current.node.tag=cp.output.node.tag:=
  (congrArg (fun node : TreeNode=>node.tag) B.node).trans (oldB.tag.trans out.target.tag)

theorem bool_different (different : cp.output.id≠cp.source.role.backing.id) :
    B.current.window.allocation=cp.output.window.allocation:=by
  rw [B.allocated]
  unfold CurrentCallCheckpointCopiedBoolCurrent.allocation
  rw [ite_eq_right different,oldB.allocated]
  unfold CurrentCallCheckpointAcceptedBoolCurrent.tree
  rw [ite_eq_right different,setExtra_self,out.target.allocated]
  unfold CurrentCallCheckpointSharedBoolFrame.allocation
  rw [ite_eq_right different]

include Q in
theorem release : Nonempty (CurrentCallResourceCurrentRelease.Released B.current.window cp.borrowFrame
    B.current.original.grant B.current.physical.offset B.current.physical.entry):=by
  have separate : B.current.id=Q.role.backing.id→∀byte,
      Window Q.role.backing.id cp.offset len.toNat byte→Window B.current.id B.current.offset 1 byte→False:=by
    intro same byte first second
    have original : cp.output.id=cp.source.role.backing.id:=by simpa only [B.id,Q.id,out.source.id] using same
    exact cp.separate original byte (by simpa only [Q.id,out.source.id] using first)
      (by simpa only [B.id,B.offset] using second)
  have absent : B.current.id≠Q.role.backing.id→∀index node,
      B.current.window.allocation.extra.nodes.get index=some node→node.tag≠Q.node.tag:=by
    intro different index node found
    have original : cp.output.id≠cp.source.role.backing.id:=by simpa only [B.id,Q.id,out.source.id] using different
    rw [bool_different out done seed returned copied oldB B original] at found
    simpa only [Q.tag] using cp.sourceTagAbsentBool original index node found
  have ledger : cp.borrowFrame.protectedTags=#[(Q.role.backing.id,Q.node.tag),(B.current.id,B.current.node.tag)]:=by
    have first : (Q.role.backing.id,Q.node.tag)=(cp.source.role.backing.id,cp.source.tag):=
      Prod.ext (Q.id.trans out.source.id) Q.tag
    have second : (B.current.id,B.current.node.tag)=(cp.output.id,cp.output.node.tag):=
      Prod.ext B.id (bool_tag out done seed returned copied oldB B)
    have rows := (congrArg (fun row : AllocId×BorTag=>#[row,(B.current.id,B.current.node.tag)]) first).trans
      (congrArg (fun row : AllocId×BorTag=>#[(cp.source.role.backing.id,cp.source.tag),row]) second)
    exact cp.protectors.trans rows.symm
  let sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨(CurrentCallCheckpointAsMutControl.entry out).kind,copied.allocation⟩
  have live : copied.machine.memory.live.find? (fun row=>row.1==Q.role.backing.id)=some (Q.role.backing.id,sourceEntry):=
    lookup_id Q.id copied.live
  exact CurrentCallCheckpointRootRelease.of_resources Q.role B.current (ids out done seed returned copied)
    Q.runtime Q.distinct Q.short cp.source.positive cp.source.grant Q.node
    (by rw [Q.tag];exact Q.concrete) Q.present Q.hidden (by rw [Q.tag,bool_tag out done seed returned copied oldB B];exact cp.sourceBoolTags)
    absent cp.borrowFrame ledger separate Q.activity sourceEntry live Q.allocation.symm
end
end DuplicatePrefix.CurrentCallCheckpointCopiedRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopiedRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common copied root release dependency {dependency}"
