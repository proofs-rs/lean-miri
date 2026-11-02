import duplicate_prefix.CurrentCallCheckpointAsMutControl
import duplicate_prefix.CurrentCallCheckpointMutableCurrent
import duplicate_prefix.CurrentCallCheckpointAsMutReturn
namespace DuplicatePrefix.CurrentCallCheckpointAsMutRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem present_of_live (machine : Before) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)) : Present (ActualWorld machine) id entry.allocation:=by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
private theorem present_move {world oldId newId oldAllocation newAllocation}
    (id : newId=oldId) (allocation : newAllocation=oldAllocation) (present : Present world oldId oldAllocation) :
    Present world newId newAllocation:=by cases id;cases allocation;exact present
variable {options remaining span len count place limits}
  {checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output checkpoint limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)

theorem parent_allocation :
    (CurrentCallCheckpointMutable.prepared checkpoint out.result out.source).role.backing.allocation=
      (CurrentCallCheckpointAsMutControl.entry out).allocation:=by
  rw [(CurrentCallCheckpointMutable.prepared checkpoint out.result out.source).allocation,
    out.source.allocation,CurrentCallCheckpointAsMutControl.p_tree out]
  rfl

/-- The logical S bank is installed on the actual helper-return heap. -/
theorem present : Present (ActualWorld seed.machine)
    (CurrentCallCheckpointMutable.prepared checkpoint out.result out.source).role.backing.id
    ((CurrentCallCheckpointMutable.prepared checkpoint out.result out.source).role.backing.allocation.setExtra
      (CurrentCallCheckpointMutable.sOutput checkpoint out.result out.source).child.tree) := by
  have actual:=present_of_live seed.machine out.source.role.backing.id
    {CurrentCallCheckpointAsMutControl.entry out with allocation:=(CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra seed.output.child.tree} seed.live
  have treeEq:=congrArg (fun output : GeneralBorrowForestFnEntry.Output=>output.child.tree)
    (CurrentCallCheckpointAsMutControl.helper_output out done seed)
  have first:=congrArg (fun allocation : Allocation Provenance BorrowTree=>
    allocation.setExtra (CurrentCallCheckpointMutable.sOutput checkpoint out.result out.source).child.tree) (parent_allocation out)
  have second:=congrArg (fun tree : BorrowTree=>(CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra tree) treeEq.symm
  exact present_move (CurrentCallCheckpointMutable.prepared checkpoint out.result out.source).id (first.trans second) actual

/-- One existing mutable release scan discharges the actual pop certificate. -/
theorem completed : (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).status=.Released:=by
  have release:=CurrentCallCheckpointMutableCurrent.release checkpoint out.result out.source seed.machine (present out done seed)
  have actual:=congrArg (fun output : GeneralBorrowForestFnEntry.Output=>
    (output.child.tree.releaseProtector output.tag output.global.protectedTags).status)
    (CurrentCallCheckpointAsMutControl.helper_output out done seed)
  exact actual.trans release.1

theorem invoke : Nonempty (CurrentCallCheckpointAsMutReturn.Returned seed):=
  CurrentCallCheckpointAsMutReturn.of_release seed (completed out done seed) checkpoint.model.debugOff checkpoint.validationFuel checkpoint.validationEq
end
end DuplicatePrefix.CurrentCallCheckpointAsMutRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAsMutRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common mutable release dependency {dependency}"
