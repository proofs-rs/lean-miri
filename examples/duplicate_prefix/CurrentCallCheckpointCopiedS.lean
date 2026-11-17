import duplicate_prefix.CurrentCallCheckpointCopyAccess
namespace DuplicatePrefix.CurrentCallCheckpointCopiedS
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallSpatialCover CurrentCallResourceNormalization GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem present_live (machine : Before) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)) : Present (ActualWorld machine) id entry.allocation:=by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
private theorem present_id {world old new allocation} (eq : new=old) (present : Present world old allocation) : Present world new allocation:=by cases eq;exact present
private theorem len_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) : (allocation.setExtra tree).len=allocation.len:=by cases allocation;rfl
private theorem bytes_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) : (allocation.setExtra tree).byteSize=allocation.byteSize:=by cases allocation;rfl
private theorem runtime_move {first second global} (eq : first=second)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts first global) : DuplicatePrefixBorrowContract.RuntimeFacts second global:=by cases eq;exact runtime
private theorem shape_move (before first second : BorrowTree) (eq : second=first)
    (shape : first={before with locations:=first.locations}) : second={before with locations:=second.locations}:=by cases eq;exact shape
private theorem origins_move {relation : LocationTree→LocationTree→Prop} {before first second : DedupRangeMap LocationTree} (eq : first=second) (origins : Origins relation before first) : Origins relation before second:=by cases eq;exact origins

variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits) (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done) (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (data : CurrentCallCheckpointAsMutSource.Data out done seed returned)
  (access : CurrentCallCheckpointCopyAccess.Access out done seed returned data)
  (copied : CurrentCallCheckpointCopyPrefix.Copied out done seed returned)

structure Data where
  context : Context copied.machine
  role : RoleCover copied.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) context .mut cp.offset len.toNat
  allocation : role.backing.allocation=copied.allocation
  id : role.backing.id=out.source.role.backing.id
  family : role.family=data.role.family
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra (CurrentCallCheckpointAsMutReturn.postTracker seed).global

include access in
theorem current : Nonempty (Data out done seed returned data copied) := by
  let read:=access.read
  have writeEq:=CurrentCallCheckpointCopyAccess.write_eq out done seed returned data read
  have copiedTree:=copied.tree.trans (congrArg (fun result : BorrowTree.BorrowTreeAccessResult=>result.tree) writeEq.symm)
  have runtime := runtime_move copiedTree.symm access.writeRuntime
  have shape:=shape_move read.current.backing.allocation.extra _ _ copiedTree access.write.tree_eq
  have capacity: copied.allocation.extra.locations.size=read.current.backing.allocation.extra.locations.size:=
    (congrArg (fun tree : BorrowTree=>tree.locations.size) copiedTree).trans access.write.capacity
  have frames:=origins_move (congrArg (fun tree : BorrowTree=>tree.locations) copiedTree.symm) access.write.frames
  have actual:=present_live copied.machine out.source.role.backing.id ⟨(CurrentCallCheckpointAsMutControl.entry out).kind,copied.allocation⟩ copied.live
  have live:=present_id (read.id.trans data.id) actual
  have readLen : read.current.backing.allocation.len=(CurrentCallCheckpointCopyPrefix.allocation out done seed).len:=
    (congrArg Allocation.len read.allocation).trans ((len_setExtra _ _).trans (congrArg Allocation.len data.allocation))
  have readBytes : read.current.backing.allocation.byteSize=(CurrentCallCheckpointCopyPrefix.allocation out done seed).byteSize:=
    (congrArg Allocation.byteSize read.allocation).trans ((bytes_setExtra _ _).trans (congrArg Allocation.byteSize data.allocation))
  have concrete : read.current.family.value.provenance=.concrete read.current.backing.id seed.output.tag:=by
    rw [read.family,read.id]
    exact CurrentCallCheckpointAsMutSourceMetadata.concrete out done seed returned data
  let point:=(read.current.backing.id,cp.offset)
  have request : Window read.current.backing.id cp.offset len.toNat point:=⟨rfl,Nat.le_refl _,by have positive:=cp.source.positive;dsimp only [point];omega⟩
  obtain ⟨i,cell⟩:=read.current.covered point request
  let overlap : CurrentCallSpatialSourceCover.Active read.current i:=⟨point,request,cell⟩
  obtain ⟨node,nodeAt,mapped,binding⟩:=(read.current.roles i overlap).binding
  change (match read.current.family.value.provenance with | .concrete id tag=>id=read.current.family.allocation ∧tag=node.tag | .wildcard=>node.isExposed=true) at binding
  rw [concrete] at binding
  have tagged : read.current.backing.allocation.extra.indexOfTag seed.output.tag=some (read.current.roles i overlap).grant:=by rw [binding.2];exact mapped
  obtain ⟨context,Q,allocation,idEq,family⟩:=CurrentCallSpatialSubrangeInstall.cover read.current copied.allocation live
    (copied.length.trans readLen.symm) (copied.byteSize.trans readBytes.symm) shape capacity runtime frames
    seed.output.tag (read.current.roles i overlap).grant concrete tagged
  exact ⟨⟨context,Q,allocation,idEq.trans (read.id.trans data.id),family.trans read.family,runtime_move (congrArg Allocation.extra allocation).symm runtime⟩⟩
end
end DuplicatePrefix.CurrentCallCheckpointCopiedS
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopiedS" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual copied full S bank dependency {dependency}"
