import duplicate_prefix.CurrentCallCheckpointAsMutSourceMetadata
import duplicate_prefix.CurrentCallCheckpointCopyPrefix
import duplicate_prefix.CurrentCallSpatialSubrangeSequence
namespace DuplicatePrefix.CurrentCallCheckpointCopyAccess
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallSpatialCover CurrentCallResourceNormalization GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits) (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done) (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (data : CurrentCallCheckpointAsMutSource.Data out done seed returned)

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {CurrentCallCheckpointAsMutControl.entry out with allocation:=CurrentCallCheckpointCopyPrefix.allocation out done seed}

abbrev Stage := CurrentCallSpatialSubrangeSequence.ReadStage data.role (entry out done seed) (UInt64.ofNat cp.offset) count

private theorem lookup_id {memory : MemoryState Provenance BorrowTree MiriMemoryKind} {oldId newId : AllocId}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind} (eq : newId=oldId)
    (live : memory.live.find? (fun row=>row.1==oldId)=some (oldId,entry)) :
    memory.live.find? (fun row=>row.1==newId)=some (newId,entry):=by cases eq;exact live

theorem role_bounds {before tracker ctx offset length} (role : RoleCover before tracker ctx .mut offset length)
    (positive : 0<length) : offset+length≤role.backing.allocation.extra.locations.size.bytes.toNat:=by
  let byte:=(role.backing.id,offset+length-1)
  have hit : Window role.backing.id offset length byte:=⟨rfl,by dsimp only [byte];omega,by dsimp only [byte];omega⟩
  obtain ⟨i,inside⟩:=role.covered byte hit
  have bound:=((role.roles i ⟨byte,hit,inside⟩).available byte hit inside).1
  have cap:=(role.roles i ⟨byte,hit,inside⟩).issued.capability
  rw [cap.treeExtent,←cap.extent]
  dsimp only [byte] at bound
  omega

theorem read_eq : CurrentCallSpatialSubrangeSequence.readResult data.role (UInt64.ofNat cp.offset) count=
    CurrentCallCheckpointCopyPrefix.readAccess out done seed := by
  unfold CurrentCallSpatialSubrangeSequence.readResult CurrentCallCheckpointCopyPrefix.readAccess
  rw [data.allocation]
  unfold CurrentCallSpatialRows.provenance
  rw [CurrentCallCheckpointAsMutSourceMetadata.concrete out done seed returned data]
  rfl

theorem stage (nonzero : count≠0) (within : count≤len/2) : Nonempty (Stage out done seed returned data) := by
  have startEq : (UInt64.ofNat cp.offset).toNat=cp.offset:=CurrentCallCheckpointShared.start_eq cp
  have countBound : count.toNat≤len.toNat:=by
    have accepted:=UInt64.le_iff_toNat_le.mp within
    rw [UInt64.toNat_div] at accepted
    change count.toNat≤len.toNat/2 at accepted
    omega
  have sourceBounds:=role_bounds data.role cp.source.positive
  let point:=(data.role.backing.id,cp.offset)
  have request : Window data.role.backing.id cp.offset len.toNat point:=⟨rfl,Nat.le_refl _,by have positive:=cp.source.positive;dsimp only [point];omega⟩
  obtain ⟨i,cell⟩:=data.role.covered point request
  let overlap : CurrentCallSpatialSourceCover.Active data.role i:=⟨point,request,cell⟩
  obtain ⟨node,nodeAt,mapped,binding⟩:=(data.role.roles i overlap).binding
  change (match data.role.family.value.provenance with | .concrete id tag=>id=data.role.family.allocation ∧tag=node.tag | .wildcard=>node.isExposed=true) at binding
  rw [CurrentCallCheckpointAsMutSourceMetadata.concrete out done seed returned data] at binding
  have tagged : data.role.backing.allocation.extra.indexOfTag seed.output.tag=some (data.role.roles i overlap).grant:=by rw [binding.2];exact mapped
  have live : returned.machine.memory.live.find? (fun row=>row.1==data.role.backing.id)=some (data.role.backing.id,entry out done seed):=
    lookup_id data.id returned.sourceLive
  exact CurrentCallSpatialSubrangeSequence.read_stage data.role data.runtime
    (CurrentCallCheckpointAsMutSourceMetadata.roots out done seed returned data)
    (CurrentCallCheckpointAsMutSourceMetadata.short out done seed returned data)
    seed.output.tag (data.role.roles i overlap).grant (CurrentCallCheckpointAsMutSourceMetadata.concrete out done seed returned data) tagged
    (entry out done seed) live data.allocation (UInt64.ofNat cp.offset) count (by rw [startEq];exact Nat.le_refl _)
    (by rw [startEq];omega) nonzero (by rw [startEq];omega)

private abbrev RowRuntime (tree : BorrowTree) (flags : ProtectedTags) (location : LocationTree) :=
  GeneralBorrowExposureCardinality.LocationCoherent tree location flags ∧GeneralBorrowLocationSifaConsistency.Profile tree location flags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location

structure Access where
  read : Stage out done seed returned data
  write : GeneralBorrowConcreteRangeInvariant.Contract read.current.backing.allocation.extra (fun _=>True)
    (RowRuntime read.current.backing.allocation.extra (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags)
    (CurrentCallSpatialRows.Frame read.current) (UInt64.ofNat cp.offset+count) (UInt64.ofNat cp.offset+count+count)
    (CurrentCallSpatialSubrangeSequence.ReadStage.writeResult read (UInt64.ofNat cp.offset+count) count)
  writeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts
    (CurrentCallSpatialSubrangeSequence.ReadStage.writeResult read (UInt64.ofNat cp.offset+count) count).tree
    (CurrentCallCheckpointAsMutReturn.postTracker seed).global

theorem write_eq (read : Stage out done seed returned data) :
    CurrentCallSpatialSubrangeSequence.ReadStage.writeResult read (UInt64.ofNat cp.offset+count) count=
      CurrentCallCheckpointCopyPrefix.writeAccess out done seed := by
  rw [CurrentCallSpatialSubrangeSequence.ReadStage.write_eq,read_eq out done seed returned data]
  unfold CurrentCallCheckpointCopyPrefix.writeAccess CurrentCallSpatialRows.provenance
  rw [CurrentCallCheckpointAsMutSourceMetadata.concrete out done seed returned data]

/-- Both actual access certificates retain full-source banks across the same
Read then Write, before the C-free copy execution consumes them. -/
theorem invoke (nonzero : count≠0) (within : count≤len/2) : Nonempty (Access out done seed returned data) := by
  obtain ⟨read⟩:=stage out done seed returned data nonzero within
  have startEq : (UInt64.ofNat cp.offset).toNat=cp.offset:=CurrentCallCheckpointShared.start_eq cp
  have numeric:=UInt64.le_iff_toNat_le.mp within
  rw [UInt64.toNat_div] at numeric
  change count.toNat≤len.toNat/2 at numeric
  have sourceBounds:=role_bounds data.role cp.source.positive
  have noWrap : (UInt64.ofNat cp.offset).toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt (by rw [startEq];exact sourceBounds) data.role.backing.allocation.extra.locations.size.bytes.toNat_lt
  have middle : (UInt64.ofNat cp.offset+count).toNat=cp.offset+count.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega),startEq]
  have positive : 0<count.toNat:=Nat.pos_of_ne_zero (fun zero=>nonzero (UInt64.toNat_inj.mp zero))
  have capacity : read.current.backing.allocation.extra.locations.size=data.role.backing.allocation.extra.locations.size:=
    (congrArg (fun tree : BorrowTree=>tree.locations.size) (CurrentCallSpatialSubrangeSequence.ReadStage.tree read)).trans read.capacity
  obtain ⟨contract,runtime,parents,allCells⟩:=CurrentCallSpatialSubrangeSequence.ReadStage.write read
    (UInt64.ofNat cp.offset+count) count (by rw [middle];omega) (by rw [middle];omega) positive
    (by rw [capacity,middle];omega) .VisitChildrenOfAccessed
  exact ⟨⟨read,contract,runtime⟩⟩

theorem completed (access : Access out done seed returned data) :
    (CurrentCallCheckpointCopyPrefix.readAccess out done seed).status=.Completed ∧
    (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).status=.Completed := by
  refine ⟨?_,?_⟩
  · exact (congrArg (fun result : BorrowTree.BorrowTreeAccessResult=>result.status) (read_eq out done seed returned data).symm).trans access.read.done
  · exact (congrArg (fun result : BorrowTree.BorrowTreeAccessResult=>result.status) (write_eq out done seed returned data access.read).symm).trans access.write.completed
end
end DuplicatePrefix.CurrentCallCheckpointCopyAccess
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopyAccess" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common sequential copy access dependency {dependency}"
