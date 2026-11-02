import duplicate_prefix.CurrentCallCheckpointLenRelease
import duplicate_prefix.CurrentCallCheckpointLenReturn
import duplicate_prefix.CurrentCallCheckpointLenMetadata
import duplicate_prefix.CurrentCallSpatialFutureCover
import duplicate_prefix.CurrentCallSpatialReleasedCover
namespace DuplicatePrefix.CurrentCallCheckpointLenCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {options remaining span len count place} (cp : Checkpoint options remaining span len count place)

theorem released_eq : ((CurrentCallCheckpointLenRelease.actual cp).tree.releaseProtector
    (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags).tree=
    CurrentCallCheckpointLenControl.releasedTree cp := by
  exact (congrArg (fun (tree : BorrowTree)=>
    (tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
      (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags).tree)
    (CurrentCallCheckpointLenRelease.actual_eq cp)).trans
      (congrArg (fun (global : GlobalState)=>
        ((CurrentCallCheckpointLenControl.borrowedTree cp).releaseProtector
          (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag global.protectedTags).tree)
        (CurrentCallCheckpointLenRelease.held_eq cp))

private theorem setExtra_twice (allocation : Allocation Provenance BorrowTree) (first second : BorrowTree) :
    (allocation.setExtra first).setExtra second=allocation.setExtra second := by cases allocation;rfl

private theorem extra_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) :
    (allocation.setExtra tree).extra=tree := by cases allocation;rfl

private theorem present_move {post : Before} {left right : AllocId} {allocation updated : Allocation Provenance BorrowTree}
    (idEq : left=right) (allocationEq : allocation=updated)
    (present : Present (ActualWorld post) right updated) : Present (ActualWorld post) left allocation := by
  cases idEq
  cases allocationEq
  exact present

theorem cover {limits} (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    ∃context : CurrentCallSpatialCover.Context result.machine,
      ∃current : RoleCover result.machine (CurrentCallCheckpointLenControl.postTracker cp) context .mut (UInt64.ofNat cp.offset).toNat len.toNat,
        current.family=(CurrentCallCheckpointLen.prepared cp).source.family ∧
        current.backing.allocation=(CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp) ∧
        current.backing.id=cp.source.role.backing.id ∧
        DuplicatePrefixBorrowContract.RuntimeFacts current.backing.allocation.extra (CurrentCallCheckpointLenControl.postTracker cp).global := by
  let p:=CurrentCallCheckpointLen.prepared cp
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  obtain ⟨done,runtime,shape,capacity,context,Q,allocation,idEq,treeEq,family,rows⟩:=CurrentCallCheckpointLenRelease.release cp result.helper
  obtain ⟨_,_,_,_,_,helper,lookup,_,_,_⟩:=CurrentCallCheckpointLen.operations cp
  obtain ⟨other,node,otherLookup,nodeAt,nodeTag,nodeParent,nodeHidden,_,_⟩:=CurrentCallCheckpointLenMetadata.graph
    p.source rfl p.runtime p.distinct p.short p.nodeRoom cp.source.tag cp.source.grant p.reader p.readerNode p.concrete p.tagged p.readerAt p.readerEdge
    p.hidden p.unheld p.room (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  have hAt : (CurrentCallCheckpointLenControl.releasedTree cp).nodeAt helper=some node := by
    rw [←released_eq cp,shape]
    exact nodeAt
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallCheckpointLenControl.releasedTree cp) (CurrentCallCheckpointLenRelease.registered cp).global := by
    rw [←released_eq cp];exact runtime
  obtain ⟨afterRuntime,_,_⟩:=GeneralBorrowHiddenProtectorDropRuntime.end_call (CurrentCallCheckpointLenControl.releasedTree cp)
    (CurrentCallCheckpointLenRelease.registered cp).global currentRuntime p.source.backing.id (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
    helper node hAt nodeTag nodeHidden
  have finalRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallCheckpointLenControl.releasedTree cp) (CurrentCallCheckpointLenControl.postTracker cp).global := by
    rw [←CurrentCallCheckpointLenRelease.future_eq cp]
    exact afterRuntime
  have finalId : Q.backing.id=cp.source.role.backing.id:=idEq.trans (CurrentCallCheckpointLenRelease.source_id cp)
  have finalAllocation : Q.backing.allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)=
      (CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp) :=
    (congrArg (fun a : Allocation Provenance BorrowTree=>a.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)) allocation).trans
      ((setExtra_twice _ _ _).trans (congrArg (fun a : Allocation Provenance BorrowTree=>a.setExtra (CurrentCallCheckpointLenControl.releasedTree cp))
        (CurrentCallCheckpointLenRelease.source_allocation cp)))
  have originalPresent : Present (ActualWorld result.machine) cp.source.role.backing.id
      ((CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)) := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some result.sourceLive),rfl⟩
  have live : Present (ActualWorld result.machine) Q.backing.id (Q.backing.allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)) :=
    present_move finalId finalAllocation originalPresent
  have releasedShape : CurrentCallCheckpointLenControl.releasedTree cp={Q.backing.allocation.extra with locations:=(CurrentCallCheckpointLenControl.releasedTree cp).locations} := by
    rw [treeEq,←released_eq cp];exact shape
  have releasedCapacity : (CurrentCallCheckpointLenControl.releasedTree cp).locations.size=Q.backing.allocation.extra.locations.size := by
    rw [treeEq,←released_eq cp];exact capacity
  have flags : ∀tag,(CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags.contains tag=(CurrentCallCheckpointLenRelease.future cp).global.protectedTags.contains tag := by
    intro tag;rw [CurrentCallCheckpointLenRelease.future_eq cp]
  have rows' : S05CurrentReleaseIterator.Rows (fun range location=>∃original∈Q.backing.allocation.extra.locations.entries.toList,
      original.range=range ∧CurrentCallSpatialRows.Frame Q original.data location) (CurrentCallCheckpointLenControl.releasedTree cp).locations := by
    rw [←released_eq cp];exact rows
  have concrete : Q.family.value.provenance=.concrete Q.backing.id cp.source.tag := by rw [family,idEq];exact p.concrete
  have tagged : Q.backing.allocation.extra.indexOfTag cp.source.tag=some cp.source.grant := by
    obtain ⟨_,_,_,_,_,_,_,_,⟨old,oldAt,oldTag,_,_⟩,_,_⟩:=CurrentCallCheckpointShared.metadata cp
    have initial : p.source.backing.allocation.extra.nodeAt cp.source.grant=some old := by rw [p.tree];exact oldAt
    obtain ⟨_,_,_,_,_,_,_,_,oldGraph⟩:=CurrentCallCheckpointLenMetadata.graph p.source rfl p.runtime p.distinct p.short p.nodeRoom
      cp.source.tag cp.source.grant p.reader p.readerNode p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld p.room
      (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
    obtain ⟨changed,changedAt,changedTag,_,_⟩:=oldGraph _ _ initial
    have beforeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.backing.allocation.extra (CurrentCallCheckpointLenRelease.registered cp).global := by
      rw [treeEq]
      exact (CurrentCallCheckpointLen.operations cp).2.2.1
    have changedAt' : Q.backing.allocation.extra.nodeAt cp.source.grant=some changed := by
      rw [treeEq];exact changedAt
    have mapped:=beforeRuntime.formed.allocator.nodeTags _ _ changedAt'
    rw [changedTag.trans (oldTag.trans cp.source.nodeTag)] at mapped
    exact mapped
  let updates:=CurrentCallSpatialReleasedCover.fixed_updates (post:=result.machine) (next:=CurrentCallCheckpointLenControl.postTracker cp)
    (tree:=CurrentCallCheckpointLenControl.releasedTree cp) Q live (by rw [CurrentCallCheckpointLenRelease.future_eq cp])
    releasedShape releasedCapacity finalRuntime flags rows' cp.source.tag cp.source.grant concrete tagged
  let current:=CurrentCallSpatialSourceCover.assemble Q live updates Q.id
  refine ⟨_,current,family,?_,?_,?_⟩
  · change Q.backing.allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)=_
    exact finalAllocation
  · exact idEq.trans (CurrentCallCheckpointLenRelease.source_id cp)
  · have currentAllocation : current.backing.allocation=Q.backing.allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp):=rfl
    have currentExtra : current.backing.allocation.extra=CurrentCallCheckpointLenControl.releasedTree cp:=
      (congrArg Allocation.extra currentAllocation).trans (extra_setExtra _ _)
    exact (congrArg (fun tree=>DuplicatePrefixBorrowContract.RuntimeFacts tree (CurrentCallCheckpointLenControl.postTracker cp).global) currentExtra).mpr finalRuntime

end
end DuplicatePrefix.CurrentCallCheckpointLenCurrent
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenCurrent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Len current dependency {dependency}"
