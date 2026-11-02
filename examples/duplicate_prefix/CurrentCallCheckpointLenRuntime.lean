import duplicate_prefix.CurrentCallCheckpointLenRelease
import duplicate_prefix.CurrentCallCheckpointLenReturn
import duplicate_prefix.CurrentCallCheckpointLenMetadata
import duplicate_prefix.CurrentCallSpatialFutureCover
import duplicate_prefix.CurrentCallSpatialReleasedCover
namespace DuplicatePrefix.CurrentCallCheckpointLenRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
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

theorem runtime {limits} (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallCheckpointLenControl.releasedTree cp)
      (CurrentCallCheckpointLenControl.postTracker cp).global := by
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
  exact finalRuntime

end
end DuplicatePrefix.CurrentCallCheckpointLenRuntime
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenRuntime" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Len runtime dependency {dependency}"
