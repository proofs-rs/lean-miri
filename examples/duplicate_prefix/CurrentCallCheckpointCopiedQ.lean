import duplicate_prefix.CurrentCallCheckpointCopiedS
import duplicate_prefix.CurrentCallCheckpointCopiedSource
namespace DuplicatePrefix.CurrentCallCheckpointCopiedQ
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
noncomputable section
variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)
  (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (data : CurrentCallCheckpointAsMutSource.Data out done seed returned)
  (access : CurrentCallCheckpointCopyAccess.Access out done seed returned data)
  (copied : CurrentCallCheckpointCopyPrefix.Copied out done seed returned)
structure Data where
  context : CurrentCallSpatialCover.Context copied.machine
  role : RoleCover copied.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) context .mut cp.offset len.toNat
  allocation : role.backing.allocation=copied.allocation
  id : role.backing.id=out.source.role.backing.id
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra (CurrentCallCheckpointAsMutReturn.postTracker seed).global
  distinct : role.backing.allocation.extra.roots.toList.Nodup
  short : role.backing.allocation.extra.nodes.size<65536
  concrete : role.family.value.provenance=.concrete role.backing.id cp.source.tag
  node : TreeNode
  present : role.backing.allocation.extra.nodes.get cp.source.grant=some node
  tag : node.tag=cp.source.tag
  hidden : node.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len)

include data access in
theorem current (within : count≤len/2) : Nonempty (Data out done seed returned copied) := by
  obtain ⟨S⟩:=CurrentCallCheckpointCopiedS.current out done seed returned data access copied
  have concrete : S.role.family.value.provenance=.concrete S.role.backing.id seed.output.tag:=by
    rw [S.family,S.id]
    have old:=CurrentCallCheckpointAsMutSourceMetadata.concrete out done seed returned data
    rw [data.id] at old
    exact old
  obtain ⟨context,Q,allocation,id,provenance,node,nodeAt,nodeTag,hidden,active⟩:=CurrentCallCheckpointCopiedSource.restore out done seed returned data access copied S.role S.runtime S.allocation S.id concrete within
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts copied.allocation.extra (CurrentCallCheckpointAsMutReturn.postTracker seed).global:=by
    have actual:=S.runtime
    rw [S.allocation] at actual
    exact actual
  have readTree:=CurrentCallSpatialSubrangeSequence.ReadStage.tree access.read
  rw [CurrentCallCheckpointCopyAccess.read_eq out done seed returned data] at readTree
  have readShape:=access.read.shape
  rw [CurrentCallCheckpointCopyAccess.read_eq out done seed returned data] at readShape
  have readRoots : (CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree.roots=data.role.backing.allocation.extra.roots:=by rw [readShape]
  have writeRoots:=access.write.roots
  rw [CurrentCallCheckpointCopyAccess.write_eq out done seed returned data access.read] at writeRoots
  have copiedRoots : copied.allocation.extra.roots=data.role.backing.allocation.extra.roots:=
    (congrArg BorrowTree.roots copied.tree).trans (writeRoots.trans ((congrArg BorrowTree.roots readTree).trans readRoots))
  have copiedShort : copied.allocation.extra.nodes.size<65536:=by
    rw [CurrentCallCheckpointCopiedSource.nodes out done seed returned copied]
    have bound:=CurrentCallCheckpointMutableCurrent.short cp out.result out.source
    rw [←CurrentCallCheckpointAsMutControl.helper_output out done seed] at bound
    exact bound
  refine ⟨{ context := context
            role := Q
            allocation := allocation
            id := id
            runtime := ?_
            distinct := ?_
            short := ?_
            concrete := provenance
            node := node
            present := nodeAt
            tag := nodeTag
            hidden := hidden
            activity := active }⟩
  · rw [allocation];exact runtime
  · rw [allocation,copiedRoots];exact CurrentCallCheckpointAsMutSourceMetadata.roots out done seed returned data
  · rw [allocation];exact copiedShort
end
end DuplicatePrefix.CurrentCallCheckpointCopiedQ
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopiedQ" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual copied q dependency {dependency}"
