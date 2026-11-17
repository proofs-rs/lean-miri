import duplicate_prefix.CurrentCallCheckpointCopiedActivity
import duplicate_prefix.CurrentCallCheckpointQCover
import duplicate_prefix.GeneralBorrowEffectfulRetagCausalOrder
namespace DuplicatePrefix.CurrentCallCheckpointCopiedSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
noncomputable section
private theorem extra_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) : (allocation.setExtra tree).extra=tree:=by cases allocation;rfl
variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)
  (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (data : CurrentCallCheckpointAsMutSource.Data out done seed returned)
  (access : CurrentCallCheckpointCopyAccess.Access out done seed returned data)
  (copied : CurrentCallCheckpointCopyPrefix.Copied out done seed returned)

theorem nodes : copied.allocation.extra.nodes=seed.output.child.tree.nodes:=by
  have cert:=CurrentCallCheckpointMutableCurrent.release cp out.result out.source seed.machine (CurrentCallCheckpointAsMutRelease.present out done seed)
  rw [←CurrentCallCheckpointAsMutControl.helper_output out done seed] at cert
  have readFrame:=(GeneralBorrowEffectfulRetagCausalOrder.access_frame (CurrentCallCheckpointCopyPrefix.allocation out done seed).extra (.concrete seed.output.tag)
    (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes count) .Read (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags .VisitChildrenOfAccessed).1
  have writeFrame:=(GeneralBorrowEffectfulRetagCausalOrder.access_frame (CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree (.concrete seed.output.tag)
    (Size.ofBytes (UInt64.ofNat cp.offset+count)) (Size.ofBytes count) .Write (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags .VisitChildrenOfAccessed).1
  rw [copied.tree]
  change (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree.nodes=_
  have writeNodes : (CurrentCallCheckpointCopyPrefix.writeAccess out done seed).tree.nodes=(CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree.nodes:=writeFrame
  have readNodes : (CurrentCallCheckpointCopyPrefix.readAccess out done seed).tree.nodes=(CurrentCallCheckpointCopyPrefix.allocation out done seed).extra.nodes:=readFrame
  rw [writeNodes,readNodes]
  have oldTree : (CurrentCallCheckpointCopyPrefix.allocation out done seed).extra=CurrentCallCheckpointAsMutReturn.releasedTree seed:=extra_setExtra _ _
  rw [oldTree]
  change (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.nodes=_
  rw [cert.2.2.1]

include data access in
/-- The actual copied full S bank restores q in the same copied world. Every
current completion stays fixed through the two physical parent reanchors. -/
theorem restore {context : CurrentCallSpatialCover.Context copied.machine}
    (role : RoleCover copied.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) context .mut cp.offset len.toNat)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra (CurrentCallCheckpointAsMutReturn.postTracker seed).global)
    (allocation : role.backing.allocation=copied.allocation)
    (id : role.backing.id=out.source.role.backing.id)
    (concrete : role.family.value.provenance=.concrete role.backing.id seed.output.tag)
    (within : count≤len/2) :
    ∃newContext : CurrentCallSpatialCover.Context copied.machine,
      ∃qRole : RoleCover copied.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) newContext .mut cp.offset len.toNat,
      qRole.backing.allocation=copied.allocation ∧qRole.backing.id=out.source.role.backing.id ∧
      qRole.family.value.provenance=.concrete qRole.backing.id cp.source.tag ∧
      ∃qNode,qRole.backing.allocation.extra.nodes.get cp.source.grant=some qNode ∧qNode.tag=cp.source.tag ∧qNode.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin qRole.backing.allocation.extra cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) := by
  have outputEq:=CurrentCallCheckpointAsMutControl.helper_output out done seed
  have concreteS : role.family.value.provenance=.concrete role.backing.id (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag:=by rw [←outputEq];exact concrete
  have nodeEq : role.backing.allocation.extra.nodes=(CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.nodes:=by
    rw [allocation,←outputEq]
    exact nodes out done seed returned copied
  have flags : (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags=
      ((CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.endCall (CurrentCallCheckpointMutable.sOutput cp out.result out.source).frame).protectedTags:=by rw [←outputEq];rfl
  obtain ⟨newContext,qRole,qAllocation,qId,qConcrete,qOffset,qLookup⟩:=CurrentCallCheckpointQCover.restore cp out.result out.source role runtime concreteS nodeEq flags
  obtain ⟨pIndex,sIndex,pNode,qNode,sNode,sLookup,sAt,sTag,sParent,pAt,pTag,pParent,qAt,qTag,qHidden,qActive⟩:=CurrentCallCheckpointMutableParents.s_frame cp out.result out.source
  have currentQ : qRole.backing.allocation.extra.nodes.get cp.source.grant=some qNode:=by rw [qAllocation,nodeEq];exact qAt
  have active:=CurrentCallCheckpointCopiedActivity.activity out done seed returned data access copied within
  refine ⟨newContext,qRole,qAllocation.trans allocation,qId.trans id,qConcrete,qNode,currentQ,qTag,qHidden,?_⟩
  rw [qAllocation,allocation]
  exact active
end
end DuplicatePrefix.CurrentCallCheckpointCopiedSource
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopiedSource" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual copied source dependency {dependency}"
