import duplicate_prefix.CurrentCallCheckpointLenCurrent
import duplicate_prefix.CurrentCallCheckpointLenActivity

namespace DuplicatePrefix.CurrentCallCheckpointLenSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {options remaining span len count place} (cp : Checkpoint options remaining span len count place)

structure Data {limits} (result : CurrentCallCheckpointLenReturn.Result cp limits) where
  context : CurrentCallSpatialCover.Context result.machine
  role : RoleCover result.machine (CurrentCallCheckpointLenControl.postTracker cp) context .mut cp.offset len.toNat
  family : role.family=cp.source.role.family
  id : role.backing.id=cp.source.role.backing.id
  allocation : role.backing.allocation=(CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra (CurrentCallCheckpointLenControl.postTracker cp).global
  distinct : role.backing.allocation.extra.roots.toList.Nodup
  concrete : role.family.value.provenance=.concrete role.backing.id cp.source.tag
  node : TreeNode
  nodeAt : role.backing.allocation.extra.nodes.get cp.source.grant=some node
  nodeTag : node.tag=cp.source.tag
  hidden : node.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra cp.source.grant .Write
    (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len)
  binding : CandidateCallBindings.WindowBinding result.machine role.family.value role.backing.id cp.offset len.toNat
  storage : CurrentCallResourceEntrySourceStorage.Data role.backing.allocation (UInt64.ofNat cp.offset) len
  profile : CurrentCallBoolProtection.WindowReady result.machine role.backing.id cp.offset len.toNat
  nodes : role.backing.allocation.extra.nodes.size+4<65536
  tags : (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat+4<18446744073709551615

private theorem extra_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) :
    (allocation.setExtra tree).extra=tree := by cases allocation;rfl
private theorem nodes_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree) :
    ({tree with locations:=locations} : BorrowTree).nodes=tree.nodes := rfl
private theorem len_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) :
    (allocation.setExtra tree).len=allocation.len := by cases allocation;rfl
private theorem bytes_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) :
    (allocation.setExtra tree).byteSize=allocation.byteSize := by cases allocation;rfl

theorem of_return {limits} (result : CurrentCallCheckpointLenReturn.Result cp limits) : Nonempty (Data cp result) := by
  let p:=CurrentCallCheckpointLen.prepared cp
  obtain ⟨context,old,family,allocation,idEq,runtime⟩:=CurrentCallCheckpointLenCurrent.cover cp result
  let Q:=CurrentCallSpatialControlView.reindex old (CurrentCallCheckpointShared.start_eq cp).symm rfl
  have currentId : Q.backing.id=cp.source.role.backing.id:=idEq
  have currentAllocation : Q.backing.allocation=(CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp):=allocation
  have treeEq : Q.backing.allocation.extra=CurrentCallCheckpointLenControl.releasedTree cp :=
    (congrArg Allocation.extra currentAllocation).trans (extra_setExtra _ _)
  have oldFamily : Q.family=cp.source.role.family:=family.trans p.family
  have tickAddresses : (CurrentCallCheckpointShared.machine cp).user.addresses=cp.machine.user.addresses := by
    change (RootZeroCompleteState.tick options remaining span cp.machine).user.addresses=cp.machine.user.addresses
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have tickExtras : (CurrentCallCheckpointShared.machine cp).user.payload.payload.user.runtime.extras=cp.machine.user.payload.payload.user.runtime.extras := by
    change (RootZeroCompleteState.tick options remaining span cp.machine).user.payload.payload.user.runtime.extras=cp.machine.user.payload.payload.user.runtime.extras
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have addresses : result.machine.user.addresses=cp.machine.user.addresses := result.flags.addresses.trans (result.helper.addresses.trans tickAddresses)
  have extras : result.machine.user.payload.payload.user.runtime.extras=cp.machine.user.payload.payload.user.runtime.extras := result.flags.extras.trans (result.helper.extras.trans tickExtras)
  obtain ⟨node,nodeAt,nodeTag,hidden,activity⟩:=CurrentCallCheckpointLenActivity.current cp result.helper
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  obtain ⟨_,_,_,capacity,growth,helper,lookup,_,_,_⟩:=CurrentCallCheckpointLen.operations cp
  obtain ⟨_,_,releaseShape,_,_⟩:=CurrentCallCheckpointLenRelease.release cp result.helper
  obtain ⟨_,_,leaf,fields⟩:=CurrentCallCheckpointLenMetadata.frame p.source rfl p.runtime p.distinct p.short p.nodeRoom
    cp.source.tag cp.source.grant p.reader p.readerNode p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld p.room
    (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
  obtain ⟨contract,_,_⟩:=CurrentCallSpatialLenAssociatedRead.prepare p.source rfl p.runtime p.distinct p.short
    cp.source.tag cp.source.grant p.reader p.readerNode p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld p.room
    (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
  have actualRoots : (CurrentCallCheckpointLenRelease.actual cp).tree.roots=p.source.backing.allocation.extra.roots := leaf.roots.trans contract.roots
  have releasedRoots : (CurrentCallCheckpointLenControl.releasedTree cp).roots=(CurrentCallCheckpointShared.tree cp).roots := by
    rw [←CurrentCallCheckpointLenCurrent.released_eq cp,releaseShape]
    exact actualRoots.trans (congrArg BorrowTree.roots p.tree)
  have sharedRoots : (CurrentCallCheckpointShared.tree cp).roots=cp.source.role.backing.allocation.extra.roots :=
    (CurrentCallCheckpointShared.metadata cp).choose_spec.choose_spec.2.2.2.2.2.1
  have distinct : Q.backing.allocation.extra.roots.toList.Nodup := by
    rw [treeEq,releasedRoots,sharedRoots];exact cp.source.distinct
  have afterNodes : (CurrentCallCheckpointLenControl.releasedTree cp).nodes=(CurrentCallCheckpointLenRelease.actual cp).tree.nodes :=
    (congrArg BorrowTree.nodes (CurrentCallCheckpointLenCurrent.released_eq cp).symm).trans
      ((congrArg BorrowTree.nodes releaseShape).trans (nodes_locations _ _))
  have nodeBudget : Q.backing.allocation.extra.nodes.size+4<65536 := by
    rw [treeEq,afterNodes]
    have growth' : (CurrentCallCheckpointLenRelease.actual cp).tree.nodes.size≤p.source.backing.allocation.extra.nodes.size+1:=growth
    rw [p.tree] at growth'
    have sharedGrowth:=(CurrentCallCheckpointShared.operation cp).2.2.2.2.1
    have budget:=cp.source.nodes
    change (CurrentCallCheckpointShared.role cp).backing.allocation.extra.nodes.size+6<65536 at budget
    omega
  have tagBudget : (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat+4<18446744073709551615 := by
    have first:=GenericFunctionEntryNumerics.successor_value cp.tracker.global.nextPointerTag (CurrentCallCheckpointShared.room cp)
    have second:=GenericFunctionEntryNumerics.successor_value (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag p.room
    have last : (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat=
        (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value.toNat+1:=second
    have previous : (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value.toNat=cp.tracker.global.nextPointerTag.value.toNat+1:=first
    have budget:=cp.tags
    omega
  have concrete : Q.family.value.provenance=.concrete Q.backing.id cp.source.tag := by rw [oldFamily,currentId];exact cp.source.concrete
  have storageInitial : CurrentCallResourceEntrySourceStorage.Data cp.sourceEntry.allocation (UInt64.ofNat cp.offset) len :=
    (congrArg (fun allocation=>CurrentCallResourceEntrySourceStorage.Data allocation (UInt64.ofNat cp.offset) len) cp.sourceAllocation).mpr cp.copyReady.storage
  have storageUpdated := (storageInitial.set_extra (CurrentCallCheckpointShared.tree cp)).set_extra (CurrentCallCheckpointLenControl.releasedTree cp)
  have storage : CurrentCallResourceEntrySourceStorage.Data Q.backing.allocation (UInt64.ofNat cp.offset) len := by
    rw [currentAllocation];exact storageUpdated
  have profile : CurrentCallBoolProtection.WindowReady result.machine Q.backing.id cp.offset len.toNat := by
    rw [currentId]
    obtain ⟨sync,lookup,outside⟩:=cp.copyReady.profile
    exact ⟨sync,by rw [extras];exact lookup,outside⟩
  have lenEq : ((CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)).len=cp.sourceEntry.allocation.len :=
    (len_setExtra _ _).trans (len_setExtra _ _)
  have bytesEq : ((CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)).byteSize=cp.sourceEntry.allocation.byteSize :=
    (bytes_setExtra _ _).trans (bytes_setExtra _ _)
  have binding : CandidateCallBindings.WindowBinding result.machine Q.family.value Q.backing.id cp.offset len.toNat := by
    obtain ⟨entry,base,live,cached,extent,headroom,bounds,address,nonnull,provenance⟩:=cp.source.binding
    have entries : entry=cp.sourceEntry:=congrArg Prod.snd (Option.some.inj (live.symm.trans cp.sourceLive))
    subst entry
    rw [oldFamily,currentId]
    refine ⟨_,base,result.sourceLive,?_,?_,?_,?_,address,nonnull,?_⟩
    · rw [addresses];exact cached
    · exact lenEq.trans (extent.trans (congrArg (fun size=>size.bytes.toNat) bytesEq.symm))
    · rw [lenEq];exact headroom
    · rw [lenEq];exact bounds
    · rw [cp.source.concrete]
  refine ⟨{ context := context
            role := Q
            family := oldFamily
            id := currentId
            allocation := currentAllocation
            runtime := runtime
            distinct := distinct
            concrete := concrete
            node := node
            nodeAt := ?_
            nodeTag := nodeTag
            hidden := hidden
            activity := ?_
            binding := binding
            storage := storage
            profile := profile
            nodes := nodeBudget
            tags := tagBudget }⟩
  · rw [treeEq];exact nodeAt
  · rw [treeEq];exact activity

end
end DuplicatePrefix.CurrentCallCheckpointLenSource
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenSource" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Len source dependency {dependency}"
