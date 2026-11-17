import duplicate_prefix.CurrentCallCheckpointLenRelease
import duplicate_prefix.GeneralBorrowActiveWithinRelease
import duplicate_prefix.CurrentCallCheckpointLenControl
import duplicate_prefix.CurrentCallCheckpointLenMetadata
import duplicate_prefix.CurrentCallSpatialFutureCover
import duplicate_prefix.CurrentCallSpatialReleasedCover
namespace DuplicatePrefix.CurrentCallCheckpointLenActivity
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

theorem current {limits frame shape base}
    (returned : CurrentCallCheckpointLenControl.Returned cp limits frame shape base) :
    ∃node,(CurrentCallCheckpointLenControl.releasedTree cp).nodeAt cp.source.grant=some node ∧node.tag=cp.source.tag ∧node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointLenControl.releasedTree cp) cp.source.grant .Write
        (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) := by
  let p:=CurrentCallCheckpointLen.prepared cp
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  obtain ⟨_,_,_,_,_,_,_,_,⟨qNode,qAt,qTag,qParent,qHidden⟩,qActivity,_⟩:=CurrentCallCheckpointShared.metadata cp
  have qInitial : p.source.backing.allocation.extra.nodeAt cp.source.grant=some qNode:=by rw [p.tree];exact qAt
  have initialActivity : GeneralBorrowFreshActiveWithin.ActiveWithin p.source.backing.allocation.extra cp.source.grant .Write (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len):=by rw [p.tree];exact qActivity
  obtain ⟨contract,readRuntime,parents⟩:=CurrentCallSpatialLenAssociatedRead.prepare p.source rfl p.runtime p.distinct p.short
    cp.source.tag cp.source.grant p.reader p.readerNode p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld p.room
    (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
  have tags : (CurrentCallCheckpointLenRelease.accessed cp).tree.tagMapping=p.source.backing.allocation.extra.tagMapping:=contract.tags
  have nodes : (CurrentCallCheckpointLenRelease.accessed cp).tree.nodes=p.source.backing.allocation.extra.nodes:=contract.nodes
  have capacity : (CurrentCallCheckpointLenRelease.accessed cp).tree.locations.size=p.source.backing.allocation.extra.locations.size:=contract.capacity
  have readActivity:=GeneralBorrowFreshActiveWithinAccess.normal p.source.backing.allocation.extra p.readerNode.tag
    (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes len) .Read (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags
    .VisitChildrenOfAccessed cp.source.grant (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) p.runtime.formed.well p.bounds
    (Nat.le_refl _) (Nat.le_refl _) initialActivity
  obtain ⟨_,_,_,_,_,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare p.source.backing.allocation.extra
    (CurrentCallCheckpointShared.tracker cp).global {} p.source.backing.id p.room p.runtime
  have mapped : (CurrentCallCheckpointLenRelease.accessed cp).tree.indexOfTag p.readerNode.tag=some p.reader:=by
    change (CurrentCallCheckpointLenRelease.accessed cp).tree.tagMapping.get _=_
    rw [tags]
    exact p.runtime.formed.allocator.nodeTags _ _ p.readerAt
  have readerAt : (CurrentCallCheckpointLenRelease.accessed cp).tree.nodeAt p.reader=some p.readerNode:=by
    change (CurrentCallCheckpointLenRelease.accessed cp).tree.nodes.get _=_
    rw [nodes];exact p.readerAt
  have freshAfter : GeneralBorrowTagMap.Fresh (CurrentCallCheckpointLenRelease.accessed cp).tree.tagMapping
      (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag:=by rw [tags];exact fresh
  have roomAfter : (CurrentCallCheckpointLenRelease.accessed cp).tree.nodes.size+1≤4294967295:=by rw [nodes];exact p.nodeRoom
  have boundsAfter : (UInt64.ofNat cp.offset).toNat+len.toNat≤(CurrentCallCheckpointLenRelease.accessed cp).tree.locations.size.bytes.toNat:=by rw [capacity];exact p.bounds
  have childActivity:=GeneralBorrowRawTargetActivity.shared (CurrentCallCheckpointLenRelease.accessed cp).tree
    (CurrentCallCheckpointLenRelease.registered cp).global readRuntime p.readerNode.tag (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
    p.reader p.readerNode mapped readerAt freshAfter roomAfter true (UInt64.ofNat cp.offset) len nonzero boundsAfter cp.source.grant
    (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) (Nat.le_refl _) (Nat.le_refl _) readActivity
  obtain ⟨_,_,_,_,_,helper,lookup,caps,active,_⟩:=CurrentCallCheckpointLen.operations cp
  obtain ⟨other,node,otherLookup,nodeAt,nodeTag,nodeParent,nodeHidden,_,old⟩:=CurrentCallCheckpointLenMetadata.graph p.source rfl p.runtime p.distinct p.short p.nodeRoom cp.source.tag cp.source.grant p.reader p.readerNode p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld p.room (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  have activeWrite:=GeneralBorrowFreshActiveWithin.to_write _ helper (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) active
  have releasedActivity:=GeneralBorrowActiveWithinRelease.release (CurrentCallCheckpointLenRelease.actual cp).tree
    (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
    helper cp.source.grant node lookup nodeAt nodeHidden (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) activeWrite childActivity
  obtain ⟨changed,changedAt,changedTag,_,changedHidden⟩:=old _ _ qInitial
  obtain ⟨_,_,shape,_,_⟩:=CurrentCallCheckpointLenRelease.release cp returned
  have treeEq : ((CurrentCallCheckpointLenRelease.actual cp).tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
      (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags).tree=CurrentCallCheckpointLenControl.releasedTree cp := by
    rw [CurrentCallCheckpointLenRelease.actual_eq cp,CurrentCallCheckpointLenRelease.held_eq cp];rfl
  refine ⟨changed,?_,changedTag.trans (qTag.trans cp.source.nodeTag),changedHidden.trans (qHidden.trans cp.source.hidden),?_⟩
  · rw [←treeEq,shape];exact changedAt
  · rw [←treeEq];exact releasedActivity

end
end DuplicatePrefix.CurrentCallCheckpointLenActivity
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenActivity" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Len activity dependency {dependency}"
