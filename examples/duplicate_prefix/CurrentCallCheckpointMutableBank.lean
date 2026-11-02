import duplicate_prefix.CurrentCallCheckpointMutableCurrent
import duplicate_prefix.CurrentCallResourceAsMutReturn
import duplicate_prefix.CurrentCallResourceLenCapability
namespace DuplicatePrefix.CurrentCallCheckpointMutableBank
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
open CurrentCallCheckpointMutable CurrentCallCheckpointMutableCurrent
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
variable {options remaining span len count place limits} (cp : Checkpoint options remaining span len count place)
  (control : CurrentCallCheckpointLenReturn.Result cp limits) (source : CurrentCallCheckpointLenSource.Data cp control)

theorem bank (post : Before)
    (present : Present (ActualWorld post) (prepared cp control source).role.backing.id
      ((prepared cp control source).role.backing.allocation.setExtra (sOutput cp control source).child.tree)) :
    ∃context : CurrentCallSpatialCover.Context post,
      ∃Q : RoleCover post ⟨(sOutput cp control source).global,(next cp control source).retagMode⟩ context .mut cp.offset len.toNat,
      Q.backing.allocation=(prepared cp control source).role.backing.allocation.setExtra (sOutput cp control source).child.tree ∧
      Q.backing.id=(prepared cp control source).role.backing.id ∧
      Q.family=CurrentCallSpatialSourceInstall.childFamily (prepared cp control source).role (sOutput cp control source).tag ∧
      S05CurrentReleaseIterator.Rows (CurrentCallSpatialProtectorRelease.SavedCells Q)
        ((sOutput cp control source).child.tree.releaseProtector (sOutput cp control source).tag (sOutput cp control source).global.protectedTags).tree.locations := by
  let nextTracker : MachineHooks.BorrowState:=⟨(sOutput cp control source).global,(next cp control source).retagMode⟩
  have rootTag : nextTracker.global.rootTag? (prepared cp control source).role.backing.id=(next cp control source).global.rootTag? (prepared cp control source).role.backing.id:=rfl
  obtain ⟨context,Q,allocation,idEq,family⟩:=cover cp control source post nextTracker present rootTag rfl
  have treeEq : Q.backing.allocation.extra=(sOutput cp control source).child.tree:=by
    rw [allocation];rfl
  obtain ⟨child,node,lookup,nodeAt,tag,hidden,active,roots⟩:=facets cp control source
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.backing.allocation.extra nextTracker.global:=by
    rw [treeEq];exact (s_operation cp control source).2.2.2.1
  have distinct : Q.backing.allocation.extra.roots.toList.Nodup:=by rw [treeEq,roots];exact (prepared cp control source).distinct
  have currentShort : Q.backing.allocation.extra.nodes.size<65536:=by rw [treeEq];exact short cp control source
  have currentAt : Q.backing.allocation.extra.nodes.get child=some node:=by rw [treeEq];exact nodeAt
  have concrete : Q.family.value.provenance=.concrete Q.backing.id node.tag:=by
    rw [family,idEq]
    change Provenance.concrete (prepared cp control source).role.backing.id (sOutput cp control source).tag=_
    rw [tag]
  have currentActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.backing.allocation.extra child .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len):=by rw [treeEq];exact active
  have noWrap : ((UInt64.ofNat cp.offset)+len).toNat=(UInt64.ofNat cp.offset).toNat+len.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (prepared cp control source).bounds (UInt64.toNat_lt (prepared cp control source).role.backing.allocation.extra.locations.size.bytes)
  have positive : (UInt64.ofNat cp.offset).toNat<((UInt64.ofNat cp.offset)+len).toNat:=by rw [noWrap];have positive:=cp.source.positive;omega
  obtain ⟨done,shape,runtime,capacity,rows⟩:=CurrentCallSpatialProtectorRelease.release Q rfl currentRuntime distinct currentShort child node currentAt concrete hidden
    (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl positive noWrap currentActive
  rw [treeEq,tag] at rows
  exact ⟨context,Q,allocation,idEq,family,rows⟩

end
end DuplicatePrefix.CurrentCallCheckpointMutableBank
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointMutableBank" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mutable-bank dependency {dependency}"
