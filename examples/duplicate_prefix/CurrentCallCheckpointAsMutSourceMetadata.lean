import duplicate_prefix.CurrentCallCheckpointAsMutSource
namespace DuplicatePrefix.CurrentCallCheckpointAsMutSourceMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
noncomputable section
private theorem extra_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) : (allocation.setExtra tree).extra=tree:=by cases allocation;rfl
variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)
  (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (data : CurrentCallCheckpointAsMutSource.Data out done seed returned)

theorem tree : data.role.backing.allocation.extra=CurrentCallCheckpointAsMutReturn.releasedTree seed:=
  (congrArg Allocation.extra data.allocation).trans (extra_setExtra _ _)

theorem concrete : data.role.family.value.provenance=.concrete data.role.backing.id seed.output.tag:=by
  rw [data.family,data.id]
  change Provenance.concrete (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.id seed.output.tag=_
  rw [(CurrentCallCheckpointMutable.prepared cp out.result out.source).id]

theorem roots : data.role.backing.allocation.extra.roots.toList.Nodup:=by
  have cert:=CurrentCallCheckpointMutableCurrent.release cp out.result out.source seed.machine (CurrentCallCheckpointAsMutRelease.present out done seed)
  rw [←CurrentCallCheckpointAsMutControl.helper_output out done seed] at cert
  obtain ⟨child,node,lookup,nodeAt,tag,hidden,active,oldRoots⟩:=CurrentCallCheckpointMutableCurrent.facets cp out.result out.source
  rw [←CurrentCallCheckpointAsMutControl.helper_output out done seed] at oldRoots
  rw [tree out done seed returned data]
  change (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.roots.toList.Nodup
  rw [cert.2.2.1]
  change seed.output.child.tree.roots.toList.Nodup
  rw [oldRoots]
  exact (CurrentCallCheckpointMutable.prepared cp out.result out.source).distinct

theorem short : data.role.backing.allocation.extra.nodes.size<65536:=by
  have cert:=CurrentCallCheckpointMutableCurrent.release cp out.result out.source seed.machine (CurrentCallCheckpointAsMutRelease.present out done seed)
  rw [←CurrentCallCheckpointAsMutControl.helper_output out done seed] at cert
  have bound:=CurrentCallCheckpointMutableCurrent.short cp out.result out.source
  rw [←CurrentCallCheckpointAsMutControl.helper_output out done seed] at bound
  rw [tree out done seed returned data]
  change (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.nodes.size<65536
  rw [cert.2.2.1]
  exact bound
end
end DuplicatePrefix.CurrentCallCheckpointAsMutSourceMetadata
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAsMutSourceMetadata" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved returned S metadata dependency {dependency}"
