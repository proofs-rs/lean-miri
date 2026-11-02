import duplicate_prefix.CurrentCallCheckpointAsMutRelease
import duplicate_prefix.CurrentCallCheckpointMutableBank
import duplicate_prefix.CurrentCallSpatialReleasedMutableCover
namespace DuplicatePrefix.CurrentCallCheckpointAsMutSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
private theorem present_of_live (machine : Before) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)) : Present (ActualWorld machine) id entry.allocation:=by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
private theorem present_move {world oldId newId oldAllocation newAllocation}
    (id : newId=oldId) (allocation : newAllocation=oldAllocation) (present : Present world oldId oldAllocation) :
    Present world newId newAllocation:=by cases id;cases allocation;exact present
private theorem extra_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) : (allocation.setExtra tree).extra=tree:=by cases allocation;rfl
private theorem setExtra_twice (allocation : Allocation Provenance BorrowTree) (first second : BorrowTree) : (allocation.setExtra first).setExtra second=allocation.setExtra second:=by cases allocation;rfl
variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)
  (returned : CurrentCallCheckpointAsMutReturn.Returned seed)

theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallCheckpointAsMutReturn.releasedTree seed)
    (CurrentCallCheckpointAsMutReturn.postTracker seed).global := by
  have cert:=CurrentCallCheckpointMutableCurrent.release cp out.result out.source seed.machine (CurrentCallCheckpointAsMutRelease.present out done seed)
  rw [←CurrentCallCheckpointAsMutControl.helper_output out done seed] at cert
  obtain ⟨child,node,lookup,nodeAt,tag,hidden,active,roots⟩:=CurrentCallCheckpointMutableCurrent.facets cp out.result out.source
  rw [←CurrentCallCheckpointAsMutControl.helper_output out done seed] at lookup nodeAt tag active roots
  have childAt : (CurrentCallCheckpointAsMutReturn.releasedTree seed).nodes.get child=some node:=by
    change (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.nodes.get child=some node
    rw [cert.2.2.1];exact nodeAt
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame (CurrentCallCheckpointAsMutReturn.releasedTree seed) seed.output.frame:=by
    intro row member index current present sameTag
    rw [seed.frameOwned] at member
    have sameRow : row=(out.source.role.backing.id,seed.output.tag):=List.mem_singleton.mp member
    subst row
    have one:=cert.2.1.formed.allocator.nodeTags index current present
    have two:=cert.2.1.formed.allocator.nodeTags child node childAt
    rw [sameTag] at one
    rw [tag] at two
    have same : index=child:=Option.some.inj (one.symm.trans two)
    subst index
    have sameNode : current=node:=Option.some.inj (present.symm.trans childAt)
    subst current
    exact hidden
  exact S05CompletedChildReanchor.runtime_end_call _ seed.output.global seed.output.frame cert.2.1 hiddenFrame

structure Data where
  context : CurrentCallSpatialCover.Context returned.machine
  role : RoleCover returned.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) context .mut cp.offset len.toNat
  allocation : role.backing.allocation=(CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)
  id : role.backing.id=out.source.role.backing.id
  family : role.family=CurrentCallSpatialSourceInstall.childFamily (CurrentCallCheckpointMutable.prepared cp out.result out.source).role seed.output.tag
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra (CurrentCallCheckpointAsMutReturn.postTracker seed).global

/-- The returned raw S pointer owns the full original source window, with one
fixed current completion per retained cell, on the actual root-7 world. -/
theorem current : Nonempty (Data out done seed returned) := by
  obtain ⟨oldContext,Q,allocation,idEq,family,rows⟩:=CurrentCallCheckpointMutableBank.bank cp out.result out.source seed.machine (CurrentCallCheckpointAsMutRelease.present out done seed)
  have cert:=CurrentCallCheckpointMutableCurrent.release cp out.result out.source seed.machine (CurrentCallCheckpointAsMutRelease.present out done seed)
  have outputEq:=CurrentCallCheckpointAsMutControl.helper_output out done seed
  have treeEq:=congrArg (fun output : GeneralBorrowForestFnEntry.Output=>output.child.tree) outputEq
  have globalEq:=congrArg (fun output : GeneralBorrowForestFnEntry.Output=>output.global) outputEq
  have tagEq:=congrArg (fun output : GeneralBorrowForestFnEntry.Output=>output.tag) outputEq
  have actualAllocation : Q.backing.allocation=(CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.setExtra seed.output.child.tree:=
    allocation.trans (congrArg (fun tree : BorrowTree=>(CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.setExtra tree) treeEq.symm)
  have actualFamily : Q.family=CurrentCallSpatialSourceInstall.childFamily (CurrentCallCheckpointMutable.prepared cp out.result out.source).role seed.output.tag:=
    family.trans (congrArg (CurrentCallSpatialSourceInstall.childFamily (CurrentCallCheckpointMutable.prepared cp out.result out.source).role) tagEq.symm)
  have releasedEq : CurrentCallCheckpointAsMutReturn.releasedTree seed=
      ((CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.releaseProtector (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags).tree:=
    congrArg (fun output : GeneralBorrowForestFnEntry.Output=>(output.child.tree.releaseProtector output.tag output.global.protectedTags).tree) outputEq
  have actualRows : S05CurrentReleaseIterator.Rows (CurrentCallSpatialProtectorRelease.SavedCells Q) (CurrentCallCheckpointAsMutReturn.releasedTree seed).locations:=by rw [releasedEq];exact rows
  rw [←outputEq] at cert
  have Qtree : Q.backing.allocation.extra=seed.output.child.tree:=(congrArg Allocation.extra actualAllocation).trans (extra_setExtra _ _)
  have Qid : Q.backing.id=out.source.role.backing.id:=idEq.trans (CurrentCallCheckpointMutable.prepared cp out.result out.source).id
  have afterAllocation : Q.backing.allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)=
      (CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed):=by
    rw [actualAllocation,setExtra_twice,CurrentCallCheckpointAsMutRelease.parent_allocation out]
  have actualLive : returned.machine.memory.live.find? (fun row=>row.1==out.source.role.backing.id)=
      some (out.source.role.backing.id,{CurrentCallCheckpointAsMutControl.entry out with allocation:=(CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)}):=returned.sourceLive
  have actualPresent : Present (ActualWorld returned.machine) out.source.role.backing.id
      ((CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)):=
    present_of_live returned.machine out.source.role.backing.id {CurrentCallCheckpointAsMutControl.entry out with allocation:=(CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)} actualLive
  have live : Present (ActualWorld returned.machine) Q.backing.id (Q.backing.allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)):=
    @present_move (ActualWorld returned.machine) out.source.role.backing.id Q.backing.id
      ((CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed))
      (Q.backing.allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)) Qid afterAllocation actualPresent
  have shape : CurrentCallCheckpointAsMutReturn.releasedTree seed={Q.backing.allocation.extra with locations:=(CurrentCallCheckpointAsMutReturn.releasedTree seed).locations}:=by rw [Qtree];exact cert.2.2.1
  have capacity : (CurrentCallCheckpointAsMutReturn.releasedTree seed).locations.size=Q.backing.allocation.extra.locations.size:=by rw [Qtree];exact cert.2.2.2
  have finalRuntime:=runtime out done seed
  have rootTag : (CurrentCallCheckpointAsMutReturn.postTracker seed).global.rootTag? Q.backing.id=
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.rootTag? Q.backing.id:=by
    change seed.output.global.rootTag? Q.backing.id=_
    exact congrArg (fun global : GlobalState=>global.rootTag? Q.backing.id) globalEq
  have flags : ∀tag,(CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags.contains tag=true→
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags.contains tag=true:=by
    intro tag held
    rw [←globalEq]
    exact GeneralBorrowRelease.end_call_weakens seed.output.global seed.output.frame tag held
  obtain ⟨child,node,lookup,nodeAt,nodeTag,hidden,active,roots⟩:=CurrentCallCheckpointMutableCurrent.facets cp out.result out.source
  rw [←outputEq] at lookup nodeAt nodeTag active roots
  have concrete : Q.family.value.provenance=.concrete Q.backing.id seed.output.tag:=by rw [actualFamily,idEq];rfl
  have mapped : Q.backing.allocation.extra.indexOfTag seed.output.tag=some child:=by rw [Qtree];exact lookup
  let updates:=CurrentCallSpatialReleasedMutableCover.fixed_updates Q (post:=returned.machine) (next:=CurrentCallCheckpointAsMutReturn.postTracker seed) (tree:=CurrentCallCheckpointAsMutReturn.releasedTree seed) live rootTag shape capacity finalRuntime flags actualRows seed.output.tag child concrete mapped
  let context:=CurrentCallSpatialSourceCover.context Q live updates
  let role:=CurrentCallSpatialSourceCover.assemble Q live updates Q.id
  refine ⟨{ context := context
            role := role
            allocation := afterAllocation
            id := Qid
            family := actualFamily
            runtime := ?_ }⟩
  have extra : role.backing.allocation.extra=CurrentCallCheckpointAsMutReturn.releasedTree seed:=extra_setExtra _ _
  rw [extra]
  exact finalRuntime
end
end DuplicatePrefix.CurrentCallCheckpointAsMutSource
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAsMutSource" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved returned S source dependency {dependency}"
