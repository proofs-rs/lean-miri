import duplicate_prefix.CurrentCallResourceCurrentRelease
import duplicate_prefix.S05CompletedChildReanchor

namespace DuplicatePrefix.CurrentCallResourceSingleBoolRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem released_pair (result : BorrowTree.ProtectorReleaseResult) (done : result.status=.Released) :
    result=⟨result.tree,.Released⟩ := by
  cases result
  cases done
  rfl

/-- A frame protecting only the actual Bool child releases that child, commits
its real tree, ends the whole frame, and reanchors the original Bool grant.
No source family, dummy q, full completion, or child-leaf premise is needed. -/
theorem release {before tracker data owner id offset}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (distinct : B.allocation.extra.roots.toList.Nodup) (short : B.allocation.extra.nodes.size<65536)
    (concrete : ∃ supplied tag,B.pointer.value.provenance=.concrete supplied tag)
    (node : TreeNode) (present : B.allocation.extra.nodes.get B.pointer.grant=some node) (hidden : node.isExposed=false)
    (frame : FrameState) (tags : frame.protectedTags=#[(id,node.tag)])
    (original : UniIndex) (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original))
    (start : UInt64) (startEq : start.toNat=offset)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write start (start+1))
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (allocationEq : entry.allocation=B.allocation) :
    Nonempty (CurrentCallResourceCurrentRelease.Released B frame original start entry) := by
  have first:=(B.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have extent:=B.issued.capability.extent
  have limit:=UInt64.toNat_lt B.allocation.byteSize.bytes
  have fits : start.toNat+1<2^64:=by omega
  have noWrap : (start+1).toNat=start.toNat+1:=by
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]
  have positive : start.toNat<(start+1).toNat:=by rw [noWrap];omega
  obtain ⟨done,shape,afterRuntime,parents,capacity,owned⟩:=CurrentCallResourceRelease.release B rfl runtime concrete distinct short node present hidden
    start 1 startEq rfl positive noWrap active
  let result:=B.allocation.extra.releaseProtector node.tag tracker.global.protectedTags
  let memory:=StackPopRelease.commitTree before.memory id entry result.tree
  have nodeAt : result.tree.nodes.get B.pointer.grant=some node:=by rw [shape];exact present
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame result.tree frame:=by
    intro row member index current currentAt sameTag
    rw [tags] at member
    have equal : row=(id,node.tag):=List.mem_singleton.mp member
    subst row
    have one:=afterRuntime.formed.allocator.nodeTags index current currentAt
    have two:=afterRuntime.formed.allocator.nodeTags B.pointer.grant node nodeAt
    rw [sameTag] at one
    have indexEq : index=B.pointer.grant:=Option.some.inj (one.symm.trans two)
    subst index
    have nodeEq : current=node:=Option.some.inj (currentAt.symm.trans nodeAt)
    subst current
    exact hidden
  have finalRuntime:=S05CompletedChildReanchor.runtime_end_call result.tree tracker.global frame afterRuntime hiddenFrame
  have member : (id,node.tag)∈frame.protectedTags.toList:=by rw [tags];simp
  have parentOwned:=S05CompletedChildReanchor.owned_end_call result.tree B.precise.completion tracker.global frame id
    B.pointer.grant original node start (start+1) edge nodeAt member owned
  have actualRelease : entry.allocation.extra.releaseProtector node.tag tracker.global.protectedTags=⟨result.tree,.Released⟩:=by
    rw [allocationEq]
    exact released_pair _ done
  refine ⟨⟨memory,result.tree,?_,?_,finalRuntime,parents,shape,capacity,?_,?_,parentOwned⟩⟩
  · rw [tags]
    exact StackPopRelease.Plan.live id node.tag entry result.tree [] before.memory memory live actualRelease (.nil _)
  · simpa only [allocationEq] using StackPopRelease.lookup_commit_same before.memory id entry result.tree
  · rw [shape]
    exact distinct
  · rw [shape]
    exact short

end
end DuplicatePrefix.CurrentCallResourceSingleBoolRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSingleBoolRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual single Bool release dependency {dependency}"
