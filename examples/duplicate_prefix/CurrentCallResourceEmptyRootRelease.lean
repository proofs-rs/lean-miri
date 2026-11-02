import duplicate_prefix.S04ReturnReleaseInactive
import duplicate_prefix.CurrentCallResourceCurrentRelease
import duplicate_prefix.S05CompletedChildReanchor

namespace DuplicatePrefix.CurrentCallResourceEmptyRootRelease
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

/-- Current stored states suffice; no source byte window or authority is used. -/
theorem quiescent_of_inactive (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (inactive : GeneralRangeMapState.Every
      (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row index node).accessed=false) tree.locations) :
    S04ReturnReleaseInactive.Quiescent tree index := by
  intro position valid state stored
  left
  have quiet:=inactive position valid
  simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using quiet

/-- Release the real inactive zero-source tag, then the current Bool child,
commit both actual trees, end the full two-protector frame, and reanchor the
original Bool grant. No source authority or source family is required. -/
theorem release {before tracker data owner id offset}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (distinct : B.allocation.extra.roots.toList.Nodup) (short : B.allocation.extra.nodes.size<65536)
    (concrete : ∃ supplied tag,B.pointer.value.provenance=.concrete supplied tag)
    (node : TreeNode) (present : B.allocation.extra.nodes.get B.pointer.grant=some node) (hidden : node.isExposed=false)
    (sourceId : AllocId) (sourceTag : BorTag)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : before.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry))
    (sourceIndex : UniIndex) (sourceNode : TreeNode)
    (sourceTagged : sourceEntry.allocation.extra.indexOfTag sourceTag=some sourceIndex)
    (sourcePresent : sourceEntry.allocation.extra.nodeAt sourceIndex=some sourceNode)
    (sourceHidden : sourceNode.isExposed=false)
    (sourceQuiet : S04ReturnReleaseInactive.Quiescent sourceEntry.allocation.extra sourceIndex)
    (sourceHiddenOnBool : ∀ index current,B.allocation.extra.nodes.get index=some current→current.tag=sourceTag→current.isExposed=false)
    (frame : FrameState) (tags : frame.protectedTags=#[(sourceId,sourceTag),(id,node.tag)])
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
  let sourceTree:=sourceEntry.allocation.extra
  let sourceMemory:=StackPopRelease.commitTree before.memory sourceId sourceEntry sourceTree
  let memory:=StackPopRelease.commitTree sourceMemory id entry result.tree
  have sourceRelease : sourceTree.releaseProtector sourceTag tracker.global.protectedTags=⟨sourceTree,.Released⟩ :=
    S04ReturnReleaseInactive.release sourceTree sourceTag sourceIndex sourceNode sourceTagged sourcePresent sourceHidden sourceQuiet tracker.global.protectedTags
  have sourceSelf : sourceEntry.allocation.setExtra sourceTree=sourceEntry.allocation := by
    change sourceEntry.allocation.setExtra sourceEntry.allocation.extra=sourceEntry.allocation
    cases sourceEntry.allocation;rfl
  have boolLive : sourceMemory.live.find? (fun row=>row.1==id)=some (id,entry) := by
    by_cases same : id=sourceId
    · have entryEq : entry=sourceEntry := by
        rw [same] at live
        exact (Prod.mk.inj (Option.some.inj (live.symm.trans sourceLive))).2
      subst entry
      subst id
      simpa only [sourceSelf] using StackPopRelease.lookup_commit_same before.memory sourceId sourceEntry sourceTree
    · exact StackPopRelease.lookup_commit_other before.memory sourceId id sourceEntry entry sourceTree same live
  have nodeAt : result.tree.nodes.get B.pointer.grant=some node:=by rw [shape];exact present
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame result.tree frame:=by
    intro row member index current currentAt sameTag
    rw [tags] at member
    have alternatives : row=(sourceId,sourceTag) ∨row=(id,node.tag) := by simpa only [Array.toList_push,Array.toList_empty,List.mem_cons,List.not_mem_nil,or_false] using member
    rcases alternatives with sourceEq | boolEq
    · subst row
      apply sourceHiddenOnBool index current
      · rw [shape] at currentAt
        exact currentAt
      · exact sameTag
    · subst row
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
    apply StackPopRelease.Plan.live sourceId sourceTag sourceEntry sourceTree [(id,node.tag)] before.memory memory sourceLive sourceRelease
    exact StackPopRelease.Plan.live id node.tag entry result.tree [] sourceMemory memory boolLive actualRelease (.nil _)
  · simpa only [allocationEq] using StackPopRelease.lookup_commit_same sourceMemory id entry result.tree
  · rw [shape]
    exact distinct
  · rw [shape]
    exact short

end
end DuplicatePrefix.CurrentCallResourceEmptyRootRelease
