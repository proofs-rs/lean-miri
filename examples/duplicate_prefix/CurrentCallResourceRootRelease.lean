import duplicate_prefix.CurrentCallResourceReleaseInstall
import duplicate_prefix.S05CompletedChildReanchor

namespace DuplicatePrefix.CurrentCallResourceRootRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Both actual root releases retain the SAME still-held protector table. The
original return grant is reanchored only after whole-frame endCall. -/
theorem same_tree {before tracker qData qOwner id offset length bData bOwner boolOffset}
    (Q : UniformWindow before tracker qData qOwner id offset length .mut)
    (B : UniformWindow before tracker bData bOwner id boolOffset 1 .ret)
    (allocation : B.allocation=Q.allocation) (completion : B.precise.completion=Q.precise.completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (distinct : Q.allocation.extra.roots.toList.Nodup) (short : Q.allocation.extra.nodes.size<65536)
    (qConcrete : ∃ suppliedId tag,Q.pointer.value.provenance=.concrete suppliedId tag)
    (bConcrete : ∃ suppliedId tag,B.pointer.value.provenance=.concrete suppliedId tag)
    (qNode bNode : TreeNode)
    (qAt : Q.allocation.extra.nodes.get Q.pointer.grant=some qNode)
    (bAt : Q.allocation.extra.nodes.get B.pointer.grant=some bNode)
    (qHidden : qNode.isExposed=false) (bHidden : bNode.isExposed=false) (bLeaf : bNode.children=#[])
    (different : B.pointer.grant≠Q.pointer.grant)
    (frame : FrameState) (ownedFrame : frame.protectedTags=#[(id,qNode.tag),(id,bNode.tag)])
    (original : UniIndex) (edge : Q.precise.completion.parents[B.pointer.grant.toNat]?=some (some original))
    (start amount boolStart : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (boolStartEq : boolStart.toNat=boolOffset)
    (positive : start.toNat<(start+amount).toNat) (boolPositive : boolStart.toNat<(boolStart+1).toNat)
    (noWrap : (start+amount).toNat=start.toNat+amount.toNat) (boolNoWrap : (boolStart+1).toNat=boolStart.toNat+1)
    (disjoint : (start+amount).toNat≤boolStart.toNat ∨ (boolStart+1).toNat≤start.toNat)
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write start (start+amount))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra B.pointer.grant .Write boolStart (boolStart+1))
    (bOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority Q.allocation.extra Q.precise.completion tracker.global.protectedTags B.pointer.grant)
      boolStart (boolStart+1) Q.allocation.extra.locations)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (entryAllocation : entry.allocation=Q.allocation) :
    let first:=Q.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
    let second:=first.tree.releaseProtector bNode.tag tracker.global.protectedTags
    first.status=.Released ∧ second.status=.Released ∧
      DuplicatePrefixBorrowContract.RuntimeFacts second.tree (tracker.global.endCall frame) ∧
      ParentInterpretation second.tree Q.precise.completion ∧
      second.tree={Q.allocation.extra with locations:=second.tree.locations} ∧
      second.tree.locations.size=Q.allocation.extra.locations.size ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority second.tree Q.precise.completion
        (tracker.global.endCall frame).protectedTags original) boolStart (boolStart+1) second.tree.locations := by
  obtain ⟨qDone,qFrame,qRuntime,qParents,qCapacity,_⟩:=CurrentCallResourceRelease.release Q rfl runtime qConcrete distinct short
    qNode qAt qHidden start amount startEq amountEq positive noWrap qActive
  obtain ⟨bAfter,bActiveAfter⟩:=CurrentCallResourceReleaseFrame.preserve Q rfl runtime qConcrete distinct short
    qNode qAt qHidden start amount startEq amountEq positive noWrap qActive boolStart (boolStart+1) boolPositive disjoint
    (S05CompletedAncestryReadMutable.Authority Q.allocation.extra Q.precise.completion tracker.global.protectedTags B.pointer.grant)
    bOwned B.pointer.grant bNode bAt bLeaf bHidden different bActive
  let first:=Q.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
  let middle:={before with memory:=StackPopRelease.commitTree before.memory id entry first.tree}
  have bAfterOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority first.tree B.precise.completion tracker.global.protectedTags B.pointer.grant)
      boolStart (boolStart+1) first.tree.locations := by
    rw [completion,qFrame]
    exact bAfter
  obtain ⟨currentB,_,pointerEq,allocationEq,preciseEq⟩:=CurrentCallResourceReleaseInstall.window B rfl entry live
    (entryAllocation.trans allocation.symm) first.tree (by rw [allocation];exact qFrame) qRuntime
    (by rw [completion];exact qParents) (by rw [allocation];exact qCapacity)
    boolStart 1 boolStartEq rfl boolPositive (by simpa using boolNoWrap) bAfterOwned
  have bAtAfter : currentB.allocation.extra.nodes.get currentB.pointer.grant=some bNode := by
    rw [allocationEq,pointerEq]
    change first.tree.nodes.get B.pointer.grant=some bNode
    rw [qFrame]
    exact bAt
  obtain ⟨bDone,bFrame,bRuntime,bParents,bCapacity,bOwn⟩:=CurrentCallResourceRelease.release currentB rfl
    (by rw [allocationEq];exact qRuntime) (by rw [pointerEq];exact bConcrete)
    (by rw [allocationEq];change first.tree.roots.toList.Nodup;rw [qFrame];exact distinct)
    (by rw [allocationEq];change first.tree.nodes.size<65536;rw [qFrame];exact short)
    bNode bAtAfter bHidden boolStart 1 boolStartEq rfl boolPositive (by simpa using boolNoWrap)
    (by rw [allocationEq,pointerEq];exact bActiveAfter)
  simp only [allocationEq,preciseEq,pointerEq,Allocation.setExtra,Allocation.mapExtra] at bDone bFrame bRuntime bParents bCapacity bOwn
  let second:=first.tree.releaseProtector bNode.tag tracker.global.protectedTags
  have nodes : second.tree.nodes=Q.allocation.extra.nodes := by rw [bFrame,qFrame]
  have finalQ : second.tree.nodes.get Q.pointer.grant=some qNode := by rw [nodes];exact qAt
  have finalB : second.tree.nodes.get B.pointer.grant=some bNode := by rw [nodes];exact bAt
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame second.tree frame := by
    intro row member index node present sameTag
    rw [ownedFrame] at member
    change row∈[(id,qNode.tag),(id,bNode.tag)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same
    · subst row
      have one:=bRuntime.formed.allocator.nodeTags index node present
      have two:=bRuntime.formed.allocator.nodeTags Q.pointer.grant qNode finalQ
      rw [sameTag,two] at one
      have found:=Option.some.inj one
      subst index
      have equal:=Option.some.inj (present.symm.trans finalQ)
      subst node
      exact qHidden
    · subst row
      have one:=bRuntime.formed.allocator.nodeTags index node present
      have two:=bRuntime.formed.allocator.nodeTags B.pointer.grant bNode finalB
      rw [sameTag,two] at one
      have found:=Option.some.inj one
      subst index
      have equal:=Option.some.inj (present.symm.trans finalB)
      subst node
      exact bHidden
  have afterRuntime:=S05CompletedChildReanchor.runtime_end_call second.tree tracker.global frame bRuntime hiddenFrame
  have oldOwned:=S05CompletedChildReanchor.owned_end_call second.tree Q.precise.completion tracker.global frame id B.pointer.grant original bNode
    boolStart (boolStart+1) edge finalB (by rw [ownedFrame];simp) (by rw [completion] at bOwn;exact bOwn)
  exact ⟨qDone,bDone,afterRuntime,by rw [completion] at bParents;exact bParents,
    by rw [bFrame,qFrame],bCapacity.trans qCapacity,oldOwned⟩

theorem same_tree_plan {before tracker qData qOwner id offset length bData bOwner boolOffset}
    (Q : UniformWindow before tracker qData qOwner id offset length .mut)
    (B : UniformWindow before tracker bData bOwner id boolOffset 1 .ret)
    (allocation : B.allocation=Q.allocation) (completion : B.precise.completion=Q.precise.completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (distinct : Q.allocation.extra.roots.toList.Nodup) (short : Q.allocation.extra.nodes.size<65536)
    (qConcrete : ∃ suppliedId tag,Q.pointer.value.provenance=.concrete suppliedId tag)
    (bConcrete : ∃ suppliedId tag,B.pointer.value.provenance=.concrete suppliedId tag)
    (qNode bNode : TreeNode)
    (qAt : Q.allocation.extra.nodes.get Q.pointer.grant=some qNode)
    (bAt : Q.allocation.extra.nodes.get B.pointer.grant=some bNode)
    (qHidden : qNode.isExposed=false) (bHidden : bNode.isExposed=false) (bLeaf : bNode.children=#[])
    (different : B.pointer.grant≠Q.pointer.grant)
    (frame : FrameState) (ownedFrame : frame.protectedTags=#[(id,qNode.tag),(id,bNode.tag)])
    (original : UniIndex) (edge : Q.precise.completion.parents[B.pointer.grant.toNat]?=some (some original))
    (start amount boolStart : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (boolStartEq : boolStart.toNat=boolOffset)
    (positive : start.toNat<(start+amount).toNat) (boolPositive : boolStart.toNat<(boolStart+1).toNat)
    (noWrap : (start+amount).toNat=start.toNat+amount.toNat) (boolNoWrap : (boolStart+1).toNat=boolStart.toNat+1)
    (disjoint : (start+amount).toNat≤boolStart.toNat ∨ (boolStart+1).toNat≤start.toNat)
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write start (start+amount))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra B.pointer.grant .Write boolStart (boolStart+1))
    (bOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority Q.allocation.extra Q.precise.completion tracker.global.protectedTags B.pointer.grant)
      boolStart (boolStart+1) Q.allocation.extra.locations)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (entryAllocation : entry.allocation=Q.allocation) :
    let first:=Q.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
    let second:=first.tree.releaseProtector bNode.tag tracker.global.protectedTags
    let middle:=StackPopRelease.commitTree before.memory id entry first.tree
    let middleEntry:={entry with allocation:=entry.allocation.setExtra first.tree}
    let final:=StackPopRelease.commitTree middle id middleEntry second.tree
    StackPopRelease.Plan tracker.global.protectedTags frame.protectedTags.toList before.memory final ∧
      DuplicatePrefixBorrowContract.RuntimeFacts second.tree (tracker.global.endCall frame) ∧
      ParentInterpretation second.tree Q.precise.completion ∧
      second.tree={Q.allocation.extra with locations:=second.tree.locations} ∧
      second.tree.locations.size=Q.allocation.extra.locations.size ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority second.tree Q.precise.completion
        (tracker.global.endCall frame).protectedTags original) boolStart (boolStart+1) second.tree.locations := by
  obtain ⟨qDone,bDone,afterRuntime,parents,framed,capacity,owned⟩:=same_tree Q B allocation completion runtime distinct short qConcrete bConcrete
    qNode bNode qAt bAt qHidden bHidden bLeaf different frame ownedFrame original edge start amount boolStart startEq amountEq boolStartEq
    positive boolPositive noWrap boolNoWrap disjoint qActive bActive bOwned entry live entryAllocation
  let first:=Q.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
  let second:=first.tree.releaseProtector bNode.tag tracker.global.protectedTags
  have firstEq : entry.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags=⟨first.tree,.Released⟩ := by
    rw [entryAllocation]
    change first=⟨first.tree,.Released⟩
    have eta : first=⟨first.tree,first.status⟩:=by cases first;rfl
    rw [show first.status=.Released from qDone] at eta
    exact eta
  let middle:=StackPopRelease.commitTree before.memory id entry first.tree
  let middleEntry:={entry with allocation:=entry.allocation.setExtra first.tree}
  have secondEq : middleEntry.allocation.extra.releaseProtector bNode.tag tracker.global.protectedTags=⟨second.tree,.Released⟩ := by
    change second=⟨second.tree,.Released⟩
    have eta : second=⟨second.tree,second.status⟩:=by cases second;rfl
    rw [show second.status=.Released from bDone] at eta
    exact eta
  refine ⟨?_,afterRuntime,parents,framed,capacity,owned⟩
  rw [ownedFrame]
  exact StackPopRelease.Plan.live id qNode.tag entry first.tree [(id,bNode.tag)] before.memory _ live firstEq
    (StackPopRelease.Plan.live id bNode.tag middleEntry second.tree [] middle _
      (StackPopRelease.lookup_commit_same before.memory id entry first.tree) secondEq (.nil _))


/-- Distinct allocation rows still release under one common held-tag set.
The source tag's absence from the Bool graph is actual fresh-tag metadata. -/
theorem different_trees_plan {before tracker qData qOwner sourceId offset length bData bOwner boolId boolOffset}
    (Q : UniformWindow before tracker qData qOwner sourceId offset length .mut)
    (B : UniformWindow before tracker bData bOwner boolId boolOffset 1 .ret)
    (different : boolId≠sourceId)
    (qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (bRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (qDistinct : Q.allocation.extra.roots.toList.Nodup) (bDistinct : B.allocation.extra.roots.toList.Nodup)
    (qShort : Q.allocation.extra.nodes.size<65536) (bShort : B.allocation.extra.nodes.size<65536)
    (qConcrete : ∃ suppliedId tag,Q.pointer.value.provenance=.concrete suppliedId tag)
    (bConcrete : ∃ suppliedId tag,B.pointer.value.provenance=.concrete suppliedId tag)
    (qNode bNode : TreeNode) (qAt : Q.allocation.extra.nodes.get Q.pointer.grant=some qNode)
    (bAt : B.allocation.extra.nodes.get B.pointer.grant=some bNode)
    (qHidden : qNode.isExposed=false) (bHidden : bNode.isExposed=false)
    (qAbsent : ∀ index node,B.allocation.extra.nodes.get index=some node→node.tag≠qNode.tag)
    (frame : FrameState) (ownedFrame : frame.protectedTags=#[(sourceId,qNode.tag),(boolId,bNode.tag)])
    (original : UniIndex) (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original))
    (start amount boolStart : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (boolStartEq : boolStart.toNat=boolOffset)
    (positive : start.toNat<(start+amount).toNat) (boolPositive : boolStart.toNat<(boolStart+1).toNat)
    (noWrap : (start+amount).toNat=start.toNat+amount.toNat) (boolNoWrap : (boolStart+1).toNat=boolStart.toNat+1)
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write start (start+amount))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write boolStart (boolStart+1))
    (qEntry bEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (qLive : before.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,qEntry))
    (bLive : before.memory.live.find? (fun row=>row.1==boolId)=some (boolId,bEntry))
    (qAllocation : qEntry.allocation=Q.allocation) (bAllocation : bEntry.allocation=B.allocation) :
    let qResult:=Q.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
    let bResult:=B.allocation.extra.releaseProtector bNode.tag tracker.global.protectedTags
    let middle:=StackPopRelease.commitTree before.memory sourceId qEntry qResult.tree
    let final:=StackPopRelease.commitTree middle boolId bEntry bResult.tree
    StackPopRelease.Plan tracker.global.protectedTags frame.protectedTags.toList before.memory final ∧
      DuplicatePrefixBorrowContract.RuntimeFacts bResult.tree (tracker.global.endCall frame) ∧
      ParentInterpretation bResult.tree B.precise.completion ∧
      bResult.tree={B.allocation.extra with locations:=bResult.tree.locations} ∧
      bResult.tree.locations.size=B.allocation.extra.locations.size ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority bResult.tree B.precise.completion
        (tracker.global.endCall frame).protectedTags original) boolStart (boolStart+1) bResult.tree.locations := by
  obtain ⟨qDone,_,_,_,_,_⟩:=CurrentCallResourceRelease.release Q rfl qRuntime qConcrete qDistinct qShort
    qNode qAt qHidden start amount startEq amountEq positive noWrap qActive
  let qResult:=Q.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
  let middle:=StackPopRelease.commitTree before.memory sourceId qEntry qResult.tree
  let post:={before with memory:=middle}
  have bLiveAfter:=StackPopRelease.lookup_commit_other before.memory sourceId boolId qEntry bEntry qResult.tree different bLive
  have bPresent : Present (ActualWorld post) boolId B.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(boolId,bEntry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some bLiveAfter),by simp only [bAllocation]⟩
  have sameExtra : B.allocation.setExtra B.allocation.extra=B.allocation := by
    cases B.allocation
    rfl
  let currentB : UniformWindow post tracker bData bOwner boolId boolOffset 1 .ret := {B with
    present:=bPresent,
    issued:=by
      have issued:=CurrentCallResourceInstallation.spatial_frame B.issued post tracker B.allocation.extra
        (by simpa only [sameExtra] using bPresent) rfl rfl
        (by intro position root found;exact found)
        (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
        B.precise.completion (by intro root origin edge;exact edge)
      simpa only [sameExtra] using issued}
  obtain ⟨bDone,bFrame,afterRuntime,parents,capacity,owned⟩:=CurrentCallResourceRelease.release currentB rfl bRuntime bConcrete bDistinct bShort
    bNode bAt bHidden boolStart 1 boolStartEq rfl boolPositive (by simpa using boolNoWrap) bActive
  let bResult:=B.allocation.extra.releaseProtector bNode.tag tracker.global.protectedTags
  have finalB : bResult.tree.nodes.get B.pointer.grant=some bNode := by rw [bFrame];exact bAt
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame bResult.tree frame := by
    intro row member index node present sameTag
    rw [ownedFrame] at member
    change row∈[(sourceId,qNode.tag),(boolId,bNode.tag)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same
    · subst row
      have old : B.allocation.extra.nodes.get index=some node := by rw [bFrame] at present;exact present
      exact False.elim ((qAbsent index node old) sameTag)
    · subst row
      have one:=afterRuntime.formed.allocator.nodeTags index node present
      have two:=afterRuntime.formed.allocator.nodeTags B.pointer.grant bNode finalB
      rw [sameTag,two] at one
      have found:=Option.some.inj one
      subst index
      have equal:=Option.some.inj (present.symm.trans finalB)
      subst node
      exact bHidden
  have finalRuntime:=S05CompletedChildReanchor.runtime_end_call bResult.tree tracker.global frame afterRuntime hiddenFrame
  have finalOwned:=S05CompletedChildReanchor.owned_end_call bResult.tree B.precise.completion tracker.global frame boolId B.pointer.grant original bNode
    boolStart (boolStart+1) edge finalB (by rw [ownedFrame];simp) owned
  have firstEq : qEntry.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags=⟨qResult.tree,.Released⟩ := by
    rw [qAllocation]
    change qResult=⟨qResult.tree,.Released⟩
    have eta : qResult=⟨qResult.tree,qResult.status⟩:=by cases qResult;rfl
    rw [show qResult.status=.Released from qDone] at eta
    exact eta
  have secondEq : bEntry.allocation.extra.releaseProtector bNode.tag tracker.global.protectedTags=⟨bResult.tree,.Released⟩ := by
    rw [bAllocation]
    change bResult=⟨bResult.tree,.Released⟩
    have eta : bResult=⟨bResult.tree,bResult.status⟩:=by cases bResult;rfl
    rw [show bResult.status=.Released from bDone] at eta
    exact eta
  refine ⟨?_,finalRuntime,parents,bFrame,capacity,finalOwned⟩
  rw [ownedFrame]
  exact StackPopRelease.Plan.live sourceId qNode.tag qEntry qResult.tree [(boolId,bNode.tag)] before.memory _ qLive firstEq
    (StackPopRelease.Plan.live boolId bNode.tag bEntry bResult.tree [] middle _ bLiveAfter secondEq (.nil _))

end
end DuplicatePrefix.CurrentCallResourceRootRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceRootRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource root-release dependency {dependency}"
