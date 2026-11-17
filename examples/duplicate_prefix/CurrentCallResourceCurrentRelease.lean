import duplicate_prefix.CurrentCallResourceRootRelease
namespace DuplicatePrefix.CurrentCallResourceCurrentRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private def at_id {machine held identities owner oldId lower length mode}
    (B : UniformWindow machine held identities owner oldId lower length mode) (newId : AllocId) (same : oldId=newId) :
    UniformWindow machine held identities owner newId lower length mode where
  loan:=B.loan;pointer:=B.pointer;allocation:=B.allocation;precise:=B.precise
  loanAt:=B.loanAt;pointerAt:=B.pointerAt;pointerId:=B.pointerId.trans same
  present:=by rw [←same];exact B.present
  preciseAt:=by rw [←same];exact B.preciseAt
  binding:=B.binding
  issued:=by rw [←same];exact B.issued
  parents:=B.parents
  window:=by intro byte inside;exact B.window byte (by simpa only [same] using inside)


structure Released {before tracker bData bOwner boolId boolOffset}
    (B : UniformWindow before tracker bData bOwner boolId boolOffset 1 .ret)
    (frame : FrameState) (original : UniIndex) (start : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) where
  memory : MemoryState Provenance BorrowTree MiriMemoryKind
  tree : BorrowTree
  plan : StackPopRelease.Plan tracker.global.protectedTags frame.protectedTags.toList before.memory memory
  live : memory.live.find? (fun row=>row.1==boolId)=some (boolId,{entry with allocation:=B.allocation.setExtra tree})
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree (tracker.global.endCall frame)
  parents : ParentInterpretation tree B.precise.completion
  shape : tree={B.allocation.extra with locations:=tree.locations}
  capacity : tree.locations.size=B.allocation.extra.locations.size
  distinct : tree.roots.toList.Nodup
  short : tree.nodes.size<65536
  owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree B.precise.completion
    (tracker.global.endCall frame).protectedTags original) start (start+1) tree.locations

/-- Current semantic q/B resources construct both real release passes and their
actual heap commits. The two releases use the same still-held protector table. -/
theorem release {before tracker qData qOwner id offset length bData bOwner boolId boolOffset}
    (Q : UniformWindow before tracker qData qOwner id offset length .mut)
    (B : UniformWindow before tracker bData bOwner boolId boolOffset 1 .ret)
    (sameAllocation : boolId=id→B.allocation=Q.allocation)
    (sameCompletion : boolId=id→B.precise.completion=Q.precise.completion)
    (qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (bRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (qDistinct : Q.allocation.extra.roots.toList.Nodup) (bDistinct : B.allocation.extra.roots.toList.Nodup)
    (qShort : Q.allocation.extra.nodes.size<65536) (bShort : B.allocation.extra.nodes.size<65536)
    (qConcrete : ∃ suppliedId tag,Q.pointer.value.provenance=.concrete suppliedId tag)
    (bConcrete : ∃ suppliedId tag,B.pointer.value.provenance=.concrete suppliedId tag)
    (qNode bNode : TreeNode)
    (qAt : Q.allocation.extra.nodes.get Q.pointer.grant=some qNode)
    (bAt : B.allocation.extra.nodes.get B.pointer.grant=some bNode)
    (qHidden : qNode.isExposed=false) (bHidden : bNode.isExposed=false) (bLeaf : bNode.children=#[])
    (tags : qNode.tag≠bNode.tag)
    (absent : boolId≠id→∀index node,B.allocation.extra.nodes.get index=some node→node.tag≠qNode.tag)
    (frame : FrameState) (ownedFrame : frame.protectedTags=#[(id,qNode.tag),(boolId,bNode.tag)])
    (original : UniIndex) (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original))
    (start amount boolStart : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (boolStartEq : boolStart.toNat=boolOffset)
    (positive : start.toNat<(start+amount).toNat) (boolPositive : boolStart.toNat<(boolStart+1).toNat)
    (noWrap : (start+amount).toNat=start.toNat+amount.toNat) (boolNoWrap : (boolStart+1).toNat=boolStart.toNat+1)
    (separate : boolId=id→(start+amount).toNat≤boolStart.toNat ∨ (boolStart+1).toNat≤start.toNat)
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write start (start+amount))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write boolStart (boolStart+1))
    (bOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority B.allocation.extra B.precise.completion tracker.global.protectedTags B.pointer.grant)
      boolStart (boolStart+1) B.allocation.extra.locations)
    (qEntry bEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (qLive : before.memory.live.find? (fun row=>row.1==id)=some (id,qEntry))
    (bLive : before.memory.live.find? (fun row=>row.1==boolId)=some (boolId,bEntry))
    (qAllocation : qEntry.allocation=Q.allocation) (bAllocation : bEntry.allocation=B.allocation) :
    Nonempty (Released B frame original boolStart bEntry) := by
  by_cases same : boolId=id
  · let sameB:=at_id B id same
    have allocation : sameB.allocation=Q.allocation:=sameAllocation same
    have completion : sameB.precise.completion=Q.precise.completion:=sameCompletion same
    have bAtQ : Q.allocation.extra.nodes.get sameB.pointer.grant=some bNode:=by rw [←allocation];exact bAt
    have different : sameB.pointer.grant≠Q.pointer.grant:=by
      intro eq
      rw [eq] at bAtQ
      exact tags (congrArg TreeNode.tag (Option.some.inj (qAt.symm.trans bAtQ)))
    obtain ⟨plan,runtime,parents,shape,capacity,owned⟩:=CurrentCallResourceRootRelease.same_tree_plan Q sameB allocation completion
      qRuntime qDistinct qShort qConcrete bConcrete qNode bNode qAt bAtQ qHidden bHidden bLeaf different frame
      (by simpa only [same] using ownedFrame) original (by rw [←completion];exact edge)
      start amount boolStart startEq amountEq boolStartEq positive boolPositive noWrap boolNoWrap (separate same)
      qActive (by rw [←allocation];exact bActive)
      (by rw [←allocation,←completion];exact bOwned) qEntry qLive qAllocation
    let first:=Q.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
    let second:=first.tree.releaseProtector bNode.tag tracker.global.protectedTags
    let middle:=StackPopRelease.commitTree before.memory id qEntry first.tree
    let middleEntry:={qEntry with allocation:=qEntry.allocation.setExtra first.tree}
    let final:=StackPopRelease.commitTree middle id middleEntry second.tree
    refine ⟨⟨final,second.tree,?_,?_,runtime,?_,?_,?_,?_,?_,?_⟩⟩
    · simpa only [same] using plan
    · have entryEq:qEntry=bEntry:=by
        have live:=bLive
        rw [same] at live
        exact (Prod.mk.inj (Option.some.inj (qLive.symm.trans live))).2
      have found:=StackPopRelease.lookup_commit_same middle id middleEntry second.tree
      have finalEntry : {middleEntry with allocation:=middleEntry.allocation.setExtra second.tree}=
          {bEntry with allocation:=B.allocation.setExtra second.tree}:=by
        dsimp only [middleEntry]
        rw [entryEq,bAllocation]
        rfl
      simpa only [same,finalEntry] using found
    · rw [←completion] at parents;exact parents
    · calc
        second.tree={Q.allocation.extra with locations:=second.tree.locations}:=shape
        _={B.allocation.extra with locations:=second.tree.locations}:=by rw [←allocation];rfl
    · exact capacity.trans (congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.locations.size) allocation.symm)
    · rw [shape];exact qDistinct
    · rw [shape];exact qShort
    · rw [←completion] at owned;exact owned
  · obtain ⟨plan,runtime,parents,shape,capacity,owned⟩:=CurrentCallResourceRootRelease.different_trees_plan Q B same
      qRuntime bRuntime qDistinct bDistinct qShort bShort qConcrete bConcrete qNode bNode qAt bAt qHidden bHidden (absent same)
      frame ownedFrame original edge start amount boolStart startEq amountEq boolStartEq positive boolPositive noWrap boolNoWrap
      qActive bActive qEntry bEntry qLive bLive qAllocation bAllocation
    let first:=Q.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
    let second:=B.allocation.extra.releaseProtector bNode.tag tracker.global.protectedTags
    let middle:=StackPopRelease.commitTree before.memory id qEntry first.tree
    let final:=StackPopRelease.commitTree middle boolId bEntry second.tree
    refine ⟨⟨final,second.tree,plan,?_,runtime,parents,shape,capacity,?_,?_,owned⟩⟩
    · simpa only [bAllocation] using StackPopRelease.lookup_commit_same middle boolId bEntry second.tree
    · rw [shape];exact bDistinct
    · rw [shape];exact bShort
end
end DuplicatePrefix.CurrentCallResourceCurrentRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceCurrentRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current resource release dependency {dependency}"
