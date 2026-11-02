import duplicate_prefix.CurrentCallSpatialRootRelease
import duplicate_prefix.CurrentCallResourceCurrentRelease
namespace DuplicatePrefix.CurrentCallSpatialCurrentRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralRangeMapOrigins CurrentCallSpatialCover
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
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


/-- Current semantic q/B resources construct both real release passes and their
actual heap commits. The two releases use the same still-held protector table. -/
theorem release {before tracker qCtx offset length bData bOwner boolId boolOffset}
    (Q : RoleCover before tracker qCtx .mut offset length)
    (B : UniformWindow before tracker bData bOwner boolId boolOffset 1 .ret)
    (sameAllocation : boolId=Q.backing.id→B.allocation=Q.backing.allocation)
    (qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.backing.allocation.extra tracker.global)
    (bRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (qDistinct : Q.backing.allocation.extra.roots.toList.Nodup) (bDistinct : B.allocation.extra.roots.toList.Nodup)
    (qShort : Q.backing.allocation.extra.nodes.size<65536) (bShort : B.allocation.extra.nodes.size<65536)
    (bConcrete : ∃ suppliedId tag,B.pointer.value.provenance=.concrete suppliedId tag)
    (anchor : UniIndex) (qNode bNode : TreeNode)
    (qConcrete : Q.family.value.provenance=.concrete Q.backing.id qNode.tag)
    (qAt : Q.backing.allocation.extra.nodes.get anchor=some qNode)
    (bAt : B.allocation.extra.nodes.get B.pointer.grant=some bNode)
    (qHidden : qNode.isExposed=false) (bHidden : bNode.isExposed=false) (bLeaf : bNode.children=#[])
    (tags : qNode.tag≠bNode.tag)
    (absent : boolId≠Q.backing.id→∀index node,B.allocation.extra.nodes.get index=some node→node.tag≠qNode.tag)
    (frame : FrameState) (ownedFrame : frame.protectedTags=#[(Q.backing.id,qNode.tag),(boolId,bNode.tag)])
    (original : UniIndex) (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original))
    (start amount boolStart : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (boolStartEq : boolStart.toNat=boolOffset)
    (positive : start.toNat<(start+amount).toNat) (boolPositive : boolStart.toNat<(boolStart+1).toNat)
    (noWrap : (start+amount).toNat=start.toNat+amount.toNat) (boolNoWrap : (boolStart+1).toNat=boolStart.toNat+1)
    (separate : boolId=Q.backing.id→(start+amount).toNat≤boolStart.toNat ∨ (boolStart+1).toNat≤start.toNat)
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.backing.allocation.extra anchor .Write start (start+amount))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write boolStart (boolStart+1))
    (bOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority B.allocation.extra B.precise.completion tracker.global.protectedTags B.pointer.grant)
      boolStart (boolStart+1) B.allocation.extra.locations)
    (qEntry bEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (qLive : before.memory.live.find? (fun row=>row.1==Q.backing.id)=some (Q.backing.id,qEntry))
    (bLive : before.memory.live.find? (fun row=>row.1==boolId)=some (boolId,bEntry))
    (qAllocation : qEntry.allocation=Q.backing.allocation) (bAllocation : bEntry.allocation=B.allocation) :
    Nonempty (CurrentCallResourceCurrentRelease.Released B frame original boolStart bEntry) := by
  by_cases same : boolId=Q.backing.id
  · let sameB:=at_id B Q.backing.id same
    have allocation : sameB.allocation=Q.backing.allocation:=sameAllocation same
    have bAtQ : Q.backing.allocation.extra.nodes.get sameB.pointer.grant=some bNode:=by rw [←allocation];exact bAt
    have different : sameB.pointer.grant≠anchor:=by
      intro eq
      rw [eq] at bAtQ
      exact tags (congrArg TreeNode.tag (Option.some.inj (qAt.symm.trans bAtQ)))
    obtain ⟨plan,runtime,parents,shape,capacity,owned⟩:=CurrentCallSpatialRootRelease.same_tree_plan Q sameB allocation
      qRuntime qDistinct qShort bConcrete anchor qNode bNode qConcrete qAt bAtQ qHidden bHidden bLeaf different frame
      (by simpa only [same] using ownedFrame) original edge
      start amount boolStart startEq amountEq boolStartEq positive boolPositive noWrap boolNoWrap (separate same)
      qActive (by rw [←allocation];exact bActive)
      (by rw [←allocation];exact bOwned) qEntry qLive qAllocation
    let first:=Q.backing.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
    let second:=first.tree.releaseProtector bNode.tag tracker.global.protectedTags
    let middle:=StackPopRelease.commitTree before.memory Q.backing.id qEntry first.tree
    let middleEntry:={qEntry with allocation:=qEntry.allocation.setExtra first.tree}
    let final:=StackPopRelease.commitTree middle Q.backing.id middleEntry second.tree
    refine ⟨⟨final,second.tree,?_,?_,runtime,?_,?_,?_,?_,?_,?_⟩⟩
    · simpa only [same] using plan
    · have entryEq:qEntry=bEntry:=by
        have live:=bLive
        rw [same] at live
        exact (Prod.mk.inj (Option.some.inj (qLive.symm.trans live))).2
      have found:=StackPopRelease.lookup_commit_same middle Q.backing.id middleEntry second.tree
      have finalEntry : {middleEntry with allocation:=middleEntry.allocation.setExtra second.tree}=
          {bEntry with allocation:=B.allocation.setExtra second.tree}:=by
        dsimp only [middleEntry]
        rw [entryEq,bAllocation]
        rfl
      simpa only [same,finalEntry] using found
    · exact parents
    · calc
        second.tree={Q.backing.allocation.extra with locations:=second.tree.locations}:=shape
        _={B.allocation.extra with locations:=second.tree.locations}:=by rw [←allocation];rfl
    · exact capacity.trans (congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.locations.size) allocation.symm)
    · rw [shape];exact qDistinct
    · rw [shape];exact qShort
    · exact owned
  · obtain ⟨plan,runtime,parents,shape,capacity,owned⟩:=CurrentCallSpatialRootRelease.different_trees_plan Q B same
      qRuntime bRuntime qDistinct bDistinct qShort bShort bConcrete anchor qNode bNode qConcrete qAt bAt qHidden bHidden (absent same)
      frame ownedFrame original edge start amount boolStart startEq amountEq boolStartEq positive boolPositive noWrap boolNoWrap
      qActive bActive qEntry bEntry qLive bLive qAllocation bAllocation
    let first:=Q.backing.allocation.extra.releaseProtector qNode.tag tracker.global.protectedTags
    let second:=B.allocation.extra.releaseProtector bNode.tag tracker.global.protectedTags
    let middle:=StackPopRelease.commitTree before.memory Q.backing.id qEntry first.tree
    let final:=StackPopRelease.commitTree middle boolId bEntry second.tree
    refine ⟨⟨final,second.tree,plan,?_,runtime,parents,shape,capacity,?_,?_,owned⟩⟩
    · simpa only [bAllocation] using StackPopRelease.lookup_commit_same middle boolId bEntry second.tree
    · rw [shape];exact bDistinct
    · rw [shape];exact bShort
end
end DuplicatePrefix.CurrentCallSpatialCurrentRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialCurrentRelease.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial current release dependency {dependency}"
