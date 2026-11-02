import duplicate_prefix.CurrentCallResourceRootRelease
import duplicate_prefix.CurrentCallResourceBodyReadiness
import duplicate_prefix.CurrentCallResourceBoolCurrent
import duplicate_prefix.CurrentCallResourceBoolTagSeparation
import duplicate_prefix.CurrentCallResourceSourceActivity

namespace DuplicatePrefix.CurrentCallResourceEntryRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralRangeMapOrigins CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

def borrowFrame : FrameState := (C.borrowFrame.addProtector id tracker.global.nextPointerTag).addProtector out.physical.id out.sourceOutput.global.nextPointerTag

structure Released where
  memory : MemoryState Provenance BorrowTree MiriMemoryKind
  tree : BorrowTree
  plan : StackPopRelease.Plan out.boolOutput.global.protectedTags (borrowFrame out).protectedTags.toList out.finalMachine.memory memory
  live : memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,{out.physical.entry with allocation:=out.updated.setExtra tree})
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree (out.boolOutput.global.endCall (borrowFrame out))
  parents : ParentInterpretation tree (CurrentCallResourceBoolCurrent.completion out)
  shape : tree={out.updated.extra with locations:=tree.locations}
  capacity : tree.locations.size=out.updated.extra.locations.size
  distinct : tree.roots.toList.Nodup
  short : tree.nodes.size<65536
  owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree (CurrentCallResourceBoolCurrent.completion out)
    (out.boolOutput.global.endCall (borrowFrame out)).protectedTags C.V.pointer.grant)
    out.physical.offset (out.physical.offset+1) tree.locations

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

/-- The entry's exact q/B resource outputs derive the real sequential pop Plan;
no completion, operation-status or future-write package is a caller premise. -/
theorem release (ready : CurrentCallResourceBodyReadiness.Ready C) (empty : C.borrowFrame={}) : Nonempty (Released out) := by
  obtain ⟨qData,qOwner,Q,qPointer,qAllocation,qCompletion⟩:=CurrentCallResourceSourceFinal.current out
  obtain ⟨bData,bOwner,B,bPointer,bAllocation,bCompletion⟩:=CurrentCallResourceBoolCurrent.current out
  obtain ⟨qNode,qFound,qTag,qLeaf,qHidden,qActivity⟩:=CurrentCallResourceSourceActivity.current out
  have bFacets:=CurrentCallResourceBoolFacets.current out
  have qGrant : Q.pointer.grant=out.sourceChild:=by rw [qPointer];rfl
  have bGrant : B.pointer.grant=out.boolChild:=by rw [bPointer];rfl
  have qAt : Q.allocation.extra.nodes.get Q.pointer.grant=some qNode:=by rw [qAllocation,qGrant];exact qFound
  have bAt : B.allocation.extra.nodes.get B.pointer.grant=some out.boolNode:=by rw [bAllocation,bGrant];exact (CurrentCallResourceBoolFacets.node out).1
  have qActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len):=by rw [qAllocation,qGrant];exact qActivity
  have bActive : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write out.physical.offset (out.physical.offset+1):=by rw [bAllocation,bGrant];exact bFacets.2.2.2
  have qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra out.boolOutput.global:=by rw [qAllocation];exact CurrentCallResourceSourceFinal.runtime out
  have qDistinct : Q.allocation.extra.roots.toList.Nodup:=by rw [qAllocation];exact CurrentCallResourceSourceFinal.roots out
  have qShort : Q.allocation.extra.nodes.size<65536:=by rw [qAllocation];exact CurrentCallResourceBodyReadiness.current_short out ready
  have bRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra out.boolOutput.global:=by rw [bAllocation];exact out.afterRuntime
  have bDistinct : B.allocation.extra.roots.toList.Nodup:=by
    rw [bAllocation]
    exact out.finalRoots (out.physical.id,{out.physical.entry with allocation:=out.updated})
      (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (CurrentCallResourceBoolCurrent.live out)))
  have qConcrete : ∃ suppliedId tag,Q.pointer.value.provenance=.concrete suppliedId tag:=⟨id,out.sourceOutput.tag,by rw [qPointer];rfl⟩
  have bConcrete : ∃ suppliedId tag,B.pointer.value.provenance=.concrete suppliedId tag:=⟨out.physical.id,out.boolOutput.tag,by rw [bPointer];rfl⟩
  have last:=(Q.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have extent:=Q.issued.capability.extent
  have sizeLimit:=UInt64.toNat_lt Q.allocation.byteSize.bytes
  have sumSmall : offset+len.toNat<2^64:=by have p:=C.positive;omega
  have startEq : (UInt64.ofNat offset).toNat=offset:=by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by have p:=C.positive;omega : offset<2^64)]
  have noWrap : (UInt64.ofNat offset+len).toNat=(UInt64.ofNat offset).toNat+len.toNat:=by simp only [UInt64.toNat_add,startEq,Nat.mod_eq_of_lt sumSmall]
  have positive : (UInt64.ofNat offset).toNat<(UInt64.ofNat offset+len).toNat:=by rw [noWrap];have p:=C.positive;omega
  have boolNoWrap : (out.physical.offset+1).toNat=out.physical.offset.toNat+1:=by
    have bounds:=out.physical.bounds
    have limit:=out.physical.capacity.toNat_lt
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega : out.physical.offset.toNat+1<2^64)]
  have boolPositive : out.physical.offset.toNat<(out.physical.offset+1).toNat:=by omega
  have ownedFrame : (borrowFrame out).protectedTags=#[(id,qNode.tag),(out.physical.id,out.boolNode.tag)]:=by
    rw [qTag,out.sourceTag,bFacets.2.2.1]
    simp only [borrowFrame,empty,FrameState.addProtector]
    rfl
  let qEntry:=CurrentCallResourceSourceFinal.entry out
  let bEntry:={out.physical.entry with allocation:=out.updated}
  have qLive:=CurrentCallResourceSourceFinal.live out
  have bLive:=CurrentCallResourceBoolCurrent.live out
  by_cases same : out.physical.id=id
  · let sameB:=at_id B id same
    have allocation : sameB.allocation=Q.allocation:=by
      change B.allocation=Q.allocation
      rw [bAllocation,qAllocation,CurrentCallResourceSourceFinal.entry,ite_eq_left same]
    have completion : sameB.precise.completion=Q.precise.completion:=by
      change B.precise.completion=Q.precise.completion
      rw [bCompletion,qCompletion,CurrentCallResourceSourceFinal.completion,ite_eq_left same]
      rfl
    have qC : Q.precise.completion=CurrentCallResourceBoolCurrent.completion out:=by
      rw [qCompletion,CurrentCallResourceSourceFinal.completion,ite_eq_left same]
      rfl
    have bAtQ : Q.allocation.extra.nodes.get sameB.pointer.grant=some out.boolNode:=by rw [←allocation];exact bAt
    have qOlder:=GeneralBorrowParentTagInvariant.parent_below_fresh out.sourceOutput.child.tree out.sourceOutput.global out.sourceWitness.runtime
      out.sourceChild out.sourceWitness.node out.sourceWitness.nodeAt
    rw [out.sourceWitness.tag] at qOlder
    have different : sameB.pointer.grant≠Q.pointer.grant:=by
      intro eq
      rw [eq] at bAtQ
      have nodeEq:=Option.some.inj (qAt.symm.trans bAtQ)
      have tags:=congrArg TreeNode.tag nodeEq
      rw [qTag,bFacets.2.2.1] at tags
      rw [tags] at qOlder
      exact Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp qOlder)
    have disjoint : (UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat ∨ (out.physical.offset+1).toNat≤(UInt64.ofNat offset).toNat:=by
      by_cases left : (UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat
      · exact .inl left
      · apply Or.inr
        apply Nat.le_of_not_gt
        intro overlap
        have originalSame:=out.physicalId.symm.trans same
        have separation:=C.separate originalSame
        exact separation (id,out.physical.offset.toNat) ⟨rfl,by omega,by omega⟩
          ⟨originalSame.symm,by rw [out.physicalOffset];exact Nat.le_refl _,by rw [out.physicalOffset];omega⟩
    have bOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority Q.allocation.extra Q.precise.completion out.boolOutput.global.protectedTags sameB.pointer.grant)
        out.physical.offset (out.physical.offset+1) Q.allocation.extra.locations:=by
      change OwnedOn (S05CompletedAncestryReadMutable.Authority Q.allocation.extra Q.precise.completion out.boolOutput.global.protectedTags B.pointer.grant) _ _ _
      rw [←allocation]
      change OwnedOn (S05CompletedAncestryReadMutable.Authority B.allocation.extra Q.precise.completion out.boolOutput.global.protectedTags B.pointer.grant) _ _ B.allocation.extra.locations
      rw [bAllocation,qC,bGrant]
      exact out.afterOwned
    have edge : Q.precise.completion.parents[sameB.pointer.grant.toNat]?=some (some C.V.pointer.grant):=by
      change Q.precise.completion.parents[B.pointer.grant.toNat]?=some (some C.V.pointer.grant)
      rw [qC,bGrant]
      exact S05ConcreteProtectedChildCompletion.child_edge _ _ _
    obtain ⟨plan,runtime,parents,shape,capacity,owned⟩:=CurrentCallResourceRootRelease.same_tree_plan Q sameB allocation completion qRuntime qDistinct qShort qConcrete bConcrete
      qNode out.boolNode qAt bAtQ qHidden bFacets.2.1 bFacets.1 different (borrowFrame out)
      (by simpa only [same] using ownedFrame) C.V.pointer.grant edge (UInt64.ofNat offset) len out.physical.offset startEq rfl rfl
      positive boolPositive noWrap (by simpa using boolNoWrap) disjoint qActive
      (by rw [←allocation];exact bActive) bOwned qEntry qLive qAllocation.symm
    let first:=Q.allocation.extra.releaseProtector qNode.tag out.boolOutput.global.protectedTags
    let second:=first.tree.releaseProtector out.boolNode.tag out.boolOutput.global.protectedTags
    let middle:=StackPopRelease.commitTree out.finalMachine.memory id qEntry first.tree
    let middleEntry:={qEntry with allocation:=qEntry.allocation.setExtra first.tree}
    let final:=StackPopRelease.commitTree middle id middleEntry second.tree
    refine ⟨⟨final,second.tree,plan,?_,runtime,by rw [qC] at parents;exact parents,?_,?_,?_,?_,by rw [qC] at owned;exact owned⟩⟩
    · have found:=StackPopRelease.lookup_commit_same middle id middleEntry second.tree
      have entryEq : {middleEntry with allocation:=middleEntry.allocation.setExtra second.tree}={out.physical.entry with allocation:=out.updated.setExtra second.tree}:=by
        dsimp only [middleEntry,qEntry]
        rw [CurrentCallResourceSourceFinal.entry,ite_eq_left same]
        cases out.updated
        rfl
      simpa only [same,entryEq] using found
    · rw [shape,qAllocation,CurrentCallResourceSourceFinal.entry,ite_eq_left same]
    · simpa only [first,second,qAllocation,CurrentCallResourceSourceFinal.entry,ite_eq_left same] using capacity
    · rw [shape];exact qDistinct
    · rw [shape];exact qShort
  · have bShort : B.allocation.extra.nodes.size<65536:=by
      rw [bAllocation,out.updatedNodes]
      have growth:=CurrentCallResourceEntryFacets.bool_growth out
      have unchanged:=out.otherTree (by intro oldSame;exact same (out.physicalId.trans oldSame))
      rw [unchanged.1] at growth
      have initial:=C.boolRoom
      omega
    have edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some C.V.pointer.grant):=by
      rw [bCompletion,bGrant]
      exact S05ConcreteProtectedChildCompletion.child_edge _ _ _
    have absent : ∀ index node,B.allocation.extra.nodes.get index=some node→node.tag≠qNode.tag:=by
      intro index node found
      rw [bAllocation] at found
      rw [qTag]
      exact CurrentCallResourceBoolTagSeparation.absent out same index node found
    obtain ⟨plan,runtime,parents,shape,capacity,owned⟩:=CurrentCallResourceRootRelease.different_trees_plan Q B same qRuntime bRuntime qDistinct bDistinct qShort bShort qConcrete bConcrete
      qNode out.boolNode qAt bAt qHidden bFacets.2.1 absent (borrowFrame out) ownedFrame C.V.pointer.grant edge (UInt64.ofNat offset) len out.physical.offset
      startEq rfl rfl positive boolPositive noWrap (by simpa using boolNoWrap) qActive bActive qEntry bEntry qLive bLive qAllocation.symm bAllocation.symm
    let first:=Q.allocation.extra.releaseProtector qNode.tag out.boolOutput.global.protectedTags
    let second:=B.allocation.extra.releaseProtector out.boolNode.tag out.boolOutput.global.protectedTags
    let middle:=StackPopRelease.commitTree out.finalMachine.memory id qEntry first.tree
    let final:=StackPopRelease.commitTree middle out.physical.id bEntry second.tree
    refine ⟨⟨final,second.tree,plan,?_,runtime,by rw [bCompletion] at parents;exact parents,?_,?_,?_,?_,by rw [bCompletion] at owned;exact owned⟩⟩
    · exact StackPopRelease.lookup_commit_same middle out.physical.id bEntry second.tree
    · simpa only [second,bAllocation] using shape
    · simpa only [second,bAllocation] using capacity
    · rw [shape];exact bDistinct
    · rw [shape];exact bShort

end
end DuplicatePrefix.CurrentCallResourceEntryRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceEntryRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual entry-release dependency {dependency}"
