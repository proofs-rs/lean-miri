import duplicate_prefix.CurrentCallResourceCurrentRelease
import duplicate_prefix.CurrentCallResourceAsMut
import duplicate_prefix.CurrentCallResourceLenRoots
import duplicate_prefix.CurrentCallResourceLenActivity
import duplicate_prefix.CurrentCallResourceLenBoolCurrent
import duplicate_prefix.CurrentCallResourceEntryRelease
namespace DuplicatePrefix.CurrentCallResourceLenRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C) {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage)

theorem release (empty : C.borrowFrame={}) :
    ∃ bData bOwner,
    ∃ B : UniformWindow returned.machine (CurrentCallResourceLenReturn.postTracker out ready) bData bOwner out.physical.id out.physical.offset.toNat 1 .ret,
      B.pointer=CurrentCallResourceBoolCurrent.pointer out ∧
      B.allocation=CurrentCallResourceLenBoolCurrent.allocation out ready ∧
      B.precise.completion=CurrentCallResourceLenBoolCurrent.completion out ready returned ∧
      Nonempty (CurrentCallResourceCurrentRelease.Released B (CurrentCallResourceEntryRelease.borrowFrame out)
        C.V.pointer.grant out.physical.offset (CurrentCallResourceLenBoolCurrent.entry out ready)) := by
  obtain ⟨qData,qOwner,current,qPointer,qAllocation,qCompletion⟩:=CurrentCallResourceAsMut.current out ready returned
  obtain ⟨bData,bOwner,B,bPointer,bAllocation,bCompletion⟩:=CurrentCallResourceLenBoolCurrent.current out ready returned
  obtain ⟨qHidden,qActivity⟩:=CurrentCallResourceLenActivity.current out ready returned
  obtain ⟨_,bOwned,⟨bNode,bFound,bTag,bParent,bLeaf,bHidden⟩,bActivity⟩:=CurrentCallResourceLenBoolFrame.result out ready returned
  have sourceExtra : (CurrentCallResourceLenCapability.sourceAllocation out ready).extra=CurrentCallResourceLenReturn.releasedTree out ready:=by
    simp only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra]
  have qTree : current.allocation.extra=CurrentCallResourceLenReturn.releasedTree out ready:=
    (congrArg Allocation.extra qAllocation).trans sourceExtra
  have qGrant : current.pointer.grant=out.sourceChild:=by rw [qPointer,returned.sourcePointer];rfl
  have bGrant : B.pointer.grant=out.boolChild:=by rw [bPointer];rfl
  have qAt : current.allocation.extra.nodes.get current.pointer.grant=some returned.sourceNode:=by
    rw [qTree,qPointer]
    exact returned.sourceAt
  have bAt : B.allocation.extra.nodes.get B.pointer.grant=some bNode:=by rw [bAllocation,bGrant];exact bFound
  have qActive : GeneralBorrowFreshActiveWithin.ActiveWithin current.allocation.extra current.pointer.grant .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len):=by
    rw [qTree,qGrant];exact qActivity
  have bActive : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write out.physical.offset (out.physical.offset+1):=by
    rw [bAllocation,bGrant];exact bActivity
  have qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts current.allocation.extra (CurrentCallResourceLenReturn.postTracker out ready).global:=by rw [qTree];exact returned.runtime
  have qDistinct : current.allocation.extra.roots.toList.Nodup:=by rw [qTree];exact CurrentCallResourceLenRoots.rootsDistinct out ready returned
  have qShort : current.allocation.extra.nodes.size<65536:=by rw [qTree];exact returned.short
  have bRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra (CurrentCallResourceLenReturn.postTracker out ready).global:=by rw [bAllocation];exact CurrentCallResourceLenBoolCurrent.runtime out ready returned
  have bDistinct : B.allocation.extra.roots.toList.Nodup:=by rw [bAllocation];exact CurrentCallResourceLenBoolCurrent.roots out ready returned
  have bShort : B.allocation.extra.nodes.size<65536:=by rw [bAllocation];exact CurrentCallResourceLenBoolCurrent.short out ready returned
  have qConcrete : ∃ suppliedId tag,current.pointer.value.provenance=.concrete suppliedId tag:=⟨id,out.sourceOutput.tag,by rw [qPointer,returned.sourcePointer];rfl⟩
  have bConcrete : ∃ suppliedId tag,B.pointer.value.provenance=.concrete suppliedId tag:=⟨out.physical.id,out.boolOutput.tag,by rw [bPointer];rfl⟩
  have older:=GeneralBorrowParentTagInvariant.parent_below_fresh out.sourceOutput.child.tree out.sourceOutput.global out.sourceWitness.runtime
    out.sourceChild out.sourceWitness.node out.sourceWitness.nodeAt
  rw [out.sourceWitness.tag] at older
  have tags : returned.sourceNode.tag≠bNode.tag:=by
    intro same
    rw [returned.sourceTag,bTag,(CurrentCallResourceBoolFacets.current out).2.2.1] at same
    rw [same] at older
    exact Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older)
  have absent : out.physical.id≠id→∀index node,B.allocation.extra.nodes.get index=some node→node.tag≠returned.sourceNode.tag:=by
    intro different index node found
    rw [bAllocation,CurrentCallResourceLenBoolCurrent.allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right different] at found
    rw [returned.sourceTag]
    exact CurrentCallResourceBoolTagSeparation.absent out different index node found
  have last:=(current.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have extent:=current.issued.capability.extent
  have limit:=UInt64.toNat_lt current.allocation.byteSize.bytes
  have sumSmall : offset+len.toNat<2^64:=by have p:=C.positive;omega
  have startEq : (UInt64.ofNat offset).toNat=offset:=by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by have p:=C.positive;omega : offset<2^64)]
  have noWrap : (UInt64.ofNat offset+len).toNat=(UInt64.ofNat offset).toNat+len.toNat:=by simp only [UInt64.toNat_add,startEq,Nat.mod_eq_of_lt sumSmall]
  have positive : (UInt64.ofNat offset).toNat<(UInt64.ofNat offset+len).toNat:=by rw [noWrap];have p:=C.positive;omega
  have boolNoWrap : (out.physical.offset+1).toNat=out.physical.offset.toNat+1:=by
    have bounds:=out.physical.bounds
    have maximum:=out.physical.capacity.toNat_lt
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega : out.physical.offset.toNat+1<2^64)]
  have boolPositive : out.physical.offset.toNat<(out.physical.offset+1).toNat:=by omega
  have ownedFrame : (CurrentCallResourceEntryRelease.borrowFrame out).protectedTags=#[(id,returned.sourceNode.tag),(out.physical.id,bNode.tag)]:=by
    rw [returned.sourceTag,out.sourceTag,bTag,(CurrentCallResourceBoolFacets.current out).2.2.1]
    simp only [CurrentCallResourceEntryRelease.borrowFrame,empty,FrameState.addProtector]
    rfl
  have separate : out.physical.id=id→(UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat ∨ (out.physical.offset+1).toNat≤(UInt64.ofNat offset).toNat:=by
    intro same
    by_cases left : (UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat
    · exact .inl left
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro overlap
      have originalSame:=out.physicalId.symm.trans same
      exact C.separate originalSame (id,out.physical.offset.toNat) ⟨rfl,by omega,by omega⟩
        ⟨originalSame.symm,by rw [out.physicalOffset];exact Nat.le_refl _,by rw [out.physicalOffset];omega⟩
  have owned : OwnedOn (S05CompletedAncestryReadMutable.Authority B.allocation.extra B.precise.completion
      (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags B.pointer.grant)
      out.physical.offset (out.physical.offset+1) B.allocation.extra.locations:=by rw [bAllocation,bCompletion,bGrant];exact bOwned
  let qEntry:={(CurrentCallResourceLenInvoke.entry out) with allocation:=CurrentCallResourceLenCapability.sourceAllocation out ready}
  obtain ⟨released⟩:=CurrentCallResourceCurrentRelease.release current B
    (by intro same;rw [bAllocation,qAllocation];exact CurrentCallResourceLenBoolCurrent.allocation_same out ready same)
    (by intro same;rw [bCompletion,qCompletion];exact CurrentCallResourceLenBoolCurrent.completion_same out ready returned same)
    qRuntime bRuntime qDistinct bDistinct qShort bShort qConcrete bConcrete returned.sourceNode bNode qAt bAt qHidden bHidden bLeaf tags absent
    (CurrentCallResourceEntryRelease.borrowFrame out) ownedFrame C.V.pointer.grant
    (by rw [bCompletion,bGrant];exact CurrentCallResourceLenBoolCurrent.edge out ready returned)
    (UInt64.ofNat offset) len out.physical.offset startEq rfl rfl positive boolPositive noWrap boolNoWrap separate qActive bActive owned
    qEntry (CurrentCallResourceLenBoolCurrent.entry out ready) returned.sourceLive (CurrentCallResourceLenBoolCurrent.live out ready returned)
    (by rw [qAllocation]) (by rw [bAllocation];exact CurrentCallResourceLenBoolCurrent.entry_allocation out ready)
  exact ⟨bData,bOwner,B,bPointer,bAllocation,bCompletion,⟨released⟩⟩
end
end DuplicatePrefix.CurrentCallResourceLenRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceLenRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Len root release dependency {dependency}"
