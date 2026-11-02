import duplicate_prefix.CurrentCallResourceAcceptedSource
import duplicate_prefix.CurrentCallResourceAcceptedBool
import duplicate_prefix.CurrentCallResourceAcceptedHeap
import duplicate_prefix.CurrentCallResourceCurrentRelease
import duplicate_prefix.CurrentCallResourceEntryRelease
namespace DuplicatePrefix.CurrentCallResourceAcceptedRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody GeneralRangeMapOrigins
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)

    (copied : CurrentCallResourceAcceptedCopy.Result done fresh valid15 seed returned)

    (P : CurrentCallResourceAsMutBoolCurrent.Packet result done fresh valid15 seed returned)
    (F : CurrentCallResourceAcceptedBool.Framed done fresh valid15 seed returned copied P)

theorem release (nonzero : count≠0) (within : count≤len/2) (empty : C.borrowFrame={})
    (physical : CurrentCallBoolScalarWrite.Window copied.machine place)
    (physicalId : physical.id=out.physical.id) (physicalOffset : physical.offset=out.physical.offset) :
    Nonempty (CurrentCallResourceCurrentRelease.Released F.B (CurrentCallResourceEntryRelease.borrowFrame out)
      C.V.pointer.grant physical.offset physical.entry):=by
  obtain ⟨qData,qOwner,current,qPointer,qAllocation,qCompletion⟩:=CurrentCallResourceAcceptedSource.current done fresh valid15 seed returned copied nonzero within
  obtain ⟨qNode,qFound,qTag,qHidden⟩:=CurrentCallResourceAcceptedSource.node done fresh valid15 seed returned copied nonzero within
  have qGrant : current.pointer.grant=out.sourceChild:=by rw [qPointer,result.sourcePointer];rfl
  have qAt : current.allocation.extra.nodes.get current.pointer.grant=some qNode:=by rw [qAllocation,qGrant];exact qFound
  have qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts current.allocation.extra (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global:=by
    rw [qAllocation];exact CurrentCallResourceAcceptedSource.runtime done fresh valid15 seed returned copied nonzero within
  have qDistinct : current.allocation.extra.roots.toList.Nodup:=by rw [qAllocation];exact CurrentCallResourceAcceptedSource.roots done fresh valid15 seed returned copied nonzero within
  have qShort : current.allocation.extra.nodes.size<65536:=by rw [qAllocation];exact CurrentCallResourceAcceptedSource.short done fresh valid15 seed returned copied nonzero within
  have qActive : GeneralBorrowFreshActiveWithin.ActiveWithin current.allocation.extra current.pointer.grant .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len):=by
    rw [qAllocation,qGrant];exact CurrentCallResourceAcceptedSource.activity done fresh valid15 seed returned copied nonzero within
  have qConcrete : ∃ suppliedId tag,current.pointer.value.provenance=.concrete suppliedId tag:=⟨id,out.sourceOutput.tag,by rw [qPointer,result.sourcePointer];rfl⟩
  have bConcrete : ∃ suppliedId tag,F.B.pointer.value.provenance=.concrete suppliedId tag:=⟨out.physical.id,out.boolOutput.tag,by rw [F.pointer,P.pointer];rfl⟩
  have older:=GeneralBorrowParentTagInvariant.parent_below_fresh out.sourceOutput.child.tree out.sourceOutput.global out.sourceWitness.runtime out.sourceChild out.sourceWitness.node out.sourceWitness.nodeAt
  rw [out.sourceWitness.tag] at older
  have tags : qNode.tag≠P.node.tag:=by
    intro same
    rw [qTag,P.nodeTag,out.boolTag] at same
    rw [same] at older
    exact Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older)
  have absent : out.physical.id≠id→∀ index node,F.B.allocation.extra.nodes.get index=some node→node.tag≠qNode.tag:=by
    intro different index node found
    rw [qTag]
    exact CurrentCallResourceAcceptedBool.Framed.absent done fresh valid15 seed returned copied P F different index node found
  have last:=(current.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have extent:=current.issued.capability.extent
  have limit:=current.allocation.byteSize.bytes.toNat_lt
  have sumSmall : offset+len.toNat<2^64:=by have p:=C.positive;omega
  have startEq : (UInt64.ofNat offset).toNat=offset:=by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by have p:=C.positive;omega : offset<2^64)]
  have noWrap : (UInt64.ofNat offset+len).toNat=(UInt64.ofNat offset).toNat+len.toNat:=by simp only [UInt64.toNat_add,startEq,Nat.mod_eq_of_lt sumSmall]
  have positive : (UInt64.ofNat offset).toNat<(UInt64.ofNat offset+len).toNat:=by rw [noWrap];have p:=C.positive;omega
  have boolNoWrap : (out.physical.offset+1).toNat=out.physical.offset.toNat+1:=by
    have bounds:=out.physical.bounds
    have maximum:=out.physical.capacity.toNat_lt
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega : out.physical.offset.toNat+1<2^64)]
  have boolPositive : out.physical.offset.toNat<(out.physical.offset+1).toNat:=by omega
  have ownedFrame : (CurrentCallResourceEntryRelease.borrowFrame out).protectedTags=#[(id,qNode.tag),(out.physical.id,P.node.tag)]:=by
    rw [qTag,P.nodeTag,out.sourceTag,out.boolTag]
    simp only [CurrentCallResourceEntryRelease.borrowFrame,empty,FrameState.addProtector]
    rfl
  have separate : out.physical.id=id→(UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat ∨(out.physical.offset+1).toNat≤(UInt64.ofNat offset).toNat:=by
    intro same
    by_cases left : (UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat
    · exact .inl left
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro overlap
      have originalSame:=out.physicalId.symm.trans same
      exact C.separate originalSame (id,out.physical.offset.toNat) ⟨rfl,by omega,by omega⟩
        ⟨originalSame.symm,by rw [out.physicalOffset];exact Nat.le_refl _,by rw [out.physicalOffset];omega⟩
  have ids : ((ActualWorld copied.machine).toList.map Prod.fst).Nodup:=by
    simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using CurrentCallResourceAcceptedHeap.ids done fresh valid15 seed returned copied
  have physicalPresent : Present (ActualWorld copied.machine) out.physical.id physical.entry.allocation:=by
    have live:=physical.live
    rw [physicalId] at live
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(out.physical.id,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have bAllocation : physical.entry.allocation=F.B.allocation:=
    CandidateCurrentUniformOwnerWindow.same_id (ActualWorld copied.machine).toList ids out.physical.id physical.entry.allocation F.B.allocation physicalPresent F.B.present
  let qEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨done.entry.kind,copied.allocation⟩
  have bLive : copied.machine.memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,physical.entry):=by
    simpa only [physicalId] using physical.live
  obtain ⟨released⟩:=CurrentCallResourceCurrentRelease.release current F.B
    (by intro same;rw [CurrentCallResourceAcceptedBool.Framed.allocation_same done fresh valid15 seed returned copied P F same,qAllocation])
    (by intro same;rw [CurrentCallResourceAcceptedBool.Framed.completion_same done fresh valid15 seed returned copied P F same,qCompletion])
    qRuntime F.runtime qDistinct F.distinct qShort F.short qConcrete bConcrete qNode P.node qAt F.nodeAt qHidden P.hidden P.leaf tags absent
    (CurrentCallResourceEntryRelease.borrowFrame out) ownedFrame C.V.pointer.grant F.edge
    (UInt64.ofNat offset) len out.physical.offset startEq rfl rfl positive boolPositive noWrap boolNoWrap separate qActive F.activity F.owned
    qEntry physical.entry copied.live bLive (by rw [qAllocation]) bAllocation
  exact ⟨{released with owned:=by rw [physicalOffset];exact released.owned}⟩
end
end DuplicatePrefix.CurrentCallResourceAcceptedRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted root release dependency {dependency}"
