import duplicate_prefix.CurrentCallResourceBoolTagSeparation
import duplicate_prefix.CurrentCallResourceAcceptedBoolDifferent
import duplicate_prefix.CurrentCallResourceCopyBoolFrame
import duplicate_prefix.CurrentCallResourceAsMutSource
import duplicate_prefix.CurrentCallResourceAcceptedAccess
import duplicate_prefix.CurrentCallResourceCopyInstall
namespace DuplicatePrefix.CurrentCallResourceAcceptedBool
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization CurrentCallResourceEntryBody GeneralRangeMapOrigins
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem window_owned {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (exclusive : demandOf mode = .exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (lo hi : UInt64) (windowLower : offset ≤ lo.toNat) (windowUpper : hi.toNat ≤ offset+length) :
    GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant)
      lo hi W.allocation.extra.locations := by
  intro position valid positive beforeUpper afterLower
  have segmentPositive := (GeneralRangeMapGeometry.facts W.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
  have member : W.allocation.extra.locations.entries[position] ∈ W.allocation.extra.locations.entries.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  by_cases earlier : lo.toNat ≤ W.allocation.extra.locations.entries[position].range.start.toNat
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,W.allocation.extra.locations.entries[position].range.start.toNat)
      ⟨rfl,by omega,by omega⟩ _ member (Nat.le_refl _) segmentPositive
      (runtime.formed.profile position valid) (runtime.possible position valid)
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,lo.toNat) ⟨rfl,windowLower,by omega⟩ _ member (by omega) afterLower
      (runtime.formed.profile position valid) (runtime.possible position valid)

private def at_id {before tracker data owner oldId offset length mode}
    (B : UniformWindow before tracker data owner oldId offset length mode) (newId : AllocId) (same : oldId=newId) :
    UniformWindow before tracker data owner newId offset length mode where
  loan:=B.loan;pointer:=B.pointer;allocation:=B.allocation;precise:=B.precise
  loanAt:=B.loanAt;pointerAt:=B.pointerAt;pointerId:=B.pointerId.trans same
  present:=by rw [←same];exact B.present
  preciseAt:=by rw [←same];exact B.preciseAt
  binding:=B.binding;issued:=by rw [←same];exact B.issued
  parents:=B.parents;window:=by intro byte inside;apply B.window;simpa only [same] using inside

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
theorem same_rows (same : out.physical.id=id) (nonzero : count≠0) (within : count≤len/2) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority copied.allocation.extra P.B.precise.completion
      (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global.protectedTags P.B.pointer.grant)
      out.physical.offset (out.physical.offset+1) copied.allocation.extra.locations ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin copied.allocation.extra P.B.pointer.grant .Write out.physical.offset (out.physical.offset+1):=by
  obtain ⟨sData,sOwner,S,sPointer,sAllocation,sCompletion⟩:=CurrentCallResourceAsMutReturn.current_post done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed returned
  let B:=at_id P.B id same
  have allocation : B.allocation=S.allocation:=by
    change P.B.allocation=S.allocation
    rw [P.allocation,CurrentCallResourceAsMutBoolCurrent.finalAllocation,ite_eq_left same,sAllocation]
  have tree : S.allocation.extra=CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed:=by rw [sAllocation];rfl
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts S.allocation.extra (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global:=by
    rw [tree];exact CurrentCallResourceAsMutSource.runtime done fresh valid15 seed
  have distinct : S.allocation.extra.roots.toList.Nodup:=by rw [tree];exact CurrentCallResourceAsMutSource.roots done fresh valid15 seed
  have short : S.allocation.extra.nodes.size<65536:=by rw [tree];exact CurrentCallResourceAsMutSource.short done fresh valid15 seed
  have concrete : S.pointer.value.provenance=.concrete id seed.output.tag:=by rw [sPointer];rfl
  have nodeAt : S.allocation.extra.nodes.get B.pointer.grant=some P.node:=by rw [←allocation];exact P.nodeAt
  obtain ⟨source,sourceAt,_,binding⟩:=S.binding
  rw [concrete] at binding
  have different : B.pointer.grant≠S.pointer.grant:=by
    intro equal
    have found:=nodeAt
    rw [equal] at found
    have nodeEq : P.node=source:=Option.some.inj (found.symm.trans sourceAt)
    have tagEq : P.node.tag=seed.output.tag:=(congrArg TreeNode.tag nodeEq).trans binding.2.symm
    have old:=P.older
    rw [tagEq] at old
    have impossible:=UInt64.lt_iff_toNat_lt.mp old
    omega
  have positive : (0 : UInt64)<count:=by
    apply UInt64.lt_iff_toNat_lt.mpr
    have nz : count.toNat≠0:=by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    simp only [UInt64.toNat_zero];omega
  have last:=(S.window (id,(UInt64.ofNat offset).toNat+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have extent:=S.issued.capability.extent
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤S.allocation.extra.locations.size.bytes.toNat:=by
    rw [S.issued.capability.treeExtent]
    have p:=C.positive;omega
  have startEq:=(CurrentCallResourceSharedStage.source_bounds out).1
  have sumSmall : offset+len.toNat<2^64:=by
    have limit:=S.allocation.extra.locations.size.bytes.toNat_lt
    omega
  have noWrap : (UInt64.ofNat offset+len).toNat=offset+len.toNat:=by simp only [UInt64.toNat_add,startEq,Nat.mod_eq_of_lt sumSmall]
  have boolNoWrap : (out.physical.offset+1).toNat=out.physical.offset.toNat+1:=by
    have bounds:=out.physical.bounds
    have maximum:=out.physical.capacity.toNat_lt
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega : out.physical.offset.toNat+1<2^64)]
  have separate : (UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat ∨(out.physical.offset+1).toNat≤(UInt64.ofNat offset).toNat:=by
    by_cases left : (UInt64.ofNat offset+len).toNat≤out.physical.offset.toNat
    · exact .inl left
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro overlap
      have originalSame:=out.physicalId.symm.trans same
      exact C.separate originalSame (id,out.physical.offset.toNat) ⟨rfl,by omega,by omega⟩
        ⟨originalSame.symm,by rw [out.physicalOffset];exact Nat.le_refl _,by rw [out.physicalOffset];omega⟩
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:={done.entry with allocation:=done.entry.allocation.setExtra (CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed)}
  have entryAllocation : entry.allocation=S.allocation:=by rw [sAllocation,seed.allocationEq];rfl
  have active : GeneralBorrowFreshActiveWithin.ActiveWithin S.allocation.extra B.pointer.grant .Write out.physical.offset (out.physical.offset+1):=by
    rw [←allocation];exact P.activity
  have framed:=CurrentCallResourceCopyBoolFrame.same S B allocation runtime distinct short seed.output.tag concrete entry returned.sourceLive entryAllocation
    count positive within bounds out.physical.offset rfl boolNoWrap separate P.node nodeAt P.leaf P.hidden different active
  simp only [tree] at framed
  rw [copied.tree]
  exact framed
structure Framed where
  B : UniformWindow copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) P.identities P.holder out.physical.id out.physical.offset.toNat 1 .ret
  pointer : B.pointer=P.B.pointer
  allocation : B.allocation=if out.physical.id=id then copied.allocation else P.B.allocation
  precise : B.precise=P.B.precise
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global
  distinct : B.allocation.extra.roots.toList.Nodup
  short : B.allocation.extra.nodes.size<65536
  nodeAt : B.allocation.extra.nodes.get B.pointer.grant=some P.node
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write out.physical.offset (out.physical.offset+1)
  owned : OwnedOn (S05CompletedAncestryReadMutable.Authority B.allocation.extra B.precise.completion
    (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global.protectedTags B.pointer.grant)
    out.physical.offset (out.physical.offset+1) B.allocation.extra.locations
  parentIssued : SpatialDelegation copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) out.physical.id B.allocation B.precise.completion C.V.pointer.grant
  parentBinding : PointerBinds B.allocation C.V.pointer
  edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some C.V.pointer.grant)

private theorem bool_nowrap : (out.physical.offset+1).toNat=out.physical.offset.toNat+1:=by
  have bounds:=out.physical.bounds
  have maximum:=out.physical.capacity.toNat_lt
  simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega : out.physical.offset.toNat+1<2^64)]

private theorem same_current (same : out.physical.id=id) (nonzero : count≠0) (within : count≤len/2) :
    Nonempty (Framed done fresh valid15 seed returned copied P):=by
  have resources:=CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within
  have oldTree : P.B.allocation.extra=CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed:=by
    rw [P.allocation,CurrentCallResourceAsMutBoolCurrent.finalAllocation,ite_eq_left same];rfl
  have frame : copied.allocation.extra={P.B.allocation.extra with locations:=copied.allocation.extra.locations}:=by rw [oldTree];exact resources.2.2.1
  have capacity : copied.allocation.extra.locations.size=P.B.allocation.extra.locations.size:=by rw [oldTree];exact resources.2.2.2.1
  have bytes : copied.allocation.byteSize=P.B.allocation.byteSize:=by
    rw [P.allocation,CurrentCallResourceAsMutBoolCurrent.finalAllocation,ite_eq_left same]
    exact copied.byteSize
  have length : copied.allocation.len=P.B.allocation.len:=by
    rw [P.allocation,CurrentCallResourceAsMutBoolCurrent.finalAllocation,ite_eq_left same]
    exact copied.length
  have parents : ParentInterpretation copied.allocation.extra P.B.precise.completion:=by
    rw [P.completion,CurrentCallResourceAsMutBoolCurrent.finalC,ite_eq_left same]
    exact resources.2.1
  have sourcePresent : Present (ActualWorld copied.machine) id copied.allocation:=by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,⟨done.entry.kind,copied.allocation⟩),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some copied.live),rfl⟩
  have present : Present (ActualWorld copied.machine) out.physical.id copied.allocation:=by simpa only [same] using sourcePresent
  have raw:=same_rows done fresh valid15 seed returned copied P same nonzero within
  have noWrap:=bool_nowrap (out:=out)
  obtain ⟨B,loan,pointer,allocation,precise⟩:=CurrentCallResourceCopyInstall.window P.B rfl copied.machine copied.allocation present length bytes frame capacity resources.1 parents
    out.physical.offset 1 rfl rfl (by omega) (by simpa only [UInt64.toNat_one] using noWrap) raw.1
  have metadata : ∀ index node,P.B.allocation.extra.nodes.get index=some node→
      ∃ changed,copied.allocation.extra.nodes.get index=some changed ∧changed.tag=node.tag ∧changed.parent=node.parent ∧
        changed.isExposed=node.isExposed ∧changed.defaultInitialPermission=node.defaultInitialPermission:=by
    intro index node found
    exact ⟨node,by rw [frame];exact found,rfl,rfl,rfl,rfl⟩
  have parentIssued:=CurrentCallAllocationLicense.spatial P.parentIssued copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) copied.allocation
    present rfl length bytes capacity (by intro position root found;rw [frame];exact found) metadata P.B.precise.completion (by intro child parent edge;exact edge)
  have parentBinding : PointerBinds copied.allocation C.V.pointer:=by
    obtain ⟨node,found,mapped,provenance⟩:=P.parentBinding
    exact ⟨node,by rw [frame];exact found,by rw [frame];exact mapped,provenance⟩
  refine ⟨{
    B:=B
    pointer:=pointer
    allocation:=by simpa only [ite_eq_left same] using allocation
    precise:=precise
    runtime:=by rw [allocation];exact resources.1
    distinct:=by rw [allocation,frame];exact P.distinct
    short:=by rw [allocation,frame];exact P.short
    nodeAt:=by rw [allocation,pointer,frame];exact P.nodeAt
    activity:=by rw [allocation,pointer];exact raw.2
    owned:=by rw [allocation,precise,pointer];exact raw.1
    parentIssued:=by rw [allocation,precise];exact parentIssued
    parentBinding:=by rw [allocation];exact parentBinding
    edge:=by rw [precise,pointer];exact P.edge}⟩

private theorem different_current (different : out.physical.id≠id) :
    Nonempty (Framed done fresh valid15 seed returned copied P):=by
  obtain ⟨B,pointer,allocation,precise,_⟩:=CurrentCallResourceAcceptedBoolDifferent.current done fresh valid15 seed returned copied P different
  have noWrap:=bool_nowrap (out:=out)
  have raw:=window_owned P.B rfl P.runtime out.physical.offset (out.physical.offset+1) (Nat.le_refl _) (by omega)
  have issued:=CurrentCallResourceAcceptedBoolDifferent.parent_issued done fresh valid15 seed returned copied P different
  refine ⟨{
    B:=B
    pointer:=pointer
    allocation:=by simpa only [ite_eq_right different] using allocation
    precise:=precise
    runtime:=by rw [allocation];exact P.runtime
    distinct:=by rw [allocation];exact P.distinct
    short:=by rw [allocation];exact P.short
    nodeAt:=by rw [allocation,pointer];exact P.nodeAt
    activity:=by rw [allocation,pointer];exact P.activity
    owned:=by rw [allocation,precise,pointer];exact raw
    parentIssued:=by rw [allocation,precise];exact issued
    parentBinding:=by rw [allocation];exact P.parentBinding
    edge:=by rw [precise,pointer];exact P.edge}⟩

/-- Both actual allocation cases preserve the Bool reservation resources
through the SAME concrete copy. The producer adds no caller-side access result. -/
theorem invoke (nonzero : count≠0) (within : count≤len/2) :
    Nonempty (Framed done fresh valid15 seed returned copied P):=by
  by_cases same : out.physical.id=id
  · exact same_current done fresh valid15 seed returned copied P same nonzero within
  · exact different_current done fresh valid15 seed returned copied P same

namespace Framed
variable (F : Framed done fresh valid15 seed returned copied P)
theorem allocation_same (same : out.physical.id=id) : F.B.allocation=copied.allocation:=by
  simpa only [ite_eq_left same] using F.allocation

theorem completion_same (same : out.physical.id=id) : F.B.precise.completion=CurrentCallResourceAsMutSource.completion done fresh valid15 seed:=by
  rw [F.precise,P.completion,CurrentCallResourceAsMutBoolCurrent.finalC,ite_eq_left same]

theorem absent (different : out.physical.id≠id) (index : UniIndex) (node : TreeNode)
    (found : F.B.allocation.extra.nodes.get index=some node) : node.tag≠out.sourceOutput.tag:=by
  rw [F.allocation,ite_eq_right different,P.allocation,CurrentCallResourceAsMutBoolCurrent.finalAllocation,ite_eq_right different,
    CurrentCallResourceLenBoolCurrent.allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right different] at found
  exact CurrentCallResourceBoolTagSeparation.absent out different index node found
end Framed

end
end DuplicatePrefix.CurrentCallResourceAcceptedBool
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedBool" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted Bool resources dependency {dependency}"
