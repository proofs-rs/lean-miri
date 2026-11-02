import duplicate_prefix.CurrentCallResourceAsMutSource
import duplicate_prefix.CurrentCallResourceAcceptedAccess
import duplicate_prefix.CurrentCallResourceCopyInstall
namespace DuplicatePrefix.CurrentCallResourceAcceptedSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody GeneralRangeMapOrigins
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
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

theorem owned (nonzero : count≠0) (within : count≤len/2) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority copied.allocation.extra
      (CurrentCallResourceAsMutSource.completion done fresh valid15 seed)
      (CurrentCallResourceAsMutSource.postTracker done fresh valid15 seed).global.protectedTags done.qWindow.pointer.grant)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) copied.allocation.extra.locations:=by
  have resources:=CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within
  have nodes : copied.allocation.extra.nodes=(CurrentCallResourceAsMutSource.tree done fresh valid15 seed).nodes:=by rw [resources.2.2.1];rfl
  exact CurrentCallResourceAsMutSource.copy_owned done fresh valid15 seed copied.allocation.extra nodes resources.2.2.2.2.1

theorem activity (nonzero : count≠0) (within : count≤len/2) :
    GeneralBorrowFreshActiveWithin.ActiveWithin copied.allocation.extra out.sourceChild .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len):=
  (CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within).2.2.2.2.2 out.sourceChild
    (CurrentCallResourceAsMutSource.activity done fresh valid15 seed)

theorem node (nonzero : count≠0) (within : count≤len/2) :
    ∃ node,copied.allocation.extra.nodes.get out.sourceChild=some node ∧node.tag=out.sourceOutput.tag ∧node.isExposed=false:=by
  obtain ⟨node,found,tag,hidden⟩:=CurrentCallResourceAsMutSource.node done fresh valid15 seed
  refine ⟨node,?_,tag,hidden⟩
  rw [(CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within).2.2.1]
  exact found

theorem runtime (nonzero : count≠0) (within : count≤len/2) :
    DuplicatePrefixBorrowContract.RuntimeFacts copied.allocation.extra (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global:=
  (CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within).1

theorem parents (nonzero : count≠0) (within : count≤len/2) :
    ParentInterpretation copied.allocation.extra (CurrentCallResourceAsMutSource.completion done fresh valid15 seed):=
  (CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within).2.1

theorem roots (nonzero : count≠0) (within : count≤len/2) : copied.allocation.extra.roots.toList.Nodup:=by
  rw [(CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within).2.2.1]
  exact CurrentCallResourceAsMutSource.roots done fresh valid15 seed

theorem short (nonzero : count≠0) (within : count≤len/2) : copied.allocation.extra.nodes.size<65536:=by
  rw [(CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within).2.2.1]
  exact CurrentCallResourceAsMutSource.short done fresh valid15 seed

theorem current (nonzero : count≠0) (within : count≤len/2) :
    ∃ currentData currentOwner,∃ current : UniformWindow copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed)
      currentData currentOwner id offset len.toNat .mut,
      current.pointer=Q.pointer ∧current.allocation=copied.allocation ∧
      current.precise.completion=CurrentCallResourceAsMutSource.completion done fresh valid15 seed:=by
  obtain ⟨qData,qOwner,old,pointer,allocation,completion⟩:=CurrentCallResourceAsMutSource.current done fresh valid15 seed returned
  have resources:=CurrentCallResourceAcceptedAccess.resources done fresh valid15 seed returned copied nonzero within
  have present : Present (ActualWorld copied.machine) id copied.allocation:=by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,⟨done.entry.kind,copied.allocation⟩),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some copied.live),rfl⟩
  have tree : old.allocation.extra=CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed:=by rw [allocation];rfl
  have shape : copied.allocation.extra={old.allocation.extra with locations:=copied.allocation.extra.locations}:=by rw [tree];exact resources.2.2.1
  have cap : copied.allocation.extra.locations.size=old.allocation.extra.locations.size:=by rw [tree];exact resources.2.2.2.1
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts copied.allocation.extra (CurrentCallResourceAsMutSource.postTracker done fresh valid15 seed).global:=resources.1
  have parents : ParentInterpretation copied.allocation.extra old.precise.completion:=by rw [completion];exact resources.2.1
  have grant : old.pointer.grant=done.qWindow.pointer.grant:=(congrArg PointerInstance.grant pointer).trans (congrArg PointerInstance.grant done.qPointer).symm
  have rawOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority copied.allocation.extra old.precise.completion
      (CurrentCallResourceAsMutSource.postTracker done fresh valid15 seed).global.protectedTags old.pointer.grant)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) copied.allocation.extra.locations:=by
    rw [completion,grant]
    exact owned done fresh valid15 seed returned copied nonzero within
  have last:=(old.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have extent:=old.issued.capability.extent
  have limit:=UInt64.toNat_lt old.allocation.byteSize.bytes
  have sumSmall : offset+len.toNat<2^64:=by have p:=C.positive;omega
  have startEq : (UInt64.ofNat offset).toNat=offset:=by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by have p:=C.positive;omega : offset<2^64)]
  have noWrap : (UInt64.ofNat offset+len).toNat=(UInt64.ofNat offset).toNat+len.toNat:=by simp only [UInt64.toNat_add,startEq,Nat.mod_eq_of_lt sumSmall]
  have positive : (UInt64.ofNat offset).toNat<(UInt64.ofNat offset+len).toNat:=by rw [noWrap];have p:=C.positive;omega
  have bytes : copied.allocation.byteSize=old.allocation.byteSize:=by rw [allocation];exact copied.byteSize
  have length : copied.allocation.len=old.allocation.len:=by rw [allocation];exact copied.length
  obtain ⟨current,loan,pointerEq,allocationEq,preciseEq⟩:=CurrentCallResourceCopyInstall.window old rfl copied.machine copied.allocation present
    length bytes shape cap runtime parents (UInt64.ofNat offset) len startEq rfl positive noWrap rawOwned
  exact ⟨qData,qOwner,current,pointerEq.trans pointer,allocationEq,(congrArg PreciseAllocation.completion preciseEq).trans completion⟩
end
end DuplicatePrefix.CurrentCallResourceAcceptedSource
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedSource" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted source resources dependency {dependency}"
