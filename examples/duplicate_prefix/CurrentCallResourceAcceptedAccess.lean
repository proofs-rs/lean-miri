import duplicate_prefix.CurrentCallResourceAcceptedCopy
import duplicate_prefix.CurrentCallResourceCopyAccess
namespace DuplicatePrefix.CurrentCallResourceAcceptedAccess
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
/-- Resource facts for the literal two accesses retained by the actual copied
allocation. No second copy or independently chosen borrow result is used. -/
theorem resources (nonzero : count≠0) (within : count≤len/2) :
    DuplicatePrefixBorrowContract.RuntimeFacts copied.allocation.extra (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global ∧
    ParentInterpretation copied.allocation.extra (CurrentCallResourceAsMutReturn.completion done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed) ∧
    copied.allocation.extra={CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed with locations:=copied.allocation.extra.locations} ∧
    copied.allocation.extra.locations.size=(CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed).locations.size ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority copied.allocation.extra
      (CurrentCallResourceAsMutReturn.completion done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)
      (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global.protectedTags seed.childIndex)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) copied.allocation.extra.locations ∧
    (∀ target,GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed) target .Write
      (UInt64.ofNat offset) (UInt64.ofNat offset+len)→GeneralBorrowFreshActiveWithin.ActiveWithin copied.allocation.extra target .Write
      (UInt64.ofNat offset) (UInt64.ofNat offset+len)):=by
  obtain ⟨childData,childOwner,child,pointer,allocation,completion⟩:=CurrentCallResourceAsMutReturn.current_post done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed returned
  have childTree : child.allocation.extra=CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed:=by rw [allocation];rfl
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts child.allocation.extra (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).global:=by
    rw [childTree]
    exact CurrentCallResourceAsMutReturn.runtime_end_call done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
  have releaseFrame:=(CurrentCallResourceAsMutReturn.release done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed).2.1
  have nodes : child.allocation.extra.nodes=seed.output.child.tree.nodes:=by
    rw [childTree,CurrentCallResourceAcceptedCopy.sourceTree,CurrentCallResourceAsMutReturn.releasedTree,releaseFrame]
  have roots : child.allocation.extra.roots=seed.output.child.tree.roots:=by
    rw [childTree,CurrentCallResourceAcceptedCopy.sourceTree,CurrentCallResourceAsMutReturn.releasedTree,releaseFrame]
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤child.allocation.extra.locations.size.bytes.toNat:=by
    rw [childTree,CurrentCallResourceAcceptedCopy.sourceTree,CurrentCallResourceAsMutReturn.releasedTree,releaseFrame]
    change (UInt64.ofNat offset).toNat+len.toNat≤(seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.locations.size.bytes.toNat
    rw [(CurrentCallResourceAsMutReturn.release done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed).2.2.2.2.1]
    exact seed.bounds
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:={done.entry with allocation:=done.entry.allocation.setExtra (CurrentCallResourceAcceptedCopy.sourceTree done fresh valid15 seed)}
  have entryEq : entry.allocation=child.allocation:=by rw [allocation,seed.allocationEq];rfl
  have concrete : child.pointer.value.provenance=.concrete id seed.output.tag:=by rw [pointer];rfl
  have positive : (0 : UInt64)<count:=by
    apply UInt64.lt_iff_toNat_lt.mpr
    have nz : count.toNat≠0:=by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    simp only [UInt64.toNat_zero];omega
  have access:=CurrentCallResourceCopyAccess.run child entry returned.sourceLive entryEq runtime
    (by rw [roots];exact seed.distinct) (by rw [nodes];exact seed.short) seed.output.tag concrete count positive within bounds
  simp only [childTree,pointer,completion] at access
  have literal : copied.allocation.extra=CurrentCallResourceAcceptedCopy.copiedTree done fresh valid15 seed:=copied.tree
  rw [literal]
  exact access.2.2
end
end DuplicatePrefix.CurrentCallResourceAcceptedAccess
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedAccess" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual copied allocation resources dependency {dependency}"
