import duplicate_prefix.CurrentCallResourceAcceptedRelease
import duplicate_prefix.CurrentCallResourceAcceptedReturn
import duplicate_prefix.CurrentCallResourceAcceptedPhysical
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CurrentCallResourceAcceptedSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
private theorem prepared_stack (before : Before) (ready : CurrentCallPush.StackReadiness before #[]) :
    CurrentCallPush.StackReadiness (CurrentCallPush.preparedMachine before #[]) #[] := by
  obtain ⟨thread,active,_⟩:=ready
  refine ⟨{thread with topUserRelevantFrame:=some 0},PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active,?_⟩
  intro index same
  have zero : (0 : Nat)=index:=Option.some.inj same
  simp only [Array.size_empty]
  omega

private theorem start {options remaining span before tracker data owner id offset len W place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : Conditions options remaining span #[] (CurrentCallResourceEntry.root before #[] place race)
      before tracker data owner id offset len W place)
    (ready : CurrentCallResourceBodyReadiness.Ready C) (stackReady : CurrentCallPush.StackReadiness before #[])
    (budget : Nat) (dispatch : limits.callDispatch=budget+1) (count : UInt64) (nonzero : count≠0) :
    let preparedReady : CurrentCallResourceBodyReadiness.Ready (CurrentCallResourcePreparedEntry.prepared C):=⟨ready.sourceNodes,ready.pointerTags⟩
    ∃ out : Output limits (CurrentCallResourcePreparedEntry.prepared C) count,
      ∃ nextData nextOwner,
      ∃ Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut,
      ∃ stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
        (CurrentCallResourceBodyReadiness.current_room out preparedReady),
      ∃ _returned : CurrentCallResourceLenReturn.Result out preparedReady Q stage,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer W.pointer.value) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        (⟨⟨#[]⟩,before⟩ : RootState)=.ok () (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine) := by
  obtain ⟨out,actualEntry⟩:=CurrentCallResourceEntry.invoke limits race C stackReady count
  let preparedReady : CurrentCallResourceBodyReadiness.Ready (CurrentCallResourcePreparedEntry.prepared C):=⟨ready.sourceNodes,ready.pointerTags⟩
  obtain ⟨nextData,nextOwner,Q,stage,⟨returned⟩⟩:=CurrentCallResourceLenReturn.invoke out preparedReady
    (prepared_stack before stackReady) budget dispatch nonzero
  exact ⟨out,nextData,nextOwner,Q,stage,returned,actualEntry⟩
private def reindex {machine held identities owner oldId lower length mode}
    (B : UniformWindow machine held identities owner oldId lower length mode)
    (newId : AllocId) (newLower : Nat) (sameId : oldId=newId) (sameLower : lower=newLower) :
    UniformWindow machine held identities owner newId newLower length mode where
  loan:=B.loan;pointer:=B.pointer;allocation:=B.allocation;precise:=B.precise
  loanAt:=B.loanAt;pointerAt:=B.pointerAt;pointerId:=B.pointerId.trans sameId
  present:=by rw [←sameId];exact B.present
  preciseAt:=by rw [←sameId];exact B.preciseAt
  binding:=B.binding
  issued:=by rw [←sameId];exact B.issued
  parents:=B.parents
  window:=by intro byte inside;exact B.window byte (by simpa only [sameId,sameLower] using inside)

private def reindex_released {machine held identities owner oldId lower frame original start entry}
    {B : UniformWindow machine held identities owner oldId lower 1 .ret}
    (old : CurrentCallResourceCurrentRelease.Released B frame original start entry)
    (newId : AllocId) (newLower : Nat) (sameId : oldId=newId) (sameLower : lower=newLower)
    (newStart : UInt64) (newEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sameStart : start=newStart) (sameEntry : entry=newEntry) :
    CurrentCallResourceCurrentRelease.Released (reindex B newId newLower sameId sameLower) frame original newStart newEntry where
  memory:=old.memory;tree:=old.tree;plan:=old.plan
  live:=by
    change old.memory.live.find? (fun row=>row.1==newId)=some (newId,{newEntry with allocation:=B.allocation.setExtra old.tree})
    rw [←sameId,←sameEntry]
    exact old.live
  runtime:=old.runtime;parents:=old.parents;shape:=old.shape;capacity:=old.capacity
  distinct:=old.distinct;short:=old.short
  owned:=by rw [←sameStart];exact old.owned

/-- Original strong Result for the nonzero accepted branch. All operational
entry, helper, copy, release and original-destination store facts are derived. -/
theorem invoke {options remaining span before tracker data owner id offset len W place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : Conditions options remaining span #[] (CurrentCallResourceEntry.root before #[] place race)
      before tracker data owner id offset len W place)
    (ready : CurrentCallResourceBodyReadiness.Ready C) (stackReady : CurrentCallPush.StackReadiness before #[])
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (physicalSource : OrdinaryPhysicalValidity.MutU8Slice W.allocation (UInt64.ofNat offset) len)
    (storageRoom : W.allocation.len+64<2^64)
    (sourceProfile : CurrentCallBoolProtection.WindowReady before id (UInt64.ofNat offset).toNat len.toNat)
    (count : UInt64) (nonzero : count≠0) (within : count≤len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer W.pointer.value) len count place:=by
  let prepared:=CurrentCallResourcePreparedEntry.prepared C
  let preparedReady : CurrentCallResourceBodyReadiness.Ready prepared:=⟨ready.sourceNodes,ready.pointerTags⟩
  obtain ⟨out,nextData,nextOwner,Q,stage,lenResult,actualEntry⟩:=start limits race C ready stackReady budget dispatch count nonzero
  have sourceReady : CurrentCallBoolProtection.WindowReady (CurrentCallPush.preparedMachine before #[]) id (UInt64.ofNat offset).toNat len.toNat:=
    sourceProfile.transport rfl
  obtain ⟨done,fresh,valid15,seed,returned,copied,_⟩:=CurrentCallResourceAcceptedCopy.invoke (result:=lenResult) budget dispatch statementFuel statementEq nonzero within
    rfl (by change (0 : UInt8)<255;decide) physicalSource storageRoom sourceReady
  obtain ⟨P⟩:=CurrentCallResourceAsMutBoolCurrent.invoke lenResult done fresh valid15 seed returned
  obtain ⟨F⟩:=CurrentCallResourceAcceptedBool.invoke done fresh valid15 seed returned copied P nonzero within
  obtain ⟨physical,pointer,physicalId,physicalOffset,binding⟩:=CurrentCallResourceAcceptedPhysical.current done fresh valid15 seed returned copied
  have rawBorrow:=RootEntryFrame.raw_borrow (CurrentCallPush.preparedMachine before #[]) (.memory place)
    (CallEntryFacts.freshRoot before).2 tracker C.state.enabled
  have empty : prepared.borrowFrame={} :=Option.some.inj (C.frameBorrow.symm.trans rawBorrow)
  obtain ⟨released⟩:=CurrentCallResourceAcceptedRelease.release done fresh valid15 seed returned copied P F nonzero within empty physical
    (physicalId.trans out.physicalId.symm) (physicalOffset.trans out.physicalOffset.symm)
  let currentB:=reindex F.B prepared.physical.id prepared.physical.offset.toNat out.physicalId (congrArg UInt64.toNat out.physicalOffset)
  let currentReleased:=reindex_released released prepared.physical.id prepared.physical.offset.toNat out.physicalId
    (congrArg UInt64.toNat out.physicalOffset) physical.offset physical.entry rfl rfl
  have parentIssued : SpatialDelegation copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed)
      prepared.physical.id currentB.allocation currentB.precise.completion prepared.V.pointer.grant:=by
    change SpatialDelegation copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed)
      prepared.physical.id F.B.allocation F.B.precise.completion prepared.V.pointer.grant
    simpa only [out.physicalId] using F.parentIssued
  have parentBinding : PointerBinds currentB.allocation prepared.V.pointer:=F.parentBinding
  obtain ⟨final,trace,terminal,terminalEmpty⟩:=CurrentCallResourceAcceptedReturn.complete done fresh valid15 seed returned copied currentB physical
    pointer physicalId physicalOffset binding parentIssued parentBinding currentReleased rfl rfl rfl
  let cfg:=config options (remaining+1) span
  let installed:=Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨cfg,limits,fun _ _=>True⟩
  have entry : CallSafety.IsCallEntry 1 installed:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [terminalEmpty];decide
  have wholeTrace:=SuccessfulTrace.append lenResult.trace trace
  exact ⟨installed,final,actualEntry,wholeTrace,terminal,terminalEmpty,
    SuccessfulTrace.no_errors context 1 installed final entry wholeTrace past,
    SuccessfulTrace.no_ub context 1 installed final entry wholeTrace past,
    SuccessfulTraceTerminal.prefix_step_success wholeTrace terminal⟩
end
end DuplicatePrefix.CurrentCallResourceAcceptedSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedSafety" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted strong safety dependency {dependency}"
