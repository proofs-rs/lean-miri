import duplicate_prefix.CurrentCallResourceRejectedReturn
import duplicate_prefix.CurrentCallResourceLenPhysical
import duplicate_prefix.CurrentCallResourceAsMut
import duplicate_prefix.CurrentCallResourceLenRoots
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.PushThread
import duplicate_prefix.CurrentCallResourceLenRelease
namespace DuplicatePrefix.CurrentCallResourceRejectedSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceEntryBody CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
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

/-- Original strong Result for the nonzero rejected branch, from INITIAL
uniform live resources and explicit stack/execution/numeric readiness. All
entry, Len, release, access, validation and store certificates are derived. -/
theorem invoke {options remaining span before tracker data owner id offset len W place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : Conditions options remaining span #[] (CurrentCallResourceEntry.root before #[] place race)
      before tracker data owner id offset len W place)
    (ready : CurrentCallResourceBodyReadiness.Ready C) (stackReady : CurrentCallPush.StackReadiness before #[])
    (budget : Nat) (dispatch : limits.callDispatch=budget+1) (count : UInt64) (gt : count>len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer W.pointer.value) len count place := by
  have nonzero : count≠0:=by
    intro zero
    have small:=UInt64.lt_iff_toNat_lt.mp gt
    rw [zero] at small
    simp at small
  let prepared:=CurrentCallResourcePreparedEntry.prepared C
  let preparedReady : CurrentCallResourceBodyReadiness.Ready prepared:=⟨ready.sourceNodes,ready.pointerTags⟩
  obtain ⟨out,nextData,nextOwner,Q,stage,returned,actualEntry⟩:=start limits race C ready stackReady budget dispatch count nonzero
  have rawBorrow:=RootEntryFrame.raw_borrow (CurrentCallPush.preparedMachine before #[]) (.memory place)
    (CallEntryFacts.freshRoot before).2 tracker C.state.enabled
  have empty : prepared.borrowFrame={} := Option.some.inj (C.frameBorrow.symm.trans rawBorrow)
  obtain ⟨bData,bOwner,B,bPointer,bAllocation,bCompletion,⟨released⟩⟩:=CurrentCallResourceLenRelease.release out preparedReady returned empty
  obtain ⟨physical,pointer,physicalId,physicalOffset,binding⟩:=CurrentCallResourceLenPhysical.of_return returned
  let currentB:=reindex B prepared.physical.id prepared.physical.offset.toNat out.physicalId (congrArg UInt64.toNat out.physicalOffset)
  have livePhysical : returned.machine.memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,physical.entry):=by
    simpa only [physicalId,out.physicalId] using physical.live
  have entryEq : CurrentCallResourceLenBoolCurrent.entry out preparedReady=physical.entry:=
    (Prod.mk.inj (Option.some.inj ((CurrentCallResourceLenBoolCurrent.live out preparedReady returned).symm.trans livePhysical))).2
  let currentReleased:=reindex_released released prepared.physical.id prepared.physical.offset.toNat out.physicalId
    (congrArg UInt64.toNat out.physicalOffset) physical.offset physical.entry
    (out.physicalOffset.trans physicalOffset.symm) entryEq
  have parentIssued : SpatialDelegation returned.machine (CurrentCallResourceLenReturn.postTracker out preparedReady)
      prepared.physical.id currentB.allocation currentB.precise.completion prepared.V.pointer.grant:=by
    change SpatialDelegation returned.machine (CurrentCallResourceLenReturn.postTracker out preparedReady)
      prepared.physical.id B.allocation B.precise.completion prepared.V.pointer.grant
    rw [bAllocation,bCompletion]
    simpa only [out.physicalId] using CurrentCallResourceLenBoolCurrent.parent_issued out preparedReady returned
  have parentBinding : PointerBinds currentB.allocation prepared.V.pointer:=by
    change PointerBinds B.allocation prepared.V.pointer
    rw [bAllocation]
    exact CurrentCallResourceLenBoolCurrent.parent_binding out preparedReady returned
  obtain ⟨final,trace,terminal,terminalEmpty⟩:=CurrentCallResourceRejectedReturn.complete out preparedReady returned currentB physical
    pointer physicalId physicalOffset binding parentIssued parentBinding currentReleased rfl rfl rfl gt
  let cfg:=config options (remaining+1) span
  let installed:=Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨cfg,limits,fun _ _=>True⟩
  have entry : CallSafety.IsCallEntry 1 installed:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [terminalEmpty];decide
  exact ⟨installed,final,actualEntry,trace,terminal,terminalEmpty,
    SuccessfulTrace.no_errors context 1 installed final entry trace past,
    SuccessfulTrace.no_ub context 1 installed final entry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.CurrentCallResourceRejectedSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceRejectedSafety" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual resource rejected safety dependency {dependency}"
