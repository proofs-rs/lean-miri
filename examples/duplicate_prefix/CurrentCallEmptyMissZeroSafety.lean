import duplicate_prefix.CurrentCallEmptyMissCurrent
import duplicate_prefix.CurrentCallResourceSingleBoolRelease
import duplicate_prefix.CurrentCallResourceRootFinish
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CurrentCallEmptyMissZeroSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
private theorem tick_model (options remaining span machine)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span machine) := by
  have flags:=RootZeroCompleteState.tick_flags options remaining span machine
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (enabled : before.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (address : UInt64) (nonzero : address≠0)
    (addressMode : before.user.addresses.provenanceMode≠.strict)
    (miss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types) :


    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 0 place := by
  obtain ⟨output,child,machine,nextData,nextOwner,Q,window,entered,modelAfter,threads,tracked,windowPointer,windowId,windowOffset,windowAllocation,
    windowBinding,windowReady,grantQ,pointerQ,runtimeQ,distinctQ,shortQ,node,nodeAt,nodeTag,leaf,hidden,activeQ,edge,parentIssued,parentBinding,checkpoint,queryMiss⟩ :=
    CurrentCallEmptyMissCurrent.invoke options limits remaining span before tracker model enabled #[] stackReady address 0 nonzero addressMode miss place physical
      data owner B pointer allocation runtime binding distinct tagRoom nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins
  let root:=CurrentCallSpatialEntryControl.root before #[] place model.noDataRace
  let installed:=CurrentCallEmptyMissFacts.frame options remaining span (CurrentCallPush.preparedMachine before #[]) tracker root address 0 physical.id output.tag miss
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  obtain ⟨result,traceBefore,body,identity,callee,size,located,slot0,returnPlace,extra,continuation,varargs,immediate⟩ :=
    CurrentCallEmptyMissFacts.zero_prefix options remaining span (CurrentCallPush.preparedMachine before #[]) tracker root address physical.id output.tag miss
      limits raw machine modelAfter validationFuel validationEq
  let beforeReturn:=RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine)
  let held : MachineHooks.BorrowState:=⟨output.global,tracker.retagMode⟩
  have memory : beforeReturn.memory=machine.memory := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have addresses : beforeReturn.user.addresses=machine.user.addresses := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have extras : beforeReturn.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators] <;>rfl
  have enabledNow : beforeReturn.borrowTracker=some held := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact tracked
  have present : Present (ActualWorld beforeReturn) physical.id Q.allocation := by
    unfold Present ActualWorld
    rw [memory]
    exact Q.present
  let afterB : UniformWindow beforeReturn held nextData nextOwner physical.id physical.offset.toNat 1 .ret := {Q with
    present:=present
    issued:=CurrentCallAllocationLicense.spatial Q.issued beforeReturn held Q.allocation present rfl rfl rfl rfl
      (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
      Q.precise.completion (by intro root origin edge;exact edge)}
  obtain ⟨P,pointerEq,idEq,offsetEq,entryEq,bindingP⟩ := CurrentCallRootPhysicalWindow.view (final:=beforeReturn) window windowBinding addresses (congrArg MemoryState.live memory)
  have physId : P.id=physical.id:=idEq.trans windowId
  have physOffset : P.offset=physical.offset:=offsetEq.trans windowOffset
  have physAllocation : P.entry.allocation=Q.allocation:=(congrArg LocalAllocation.allocation entryEq).trans windowAllocation
  have currentAt : afterB.allocation.extra.nodes.get afterB.pointer.grant=some node := by
    change Q.allocation.extra.nodes.get Q.pointer.grant=some node
    rw [grantQ];exact nodeAt
  have currentActive : GeneralBorrowFreshActiveWithin.ActiveWithin afterB.allocation.extra afterB.pointer.grant .Write P.offset (P.offset+1) := by
    change GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write P.offset (P.offset+1)
    rw [grantQ,physOffset];exact activeQ
  let frame : FrameState:=({} : FrameState).addProtector physical.id output.tag
  have tags : frame.protectedTags=#[(physical.id,node.tag)] := by rw [nodeTag];rfl
  have currentEdge : afterB.precise.completion.parents[afterB.pointer.grant.toNat]?=some (some B.pointer.grant) := by
    change Q.precise.completion.parents[Q.pointer.grant.toNat]?=_
    rw [grantQ];exact edge
  have bLive : beforeReturn.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,P.entry) := by rw [←physId];exact P.live
  obtain ⟨released⟩ := CurrentCallResourceSingleBoolRelease.release afterB runtimeQ distinctQ shortQ
    ⟨physical.id,output.tag,by change Q.pointer.value.provenance=_;rw [pointerQ]⟩ node currentAt hidden frame tags B.pointer.grant currentEdge
    P.offset (congrArg UInt64.toNat physOffset) currentActive P.entry bLive physAllocation
  have parentNow : SpatialDelegation beforeReturn held physical.id afterB.allocation afterB.precise.completion B.pointer.grant :=
    CurrentCallAllocationLicense.spatial parentIssued beforeReturn held Q.allocation present rfl rfl rfl rfl
      (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
      Q.precise.completion (by intro root origin edge;exact edge)
  obtain ⟨thread,oldActive,_⟩:=stackReady
  let currentThread:={thread with topUserRelevantFrame:=some 0}
  have activeNow : beforeReturn.threads.activeThread?=some currentThread := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators,threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 oldActive
  obtain ⟨rootBody,rootIdentity,rootCallee,rootContinuation,rootReturnPlace,rootVarargs,rootClocks,rootBorrow,rootLocation⟩ :=
    CurrentCallEmptyMissFacts.metadata options remaining span (CurrentCallPush.preparedMachine before #[]) tracker root address 0 physical.id output.tag miss
  have frameTracked : result.extra.borrowTracker=some frame := by rw [extra];exact rootBorrow
  have noClocks : result.extra.dataRace=none := by rw [extra];exact rootClocks.trans root.noClocks
  have stop : result.returnContinuation=.stop true := continuation.trans rootContinuation
  have va : result.vaList=#[]:=varargs.trans rootVarargs
  have destination : result.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩ := by rw [returnPlace,rootReturnPlace];rfl
  have samePointer : P.pointer=B.pointer.value:=pointerEq.trans (windowPointer.trans pointer)
  have readyNow : CurrentCallBoolProtection.WindowReady beforeReturn P.id P.offset.toNat 1 := by rw [idEq,offsetEq];exact windowReady.transport extras
  obtain ⟨final,returned,terminal,emptyStack⟩ := CurrentCallResourceRootFinish.finish options limits remaining span place B afterB P bindingP physId
    (congrArg UInt64.toNat physOffset) samePointer parentNow parentBinding result frame released
    (tick_model options remaining span _ (tick_model options remaining span _ modelAfter)) enabledNow frameTracked currentThread activeNow
    body located size noClocks stop va immediate true slot0 destination readyNow validationFuel validationEq
  let start:=Storage.withCurrent #[] installed machine
  have trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits start final:=SuccessfulTrace.append traceBefore returned
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [emptyStack];decide
  exact ⟨start,final,entered,trace,terminal,emptyStack,
    SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
end
end DuplicatePrefix.CurrentCallEmptyMissZeroSafety
