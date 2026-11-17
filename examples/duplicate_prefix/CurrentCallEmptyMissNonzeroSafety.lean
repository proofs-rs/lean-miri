import duplicate_prefix.CurrentCallEmptyMissBodyControl
import duplicate_prefix.CurrentCallEmptyIntegerCounterFrame
import duplicate_prefix.CurrentCallEmptyMissCurrent
import duplicate_prefix.CurrentCallResourceSingleBoolRelease
import duplicate_prefix.CurrentCallResourceRootFinish
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CurrentCallEmptyMissNonzeroSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (enabled : before.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (address count : UInt64) (countNonzero : count≠0) (nonzero : address≠0)
    (addressMode : before.user.addresses.provenanceMode≠.strict)
    (miss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+3<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :


    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  obtain ⟨output,child,machine,nextData,nextOwner,Q,window,entered,modelAfter,threads,tracked,windowPointer,windowId,windowOffset,windowAllocation,
    windowBinding,windowReady,grantQ,pointerQ,runtimeQ,distinctQ,shortQ,node,nodeAt,nodeTag,leaf,hidden,activeQ,edge,parentIssued,parentBinding,checkpoint,queryMiss⟩ :=
    CurrentCallEmptyMissCurrent.invoke options limits remaining span before tracker model enabled #[] stackReady address count nonzero addressMode miss place physical
      data owner B pointer allocation runtime binding distinct (by omega) nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins
  let root:=CurrentCallSpatialEntryControl.root before #[] place model.noDataRace
  let installed:=CurrentCallEmptyMissFacts.frame options remaining span (CurrentCallPush.preparedMachine before #[]) tracker root address count physical.id output.tag miss

  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have entryNat:=checkpoint.counter
  have currentOrigins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types := by rw [checkpoint.user];exact origins
  have currentAddressMode : machine.user.addresses.provenanceMode≠.strict := by rw [checkpoint.user];exact addressMode
  let held : MachineHooks.BorrowState:=⟨output.global,tracker.retagMode⟩
  have helperRoom : held.global.nextPointerTag.value.toNat+1<18446744073709551615 := by change output.global.nextPointerTag.value.toNat+1<_ ;rw [entryNat];omega
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have activeBefore : machine.threads.activeThread?=some thread := by
    rw [threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  obtain ⟨result,beforeReturn,finalTracker,traceBefore,body,identity,callee,extra,returnPlace,continuation,varargs,_,size,located,slot0,immediate,
    memory,enabledNow,modeEq,globalShape,nextNat,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,⟨finalThread,activeNow⟩⟩ :=
    CurrentCallEmptyMissBodyControl.to_return options limits remaining span (CurrentCallPush.preparedMachine before #[]) tracker root address count physical.id output.tag miss
      raw machine held tracked modelAfter currentOrigins nonzero countNonzero currentAddressMode queryMiss helperRoom dynamicFuel validationFuel dynamicEq validationEq budget dispatchEq thread activeBefore rfl
  obtain ⟨afterB,pointerB,allocationB,preciseB,runtimeB⟩ := CurrentCallEmptyIntegerCounterFrame.window Q runtimeQ beforeReturn finalTracker memory globalShape (by
      rw [nextNat]
      change output.global.nextPointerTag.value.toNat≤output.global.nextPointerTag.value.toNat+2
      omega)
  obtain ⟨P,pointerEq,idEq,offsetEq,entryEq,bindingP⟩ := CurrentCallRootPhysicalWindow.view (final:=beforeReturn) window windowBinding addresses (congrArg MemoryState.live memory)
  have physId : P.id=physical.id:=idEq.trans windowId
  have physOffset : P.offset=physical.offset:=offsetEq.trans windowOffset
  have physAllocation : P.entry.allocation=afterB.allocation:=(congrArg LocalAllocation.allocation entryEq).trans (windowAllocation.trans allocationB.symm)
  have currentAt : afterB.allocation.extra.nodes.get afterB.pointer.grant=some node := by rw [allocationB,pointerB,grantQ];exact nodeAt
  have currentActive : GeneralBorrowFreshActiveWithin.ActiveWithin afterB.allocation.extra afterB.pointer.grant .Write P.offset (P.offset+1) := by
    rw [allocationB,pointerB,grantQ,physOffset];exact activeQ
  let frame : FrameState:=({} : FrameState).addProtector physical.id output.tag
  have tags : frame.protectedTags=#[(physical.id,node.tag)] := by rw [nodeTag];rfl
  have currentEdge : afterB.precise.completion.parents[afterB.pointer.grant.toNat]?=some (some B.pointer.grant) := by rw [preciseB,pointerB,grantQ];exact edge
  have bLive : beforeReturn.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,P.entry) := by rw [←physId];exact P.live
  obtain ⟨released⟩ := CurrentCallResourceSingleBoolRelease.release afterB runtimeB (by rw [allocationB];exact distinctQ) (by rw [allocationB];exact shortQ)
    ⟨physical.id,output.tag,by rw [pointerB,pointerQ]⟩ node currentAt hidden frame tags B.pointer.grant currentEdge P.offset (congrArg UInt64.toNat physOffset) currentActive P.entry bLive physAllocation
  have parentNow : SpatialDelegation beforeReturn finalTracker physical.id afterB.allocation afterB.precise.completion B.pointer.grant := by
    rw [allocationB,preciseB]
    have present : Present (ActualWorld beforeReturn) physical.id Q.allocation := by unfold Present ActualWorld;rw [memory];exact Q.present
    exact CurrentCallAllocationLicense.spatial parentIssued beforeReturn finalTracker Q.allocation present (by rw [globalShape];rfl) rfl rfl rfl
      (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
      Q.precise.completion (by intro root origin edge;exact edge)
  have parentBindingNow : PointerBinds afterB.allocation B.pointer := by rw [allocationB];exact parentBinding
  obtain ⟨rootBody,rootIdentity,rootCallee,rootContinuation,rootReturnPlace,rootVarargs,rootClocks,rootBorrow,rootLocation⟩ :=
    CurrentCallEmptyMissFacts.metadata options remaining span (CurrentCallPush.preparedMachine before #[]) tracker root address count physical.id output.tag miss
  have frameTracked : result.extra.borrowTracker=some frame := by rw [extra];exact rootBorrow
  have noClocks : result.extra.dataRace=none := by rw [extra];exact rootClocks.trans root.noClocks
  have stop : result.returnContinuation=.stop true := continuation.trans rootContinuation
  have va : result.vaList=#[]:=varargs.trans rootVarargs
  have destination : result.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩ := by rw [returnPlace,rootReturnPlace];rfl
  have samePointer : P.pointer=B.pointer.value:=pointerEq.trans (windowPointer.trans pointer)
  have readyNow : CurrentCallBoolProtection.WindowReady beforeReturn P.id P.offset.toNat 1 := by rw [idEq,offsetEq];exact windowReady.transport extras
  have finalMode : finalTracker.retagMode=.Default := by
    obtain ⟨old,enabled,mode⟩:=modelAfter.defaultTracker
    have same : old=held:=Option.some.inj (enabled.symm.trans tracked)
    subst old
    exact modeEq.trans mode
  have finalModel : DuplicatePrefixCallModel.Model options remaining span beforeReturn :=
    ⟨modelAfter.debugOff,modelAfter.preciseOff,modelAfter.implicitOff,ghost,shallow,⟨finalTracker,enabledNow,finalMode⟩,race,backend.trans modelAfter.noBackend,
      by rw [types];exact modelAfter.metadata,fixed,unchecked,noGc,modelAfter.nullComparator,modelAfter.sourceMatches⟩
  obtain ⟨final,returned,terminal,emptyStack⟩ := CurrentCallResourceRootFinish.finish options limits remaining span place B afterB P bindingP physId
    (congrArg UInt64.toNat physOffset) samePointer parentNow parentBindingNow result frame released finalModel enabledNow frameTracked finalThread activeNow
    (body.trans (rootBody.trans root.body)) located size noClocks stop va immediate false slot0 destination readyNow validationFuel validationEq
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
end DuplicatePrefix.CurrentCallEmptyMissNonzeroSafety
