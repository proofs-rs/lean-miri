import duplicate_prefix.CurrentCallEmptyProtocolEntry
import duplicate_prefix.CurrentCallEmptyNonliveCopy
import duplicate_prefix.CurrentCallEmptyNonliveResources
import duplicate_prefix.CurrentCallEmptyNonliveContinuation
import duplicate_prefix.CurrentCallResourcePreparedEntry
import duplicate_prefix.CurrentCallSelectedBorrowTagOrigin
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CurrentCallEmptyNonliveSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section
/-- All metadata-backed absent concrete source representations share one actual
entry and one optional-ledger continuation. No source allocation/family or
source permission is required, for either count branch. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before) (enabled : before.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (sourceId : AllocId) (parentTag : BorTag) (base sourceOffset count : UInt64) (nonnull : base+sourceOffset≠0)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory sourceId (some parentTag))
    (absent : before.memory.live.find? (fun row=>row.1==sourceId)=none)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (data : Identities) (owner : Nat) (B : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+6<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (dynamicFuel validationFuel budget : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (base+sourceOffset)))) 0 count place := by
  let prepared:=CurrentCallPush.preparedMachine before #[]
  let root:=CurrentCallSpatialEntryControl.root before #[] place model.noDataRace
  have preparedModel:=CurrentCallResourcePreparedEntry.model model #[]
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have frameBorrow : root.frame.extra.borrowTracker=some ({} : FrameState):=
    RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot before).2 tracker enabled
  have fresh : tracker.global.nextPointerTag.value<18446744073709551615:=UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  obtain ⟨copyCtx⟩:=(DuplicatePrefixCallModel.contexts options remaining span before model).1
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span before model).2.2.2
  obtain ⟨sourceFn,copy,sourceMemory,sourceUser,sourceThreads,sourceRace,sourceTracked⟩:=
    CurrentCallEmptyNonliveCopy.copy options limits remaining span copyCtx prepared tracker preparedModel origins #[] root {} frameBorrow
      sourceId parentTag base sourceOffset nonnull cached metadata absent fresh dynamicFuel validationFuel dynamicEq validationEq
  let next : MachineHooks.BorrowState:=⟨(registered tracker.global {} sourceId fresh).1,.FnEntry⟩
  let source : Before:={sourceFn with borrowTracker:=some {next with retagMode:=tracker.retagMode}}
  have sourceMem : source.memory=before.memory:=sourceMemory
  have sourceUserEq : source.user=prepared.user:=sourceUser
  have sourceTracker : source.borrowTracker=some {next with retagMode:=tracker.retagMode}:=rfl
  obtain ⟨P,pointerP,allocationP,preciseP,runtimeP⟩:=CurrentCallEmptyNonliveResources.registered B runtime {} sourceId fresh source sourceMem
  let physicalP : CandidateCurrentBoolUninitWrite.PhysicalWindow source place:={physical with
    live:=by rw [sourceMem];exact physical.live
    cachedBase:=by rw [sourceUserEq];exact physical.cachedBase}
  have freshP : next.global.nextPointerTag.value<18446744073709551615:=by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value];omega
  let sourceFrame:=({} : FrameState).addProtector sourceId tracker.global.nextPointerTag
  let input:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
  let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId tracker.global.nextPointerTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
  obtain ⟨output,child,machine,nextData,nextOwner,Q,entered,tracked,pointerQ,runtimeQ,rootsQ,shortQ,node,nodeAt,nodeTag,leaf,hidden,activity,
    parentIssued,parentBinding,returnPlace,edge,actual,⟨witness⟩,outputTag,constructor,constructorPresent,rootTag,extra,live,
    scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady,userEq,threadsEq,raceEq,memoryEq,global,mutation,snapshot⟩:=
    CurrentCallEmptyProtocolEntry.init_current_of_copy options limits remaining span ctx before tracker #[] place model.noDataRace stackReady model.debugOff
      input updated count sourceFn source next sourceFrame enabled sourceTracked rfl model.ghostOff model.shallow
      (by rw [sourceUser];exact model.ghostOff) (by rw [sourceUser];exact model.shallow)
      (by rw [sourceRace];exact model.noDataRace) (by rw [sourceUser];exact preparedModel.noBackend)
      validationFuel validationEq copy physicalP data owner P
      (pointer.trans (congrArg PointerInstance.value pointerP).symm) (allocation.trans allocationP.symm) runtimeP (by
        change CandidateCallBindings.WindowBinding source physical.pointer physical.id physical.offset.toNat 1
        unfold CandidateCallBindings.WindowBinding
        rw [sourceMem,sourceUserEq]
        exact binding)
      (by rw [allocationP];exact distinct) freshP (by rw [allocationP];exact nodeRoom) (ready.transport (by rw [sourceUserEq];rfl)) rfl
  have mode : tracker.retagMode=.Default:=by
    obtain ⟨old,found,mode⟩:=model.defaultTracker
    have same : old=tracker:=Option.some.inj (found.symm.trans enabled)
    simpa only [same] using mode
  have currentModel : DuplicatePrefixCallModel.Model options remaining span machine:=by
    refine ⟨model.debugOff,model.preciseOff,model.implicitOff,?_,?_,⟨⟨output.global,tracker.retagMode⟩,tracked,mode⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
    · rw [userEq,sourceUserEq];exact preparedModel.ghostOff
    · rw [userEq,sourceUserEq];exact preparedModel.shallow
    · rw [raceEq,sourceRace];exact model.noDataRace
    · rw [userEq,sourceUserEq];exact preparedModel.noBackend
    · rw [userEq,sourceUserEq];exact preparedModel.metadata
    · rw [threadsEq,sourceThreads];exact preparedModel.fixedScheduler
    · rw [userEq,sourceUserEq];exact preparedModel.unchecked
    · rw [userEq,sourceUserEq];exact preparedModel.noGc
  have sourceDifferent : physical.id≠sourceId:=S03NonliveEmptyMetadata.separate before.memory sourceId physical.id physical.entry absent physical.live
  have currentAbsent : machine.memory.live.find? (fun row=>row.1==sourceId)=none:=by
    rw [live];exact S03NonliveEmptyMetadata.live_replace_absent source.memory sourceId physical.id _ (by rw [sourceMem];exact absent) sourceDifferent
  have currentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata machine.memory sourceId (some parentTag):=by
    rw [memoryEq];exact S03NonliveEmptyMetadata.replace source.memory sourceId physical.id _ _ (by rw [sourceMem];exact metadata) (by rw [sourceMem];exact absent) sourceDifferent
  have sourceBeforeB : tracker.global.nextPointerTag.value.toNat<next.global.nextPointerTag.value.toNat:=by
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value];omega
  have sourceHidden : ∀index current,Q.allocation.extra.nodes.get index=some current→current.tag=tracker.global.nextPointerTag→current.isExposed=false:=by
    intro index current found same
    apply False.elim
    apply CurrentCallSelectedBorrowTagOrigin.written_node_absent P runtimeP sourceFrame freshP (by rw [allocationP];exact distinct)
      (by rw [allocationP];exact nodeRoom) physical.offset rfl output child actual witness tracker.global.nextPointerTag
      (by rw [allocationP];exact runtime.below.mapping) sourceBeforeB index current (by rw [extra] at found;exact found) same
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : machine.threads.activeThread?=some thread:=by
    rw [threadsEq,sourceThreads];exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  have grant : Q.pointer.grant=child:=by rw [pointerQ];rfl
  have value : Q.pointer.value.provenance=.concrete physical.id output.tag:=by rw [pointerQ];rfl
  let core : CurrentCallEmptyContinuation.Core options remaining span place machine ⟨output.global,tracker.retagMode⟩ nextData nextOwner physical.id physical.offset.toNat B.pointer Q scalar:={
    originalId:=B.pointerId,binding:=scalarBinding,idEq:=scalarId,offsetEq:=congrArg UInt64.toNat scalarOffset,
    pointerEq:=scalarPointer.trans pointer,allocationEq:=scalarAllocation,
    parentIssued:=by rw [pointerP] at parentIssued;exact parentIssued,
    parentBinding:=by rw [pointerP] at parentBinding;exact parentBinding,
    runtime:=runtimeQ,roots:=rootsQ,short:=shortQ,concrete:=⟨physical.id,output.tag,value⟩,
    node:=node,nodeAt:=by rw [grant];exact nodeAt,hidden:=hidden,active:=by rw [grant,scalarOffset];exact activity,
    source:=some (sourceId,tracker.global.nextPointerTag),ledger:=.nonlive sourceId tracker.global.nextPointerTag (some parentTag) currentMetadata currentAbsent sourceHidden,
    borrowFrame:=sourceFrame.addProtector physical.id output.tag,tags:=by rw [nodeTag];rfl,
    edge:=by rw [grant];rw [pointerP] at edge;exact edge,model:=currentModel,tracked:=tracked,thread:=thread,activeThread:=active,physicalReady:=scalarReady}
  have currentOrigins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types:=by rw [userEq,sourceUserEq];exact origins
  have currentBase : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩:=by rw [userEq,sourceUserEq];exact cached
  have counter : output.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2:=by
    rw [global]
    change (TypedRetagEmpty.successorTag next.global.nextPointerTag freshP).value.toNat=_
    rw [GenericFunctionEntryNumerics.successor_value]
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat+1=_
    rw [GenericFunctionEntryNumerics.successor_value]
  have borrowCore : core.borrowFrame=sourceFrame.addProtector physical.id core.node.tag:=by
    change sourceFrame.addProtector physical.id output.tag=sourceFrame.addProtector physical.id node.tag
    rw [nodeTag]
  obtain ⟨final,trace,terminal,empty⟩ : ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root updated sourceFrame count physical.id output.tag) machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[]:=by
    by_cases zero : count=0
    · subst count
      have done:=CurrentCallEmptyContinuation.zero core limits root updated sourceFrame raw borrowCore rfl rfl rfl validationFuel validationEq
      simpa only [show core.node.tag=output.tag from nodeTag] using done
    · have done:=CurrentCallEmptyContinuation.nonlive core limits root raw sourceFrame borrowCore rfl rfl rfl sourceId tracker.global.nextPointerTag (some parentTag)
        base sourceOffset count nonnull zero currentMetadata currentAbsent currentBase (by change _<output.global.nextPointerTag.value.toNat;rw [counter];omega)
        (by change output.global.nextPointerTag.value.toNat+4<_;rw [counter];omega) runtimeQ.below.protectors
        (UInt64.lt_iff_toNat_lt.mpr (by change output.global.nextPointerTag.value.toNat<18446744073709551615;rw [counter];omega)) currentOrigins
        dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
        (by change output.global.nextPointerTag.value.toNat+1<_;rw [counter];omega) rfl
      simpa only [updated,show core.node.tag=output.tag from nodeTag,actual_access_runtime] using done
  let start:=Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root updated sourceFrame count physical.id output.tag) machine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [empty];decide
  exact ⟨start,final,entered,trace,terminal,empty,SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
end
end DuplicatePrefix.CurrentCallEmptyNonliveSafety
