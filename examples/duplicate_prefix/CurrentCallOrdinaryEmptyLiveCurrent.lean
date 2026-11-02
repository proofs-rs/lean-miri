import duplicate_prefix.CurrentCallOrdinaryEmptyNonliveCurrent
import duplicate_prefix.CurrentCallOrdinaryLiveCurrentSafety
import duplicate_prefix.CurrentCallEmptyPointerDifferentFinish
import duplicate_prefix.ConcretePoolRootCopy
import duplicate_prefix.WildcardPoolHitRootCopy
import duplicate_prefix.S04ZeroConcreteRuntime
import duplicate_prefix.S04ZeroWildcardRuntime
import duplicate_prefix.CurrentCallEmptyEntrySourceData
import duplicate_prefix.CurrentCallEmptyLiveSourceCopy

namespace DuplicatePrefix.CurrentCallOrdinaryEmptyLiveCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver GeneralBorrowFnEntryRegistration CurrentCallOrdinaryInput
open CandidateStableCallOwnership CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
open Lean Elab Term in
elab "empty_live_current_rule " suffix:str : term => do
  let found:=(←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected unique checked empty LIVE/CURRENT helper {suffix.getString}"

private theorem phase {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (sourceId : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry))
    (sourceBase : UInt64) (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,sourceBase⟩)
    (query : CurrentCallConversionPlan.sourceQuery before argument 0=.ok (some sourceId))
    (fresh : input.tracker.global.nextPointerTag.value<18446744073709551615)
    (sourceMachine : Before) (tree : BorrowTree) (frame : CompilerFrameContext.ActualFrame)
    (tracked : sourceMachine.borrowTracker=some ⟨(registered input.tracker.global {} sourceId fresh).1,input.tracker.retagMode⟩)
    (memory : sourceMachine.memory=RetagEntry.updatedMemory before.memory sourceId entry tree)
    (user : sourceMachine.user=(CurrentCallPush.preparedMachine before #[]).user)
    (threads : sourceMachine.threads=(CurrentCallPush.preparedMachine before #[]).threads)
    (race : sourceMachine.dataRace=none)
    (frameBorrow : frame.extra.borrowTracker=some (({} : FrameState).addProtector sourceId input.tracker.global.nextPointerTag)) :
    ∃D : CurrentCallConversionBoolPhase.CurrentData sourceMachine
        ⟨(registered input.tracker.global {} sourceId fresh).1,input.tracker.retagMode⟩ #[] frame
        (({} : FrameState).addProtector sourceId input.tracker.global.nextPointerTag) place,
      D.family=input.returnFamily ∧D.offset=input.returnOffset ∧∃P : CurrentCallConversionBoolPhase.FirstPhase input D,P.reserve=14 := by
  let sourceTracker : MachineHooks.BorrowState:=⟨(registered input.tracker.global {} sourceId fresh).1,input.tracker.retagMode⟩
  have different : sourceId≠input.returnFamily.allocation := by
    intro equal
    rw [equal,latent.1] at live
    cases live
  have counter : sourceTracker.global.nextPointerTag.value.toNat=input.tracker.global.nextPointerTag.value.toNat+1 :=
    GenericFunctionEntryNumerics.successor_value _ fresh
  have freshB : sourceTracker.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have room:=input.resources.tagRoom
    change sourceTracker.global.nextPointerTag.value.toNat<18446744073709551615
    rw [counter];omega
  have boolAbsent : sourceMachine.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=none := by
    rw [memory]
    change ((before.memory.live.filter (fun row=>row.1!=sourceId)).push (sourceId,{entry with allocation:=entry.allocation.setExtra tree})).find? _=none
    rw [CurrentCallOtherAllocationWindow.lookup _ _ _ _ different]
    exact latent.1
  obtain ⟨D,family,offset,current⟩:=CurrentCallConversionBoolPhase.from_initial (frames:=#[]) input latent tracked frameBorrow freshB boolAbsent
    (by rw [memory];rfl) (by rw [memory];rfl) (by rw [memory];rfl) (by rw [user];rfl) (by rfl)
    (by intro root rootCached;have old:=(empty_live_current_rule "CurrentCallOrdinaryEmptyNonliveCurrent.cached_below") input _ root rootCached;rw [counter];omega)
    ((empty_live_current_rule "CurrentCallOrdinaryEmptyNonliveCurrent.registered_protectors") input.tracker.global {} sourceId fresh input.protectorsBelow)
    (by change InitialRegistryVacant sourceMachine input.returnFamily.allocation;unfold InitialRegistryVacant;rw [user];exact latent.2.2.2.1)
    race (by rw [user];exact input.model.ghostOff) (by rw [user];exact input.model.noBackend)
  have retQuery : CurrentCallConversionPlan.returnQuery before place=.ok (some input.returnFamily.allocation) := by
    have q:=CurrentCallConversionPlanAdequacy.query_of_selected before input.tracker input.returnFamily input.returnOffset
      input.returnCapacity 1 false input.returnRepresentation (.inr latent) (by decide)
    simpa only [CurrentCallConversionPlan.returnQuery,input.returnEncoding,Pointer.withOptionalProvenance] using q
  have sourcePayload:=CurrentCallConversionPlan.payload_live before sourceId entry live
  have boolPayload : CurrentCallConversionPlan.payload before input.returnFamily.allocation=some D.source :=
    CurrentCallConversionPlanAdequacy.payload_of_current before _ D.source latent.1 latent.2.1 latent.2.2.1 current
  have head : CurrentCallConversionPlan.selectedPayloads before argument 0 place=D.source::[] := by
    unfold CurrentCallConversionPlan.selectedPayloads CurrentCallConversionPlan.selectedRows
    rw [query,retQuery]
    change (CurrentCallConversionPlan.rowsFromIds before (some sourceId) (some input.returnFamily.allocation)).map Prod.snd=[D.source]
    simp [CurrentCallConversionPlan.rowsFromIds,sourcePayload,boolPayload]
  have phaseMemory : D.registered.machine.memory=RetagEntry.updatedMemory before.memory sourceId entry tree := memory
  have phaseAddresses : D.registered.machine.user.addresses=before.user.addresses := by change sourceMachine.user.addresses=before.user.addresses;rw [user];rfl
  let P : CurrentCallConversionBoolPhase.FirstPhase input D := {
    infoEq:=by intro id;rw [phaseMemory];exact (empty_live_current_rule "CurrentCallOrdinaryLiveCurrentSafety.info_tree") before.memory sourceId entry tree live id
    addresses:=phaseAddresses
    tape:=by change sourceMachine.user.payload.payload.user.choices=before.user.payload.payload.user.choices;rw [user];rfl
    thread:=by change sourceMachine.threads.activeThread=before.threads.activeThread;rw [threads];rfl
    roots:=by intro id;rfl
    spent:=2,reserve:=14,room:=by decide,positive:=by decide
    counter:=by
      change (TypedRetagEmpty.successorTag sourceTracker.global.nextPointerTag D.fresh).value.toNat≤_
      rw [GenericFunctionEntryNumerics.successor_value,counter];omega
    metadata:=by
      intro id member
      exact CurrentCallConversionTargetMetadataFrame.transport before D.registered.machine sourceId
        {entry with allocation:=entry.allocation.setExtra tree} phaseMemory ⟨⟨sourceId,sourceBase⟩,cached⟩
        (by intro query base found;rw [phaseAddresses];exact found) id (CurrentCallOrdinaryConversionSelected.targets_metadata input id member)
    rest:=[],head:=head}
  exact ⟨D,family,offset,P,rfl⟩

private theorem finish_source {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (sourceId : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry))
    (base sourceOffset count : UInt64) (nonnull : base+sourceOffset≠0)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩)
    (query : CurrentCallConversionPlan.sourceQuery before argument 0=.ok (some sourceId))
    (fresh : input.tracker.global.nextPointerTag.value<18446744073709551615)
    (sourceFn : Before) (sourceTree : BorrowTree)
    (sourceMemory : sourceFn.memory=RetagEntry.updatedMemory before.memory sourceId entry sourceTree)
    (sourceUser : sourceFn.user=(CurrentCallPush.preparedMachine before #[]).user)
    (sourceThreads : sourceFn.threads=(CurrentCallPush.preparedMachine before #[]).threads)
    (sourceRace : sourceFn.dataRace=before.dataRace)
    (sourceTracked : sourceFn.borrowTracker=some ⟨(registered input.tracker.global {} sourceId fresh).1,.FnEntry⟩)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceTree (registered input.tracker.global {} sourceId fresh).1)
    (sourceLeaf : CurrentCallEmptyEntrySourceData.Leaf sourceTree input.tracker.global.nextPointerTag)
    (sourceGrowth : sourceTree.nodes.size≤entry.allocation.extra.nodes.size+1) :
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let inputValue:=(DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument 0 ActualReferenceMetadata.reference).imm
    let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete sourceId input.tracker.global.nextPointerTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate inputValue,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace 0 (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent #[] (firstLive root).frame (ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry))=
      .ok () (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.sourceRoot root updated
        (({} : FrameState).addProtector sourceId input.tracker.global.nextPointerTag)).frame sourceFn)→
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  intro root inputValue updated copy
  let prepared:=CurrentCallPush.preparedMachine before #[]
  have preparedModel:=CurrentCallResourcePreparedEntry.model input.model #[]
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have workPositive : 0<DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
  let dynamicFuel:=options.place.dynamicFuel-1
  let validationFuel:=options.limits.validation-1
  let budget:=limits.callDispatch-1
  have dynamicEq : options.place.dynamicFuel=dynamicFuel+1 := by have room:=input.resources.dynamicFuel;dsimp only [dynamicFuel];omega
  have validationEq : options.limits.validation=validationFuel+1 := by have room:=input.resources.configuredFuel.2.2.2;dsimp only [validationFuel];omega
  have dispatchEq : limits.callDispatch=budget+1 := by have room:=input.resources.executionFuel.1;dsimp only [budget];omega
  let next : MachineHooks.BorrowState:=⟨(registered input.tracker.global {} sourceId fresh).1,.FnEntry⟩
  let source : Before:={sourceFn with borrowTracker:=some {next with retagMode:=input.tracker.retagMode}}
  let sourceFrame:=({} : FrameState).addProtector sourceId input.tracker.global.nextPointerTag
  let boolFrame:=(atSpan (RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot root updated sourceFrame) count) ⟨601⟩).frame
  have sourceModel : DuplicatePrefixCallModel.Model options remaining span source:=
    (empty_live_current_rule "CurrentCallOrdinaryEmptyNonliveCurrent.model_move") preparedModel sourceUser sourceThreads sourceRace rfl input.defaultMode
  have args:=CurrentCallEmptyProtocolControl.arguments options limits remaining span input.model.debugOff validationFuel validationEq #[] root raw
    prepared sourceFn input.tracker next input.runtime.enabled sourceTracked input.model.ghostOff input.model.shallow
    (by rw [sourceUser];exact preparedModel.ghostOff) (by rw [sourceUser];exact preparedModel.shallow)
    inputValue updated sourceFrame count copy
  obtain ⟨D,dFamily,dOffset,P,reserveEq⟩:=phase input latent sourceId entry live base cached query fresh source sourceTree boolFrame rfl sourceMemory sourceUser sourceThreads
    (sourceRace.trans input.model.noDataRace) (by rfl)
  obtain ⟨retagCtx⟩:=ActualRetagContext.exists_context options (remaining+1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨externStatic,wiring,finalAddresses,finalTape,result,⟨O⟩⟩:=CurrentCallConversionBoolPhase.first input retagCtx D P
  have postEq:=(empty_live_current_rule "CurrentCallOrdinaryEmptyNonliveCurrent.repack") O.stack
  have protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent #[] boolFrame source)=.ok ()
      (Storage.withCurrent #[] (registeredFrame boolFrame sourceFrame D.family.allocation next.global.nextPointerTag) O.post.machine) := by
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place _=_
    rw [←postEq]
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining+1) span retagCtx place input.returnLayout
      options.limits.retag limits.retag) _).symm.trans O.actual
  have entered:=CurrentCallEmptyProtocolControl.init_of_arguments options limits remaining span before #[] place input.model.noDataRace input.model.debugOff input.stackReady
    inputValue updated sourceFrame count source O.post.machine D.family.allocation next.global.nextPointerTag args protection
  have currentModel:=CurrentCallConversionBoolModel.model O sourceModel
  have currentOrigins:=CurrentCallConversionBoolModel.origins O (show DuplicatePrefixTypeCacheOrigins.Origins source.user.payload.payload.user.types by rw [sourceUser];exact input.cacheOrigins)
  have currentThreads : O.post.machine.threads=prepared.threads := (CurrentCallConversionBoolModel.threads O).trans sourceThreads
  have currentMemory:=CurrentCallConversionBoolModel.memory O
  let R:=O.output
  let BT : MachineHooks.BorrowState:={D.next with global:=result.global}
  have different : sourceId≠D.family.allocation := by
    rw [dFamily]
    intro same
    rw [same,latent.1] at live
    cases live
  let currentSourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind:={entry with allocation:=entry.allocation.setExtra sourceTree}
  have sourceLive : source.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,currentSourceEntry) := by
    rw [sourceMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have currentSourceLive : O.post.machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,currentSourceEntry) := by
    rw [CurrentCallConversionBoolModel.memory_other O sourceId different]
    exact sourceLive
  obtain ⟨_,_,_,registeredRuntime,_,_⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare sourceTree next.global sourceFrame D.family.allocation D.fresh sourceRuntime
  have registeredR : DuplicatePrefixBorrowContract.RuntimeFacts sourceTree D.next.global:=registeredRuntime
  have currentSourceRuntime:=CurrentCallZeroSharedBoolWindow.runtime_mono sourceTree D.next.global result.global registeredR result.flags result.counter
  obtain ⟨sourceIndex,sourceNode,sourceTagged,sourceAt,sourceTag,sourceChildren,sourceHiddenLeaf,sourceInactive⟩:=sourceLeaf
  have quiet:=CurrentCallResourceEmptyRootRelease.quiescent_of_inactive sourceTree sourceIndex sourceNode sourceInactive
  have sourceRoom : sourceTree.nodes.size+2≤4294967295 := by
    have old:=input.resources.nodeRoom (sourceId,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live))
    change entry.allocation.extra.nodes.size+16<65536 at old
    omega
  have sourceCounter : next.global.nextPointerTag.value.toNat=input.tracker.global.nextPointerTag.value.toNat+1 :=
    GenericFunctionEntryNumerics.successor_value _ fresh
  have rootHit : result.global.rootTag? D.family.allocation=some D.root := result.roots _ _ D.rootCached
  have initialRoot : input.tracker.global.rootTag? D.family.allocation=some D.root := D.rootCached
  have rootBeforeSource:=(empty_live_current_rule "CurrentCallOrdinaryEmptyNonliveCurrent.cached_below") input D.family.allocation D.root initialRoot
  have sourceHidden : ∀index node,R.window.allocation.extra.nodes.get index=some node→
      node.tag=input.tracker.global.nextPointerTag→node.isExposed=false := by
    have absentTag:=(empty_live_current_rule "CurrentCallOrdinaryEmptyNonliveCurrent.two_nodes_absent") R input.tracker.global.nextPointerTag O.nodes (by
      intro node found
      obtain ⟨rootNode,rootAt,_,_,cachedRoot⟩:=R.window.issued.capability.rootNode
      have equal : node=rootNode:=Option.some.inj (found.symm.trans rootAt)
      rw [O.id] at cachedRoot
      have tagEq : rootNode.tag=D.root:=Option.some.inj (cachedRoot.symm.trans rootHit)
      rw [equal,tagEq]
      exact rootBeforeSource) (by rw [O.tag];rw [sourceCounter];omega)
    intro index node found equal
    exact False.elim (absentTag index node found equal)
  obtain ⟨oldThread,oldActive,_⟩:=input.stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : O.post.machine.threads.activeThread?=some thread := by
    rw [currentThreads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  let ledger : CurrentCallEmptyLedgerRelease.SourceLedger O.post.machine R.window.allocation.extra
      (some (sourceId,input.tracker.global.nextPointerTag)):=
    .live sourceId input.tracker.global.nextPointerTag currentSourceEntry currentSourceLive sourceIndex sourceNode sourceTagged sourceAt sourceHiddenLeaf quiet sourceHidden
  let core:=CurrentCallEmptyReturnCore.of_return R (some (sourceId,input.tracker.global.nextPointerTag)) ledger
    (sourceFrame.addProtector R.id R.node.tag) rfl currentModel O.tracked thread active
  have borrowCore : core.borrowFrame=sourceFrame.addProtector R.id core.node.tag:=rfl
  have currentBase : O.post.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩:=
    CurrentCallConversionBoolModel.base_hit O sourceId ⟨sourceId,base⟩ (by change source.user.addresses.baseAddr.find? _=_;rw [sourceUser];exact cached)
  have sourceBelow : input.tracker.global.nextPointerTag.value.toNat<BT.global.nextPointerTag.value.toNat := by
    have nextCounter:=GenericFunctionEntryNumerics.successor_value next.global.nextPointerTag D.fresh
    have counter:=result.counter
    change (TypedRetagEmpty.successorTag next.global.nextPointerTag D.fresh).value.toNat≤result.global.nextPointerTag.value.toNat at counter
    rw [nextCounter,sourceCounter] at counter
    dsimp only [BT]
    omega
  have bodyRoom : BT.global.nextPointerTag.value.toNat+4<2^64 := by
    have room:=result.rootBudget
    change result.global.nextPointerTag.value.toNat+4<2^64
    omega
  have bodyFresh : BT.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have room:=bodyRoom
    change result.global.nextPointerTag.value.toNat+4<2^64 at room
    change result.global.nextPointerTag.value.toNat<18446744073709551615
    omega
  obtain ⟨final,trace,terminal,empty⟩ : ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root updated sourceFrame count R.id R.node.tag) O.post.machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
    by_cases zero : count=0
    · subst count
      exact CurrentCallEmptyContinuation.zero core limits root updated sourceFrame raw borrowCore rfl rfl rfl validationFuel validationEq
    · have done:=CurrentCallEmptyPointerDifferentFinish.finish options limits remaining span place R.original R.originalId R.window R.physical
        core.binding R.physicalId R.physicalOffset R.originalPointer.symm R.physicalAllocation R.originalIssued R.originalBinding R.runtime R.distinct R.short
        core.concrete R.node R.nodeAt R.hidden R.activity sourceId currentSourceEntry currentSourceLive (by rw [O.id];exact different)
        currentSourceRuntime sourceRoom input.tracker.global.nextPointerTag sourceIndex sourceNode sourceTagged sourceAt sourceHiddenLeaf quiet sourceHidden
        base sourceOffset count nonnull zero currentBase root raw
        (CurrentCallEmptyProtocolControl.frame root updated sourceFrame count R.id R.node.tag)
        (by exact CurrentCallEmptyProtocolControl.frame_some root updated {} sourceId input.tracker.global.nextPointerTag count R.id R.node.tag)
        rfl rfl rfl currentModel currentOrigins O.tracked thread active rfl R.edge core.physicalReady
        (by have room:=bodyRoom;change result.global.nextPointerTag.value.toNat+4<2^64 at room;change result.global.nextPointerTag.value.toNat+1<18446744073709551615;omega)
        dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
      simpa only [updated,actual_access_runtime] using done
  let start:=Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root updated sourceFrame count R.id R.node.tag) O.post.machine
  have entered' : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
        argument 0),.Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=.ok () start := by
    simpa only [start,R,O.id,O.tag,CurrentCallEmptyProtocolControl.frame,root,next,inputValue,DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue] using entered
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [empty];decide
  exact ⟨start,final,entered',trace,terminal,empty,SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩




/-- A live concrete empty source and latent CURRENT Bool execute their actual
source-only q constructor followed by one Bool conversion and the shared body. -/
theorem concrete {options limits remaining span before place}
    (sourceId : AllocId) (parentTag : BorTag) (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address))) 0 place)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry))
    (parent : DuplicatePrefixEmptyReferenceInput.Parent entry.allocation.extra (some parentTag))
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address))) 0 count place := by
  have empty : EmptySource before input.tracker
      (DuplicatePrefixSliceArgument.placePointer (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address)))) := by
    rcases input.source with empty|positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  change address≠0 ∧(∃base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩) ∧_ at empty
  obtain ⟨nonnull,⟨base,cached⟩,_⟩:=empty
  obtain ⟨index,node,tagged,nodeAt⟩:=parent
  let offset:=address-base
  have addressEq : base+offset=address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address base
  have member : (sourceId,entry)∈before.memory.live.toList:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.tracker.global:=
    ⟨input.runtime.formed _ member,input.runtime.coherent _ member,input.runtime.possible _ member,input.resources.tagsBelow _ member⟩
  have room : entry.allocation.extra.nodes.size+1≤4294967295 := by
    have old:=input.resources.nodeRoom (sourceId,entry) member
    change entry.allocation.extra.nodes.size+16<65536 at old
    omega
  have fresh : input.tracker.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have old:=input.resources.tagRoom
    change input.tracker.global.nextPointerTag.value.toNat<18446744073709551615
    omega
  let prepared:=CurrentCallPush.preparedMachine before #[]
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  have workPositive : 0<DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
  let R : CurrentCallEmptyLiveSourceCopy.Ready options remaining span prepared input.tracker #[] root sourceId entry base offset := {
    model:=CurrentCallResourcePreparedEntry.model input.model #[],origins:=input.cacheOrigins,enabled:=input.runtime.enabled,
    rootBorrow:=RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot before).2 input.tracker input.runtime.enabled,
    present:=live,cached:=cached,nonzero:=by rw [addressEq];exact nonnull,runtime:=runtime,room:=room,fresh:=fresh,
    dynamicFuel:=options.place.dynamicFuel-1,validationFuel:=options.limits.validation-1,
    dynamicEq:=by have fuel:=input.resources.dynamicFuel;omega,
    validationEq:=by have fuel:=input.resources.configuredFuel.2.2.2;omega}
  obtain ⟨P⟩:=CurrentCallEmptyLiveSourceCopy.concrete limits R parentTag index node tagged nodeAt
  have query : CurrentCallConversionPlan.sourceQuery before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address))) 0=.ok (some sourceId) :=
    CurrentCallConversionPlanAdequacy.query_concrete before _ 0 sourceId parentTag base rfl cached
  apply finish_source input latent sourceId entry live base offset count (by rw [addressEq];exact nonnull) cached query R.fresh P.machine P.tree
    P.memory P.user P.threads P.race P.tracked P.runtime P.leaf P.growth
  simpa only [DuplicatePrefixSliceArgument.rawValue,CurrentCallEmptyLiveSourceCopy.value,addressEq,root,prepared,Array.size_empty] using P.copy

/-- The wildcard LIVE hit creates its genuine parentless zero q node. It uses
the same CURRENT Bool phase and continuation, without source byte ownership. -/
theorem wildcard {options limits remaining span before place}
    (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (hit : CurrentCallEmptyClassification.Hit before input.tracker address)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==hit.id)=some (hit.id,entry))
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  have empty : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.pointer (Pointer.new .wildcard (Size.ofBytes address)))) := by
    rcases input.source with empty|positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  change address≠0 ∧before.user.addresses.provenanceMode≠.strict ∧GlobalAddressRecurringFormation.State before.memory before.user.addresses ∧_ at empty
  obtain ⟨nonnull,nonstrict,coherent,_⟩:=empty
  have sizeEq : hit.info.size=entry.allocation.byteSize := by
    have known:=hit.known
    simp only [MemoryState.getAllocInfo,live] at known
    exact (congrArg AllocationInfo.size (Except.ok.inj known)).symm
  let offset:=address-hit.base
  have addressEq : hit.base+offset=address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address hit.base
  have member : (hit.id,entry)∈before.memory.live.toList:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.tracker.global:=
    ⟨input.runtime.formed _ member,input.runtime.coherent _ member,input.runtime.possible _ member,input.resources.tagsBelow _ member⟩
  have room : entry.allocation.extra.nodes.size+1≤4294967295 := by
    have old:=input.resources.nodeRoom (hit.id,entry) member
    change entry.allocation.extra.nodes.size+16<65536 at old
    omega
  have fresh : input.tracker.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have old:=input.resources.tagRoom
    change input.tracker.global.nextPointerTag.value.toNat<18446744073709551615
    omega
  let prepared:=CurrentCallPush.preparedMachine before #[]
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  have workPositive : 0<DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
  let R : CurrentCallEmptyLiveSourceCopy.Ready options remaining span prepared input.tracker #[] root hit.id entry hit.base offset := {
    model:=CurrentCallResourcePreparedEntry.model input.model #[],origins:=input.cacheOrigins,enabled:=input.runtime.enabled,
    rootBorrow:=RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot before).2 input.tracker input.runtime.enabled,
    present:=live,cached:=hit.cached,nonzero:=by rw [addressEq];exact nonnull,runtime:=runtime,room:=room,fresh:=fresh,
    dynamicFuel:=options.place.dynamicFuel-1,validationFuel:=options.limits.validation-1,
    dynamicEq:=by have fuel:=input.resources.dynamicFuel;omega,
    validationEq:=by have fuel:=input.resources.configuredFuel.2.2.2;omega}
  obtain ⟨P⟩:=CurrentCallEmptyLiveSourceCopy.wildcard limits R nonstrict
    (by rw [addressEq,←sizeEq];exact hit.geometry) hit.exposed
  have query : CurrentCallConversionPlan.sourceQuery before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0=.ok (some hit.id) :=
    CurrentCallConversionPlanAdequacy.query_wildcard before _ 0 hit.id hit.base hit.info rfl (by decide)
      hit.geometry nonstrict hit.exposed hit.cached hit.known (coherent.live.2 hit.id (Array.contains_iff_mem.mp hit.exposed))
  apply finish_source input latent hit.id entry live hit.base offset count (by rw [addressEq];exact nonnull) hit.cached query R.fresh P.machine P.tree
    P.memory P.user P.threads P.race P.tracked P.runtime P.leaf P.growth
  simpa only [DuplicatePrefixSliceArgument.rawValue,CurrentCallEmptyLiveSourceCopy.value,addressEq,root,prepared,Array.size_empty] using P.copy

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyLiveCurrent

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyLiveCurrent.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary empty LIVE/current dependency {name}: {dependency}"
