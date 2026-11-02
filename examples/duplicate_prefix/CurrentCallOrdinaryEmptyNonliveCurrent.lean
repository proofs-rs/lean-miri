import duplicate_prefix.CurrentCallConversionBoolPhase
import duplicate_prefix.CurrentCallEmptyNonliveCopy
import duplicate_prefix.CurrentCallEmptyNonliveContinuation
import duplicate_prefix.CurrentCallEmptyReturnCore
import duplicate_prefix.CurrentCallResourcePreparedEntry
import duplicate_prefix.CurrentCallOrdinaryConversionSelected
import duplicate_prefix.CurrentCallConversionBoolModel
import duplicate_prefix.CurrentCallEmptyNonliveEncoding
import duplicate_prefix.S03NonliveMetadataTag
import duplicate_prefix.PushThread
import duplicate_prefix.CurrentCallBoolRetagBudget
import duplicate_prefix.CurrentCallEmptyClassification

namespace DuplicatePrefix.CurrentCallOrdinaryEmptyNonliveCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver GeneralBorrowFnEntryRegistration CurrentCallOrdinaryInput
open CandidateStableCallOwnership CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem payload_none {before : Before} {id : AllocId} {tag : Option BorTag}
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id tag)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none) :
    CurrentCallConversionPlan.payload before id=none := by
  cases metadata with
  | live entry present parent=>rw [absent] at present;cases present
  | functionRow missing present=>simp [CurrentCallConversionPlan.payload,missing,present]
  | vaListRow missing noFunction present=>simp [CurrentCallConversionPlan.payload,missing,noFunction,present]
  | nondataGlobal descriptor missing noFunction noVaList present kind=>
    rcases kind with kind|kind|kind
    all_goals simp [CurrentCallConversionPlan.payload,missing,noFunction,noVaList,present,kind]
  | dead entry missing noFunction noVaList noGlobal present=>
    simp [CurrentCallConversionPlan.payload,missing,noFunction,noVaList,noGlobal]

private theorem cached_below {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (id : AllocId) (root : BorTag) (cached : input.tracker.global.rootTag? id=some root) :
    root.value.toNat<input.tracker.global.nextPointerTag.value.toNat := by
  cases found : input.tracker.global.rootPointerTags.find? (fun row=>row.1==id) with
  | none=>simp only [GlobalState.rootTag?,found,Option.map_none] at cached;cases cached
  | some row=>
    have same : row.2=root:=Option.some.inj (by simpa only [GlobalState.rootTag?,found,Option.map_some] using cached)
    have below:=input.resources.cachedRootsBelow row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
    rw [same] at below
    exact below

private theorem registered_protectors (global : GlobalState) (frame : FrameState) (id : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615)
    (below : ∀row∈global.protectedTags.entries,row.1.value.toNat<global.nextPointerTag.value.toNat) :
    ∀row∈(registered global frame id room).1.protectedTags.entries,
      row.1.value.toNat<(registered global frame id room).1.nextPointerTag.value.toNat := by
  intro row member
  change row∈(global.protectedTags.entries.filter (fun item=>item.1!=global.nextPointerTag)).push
    (global.nextPointerTag,.StrongProtector) at member
  change row.1.value.toNat<(TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
  rw [GenericFunctionEntryNumerics.successor_value]
  rcases Array.mem_push.mp member with old|same
  · exact Nat.lt_trans (below row (Array.mem_filter.mp old).1) (Nat.lt_succ_self _)
  · subst row;exact Nat.lt_succ_self _

private theorem phase {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (sourceId : AllocId) (sourceTag : Option BorTag)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory sourceId sourceTag)
    (absent : before.memory.live.find? (fun row=>row.1==sourceId)=none)
    (query : CurrentCallConversionPlan.sourceQuery before argument 0=.ok (some sourceId))
    (fresh : input.tracker.global.nextPointerTag.value<18446744073709551615)
    (sourceMachine : Before) (frame : CompilerFrameContext.ActualFrame)
    (tracked : sourceMachine.borrowTracker=some
      ⟨(registered input.tracker.global {} sourceId fresh).1,input.tracker.retagMode⟩)
    (memory : sourceMachine.memory=before.memory)
    (user : sourceMachine.user=(CurrentCallPush.preparedMachine before #[]).user)
    (threads : sourceMachine.threads=(CurrentCallPush.preparedMachine before #[]).threads)
    (race : sourceMachine.dataRace=none)
    (frameBorrow : frame.extra.borrowTracker=some (({} : FrameState).addProtector sourceId input.tracker.global.nextPointerTag)) :
    ∃D : CurrentCallConversionBoolPhase.CurrentData sourceMachine
        ⟨(registered input.tracker.global {} sourceId fresh).1,input.tracker.retagMode⟩ #[] frame
        (({} : FrameState).addProtector sourceId input.tracker.global.nextPointerTag) place,
      D.family=input.returnFamily ∧D.offset=input.returnOffset ∧∃P : CurrentCallConversionBoolPhase.FirstPhase input D,P.reserve=14 := by
  let sourceTracker : MachineHooks.BorrowState:=⟨(registered input.tracker.global {} sourceId fresh).1,input.tracker.retagMode⟩
  have counter : sourceTracker.global.nextPointerTag.value.toNat=input.tracker.global.nextPointerTag.value.toNat+1 :=
    GenericFunctionEntryNumerics.successor_value _ fresh
  have freshB : sourceTracker.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have room:=input.resources.tagRoom
    change sourceTracker.global.nextPointerTag.value.toNat<18446744073709551615
    rw [counter];omega
  obtain ⟨D,family,offset,current⟩:=CurrentCallConversionBoolPhase.from_initial (frames:=#[]) input latent tracked frameBorrow freshB
    (by rw [memory];exact latent.1) (by rw [memory]) (by rw [memory]) (by rw [memory]) (by rw [user];rfl)
    (by rfl) (by intro root cached;have old:=cached_below input _ root cached;rw [counter];omega)
    (registered_protectors input.tracker.global {} sourceId fresh input.protectorsBelow)
    (by change InitialRegistryVacant sourceMachine input.returnFamily.allocation;unfold InitialRegistryVacant;rw [user];exact latent.2.2.2.1)
    race (by rw [user];exact input.model.ghostOff) (by rw [user];exact input.model.noBackend)
  have retQuery : CurrentCallConversionPlan.returnQuery before place=.ok (some input.returnFamily.allocation) := by
    have q:=CurrentCallConversionPlanAdequacy.query_of_selected before input.tracker input.returnFamily input.returnOffset
      input.returnCapacity 1 false input.returnRepresentation (.inr latent) (by decide)
    simpa only [CurrentCallConversionPlan.returnQuery,input.returnEncoding,Pointer.withOptionalProvenance] using q
  have sourcePayload:=payload_none metadata absent
  have boolPayload : CurrentCallConversionPlan.payload before input.returnFamily.allocation=some D.source :=
    CurrentCallConversionPlanAdequacy.payload_of_current before _ D.source latent.1 latent.2.1 latent.2.2.1 current
  have head : CurrentCallConversionPlan.selectedPayloads before argument 0 place=D.source::[] := by
    unfold CurrentCallConversionPlan.selectedPayloads CurrentCallConversionPlan.selectedRows
    rw [query,retQuery]
    change (CurrentCallConversionPlan.rowsFromIds before (some sourceId) (some input.returnFamily.allocation)).map Prod.snd=[D.source]
    simp [CurrentCallConversionPlan.rowsFromIds,sourcePayload,boolPayload]
  have phaseMemory : D.registered.machine.memory=before.memory := memory
  have phaseAddresses : D.registered.machine.user.addresses=before.user.addresses := by change sourceMachine.user.addresses=before.user.addresses;rw [user];rfl
  let P : CurrentCallConversionBoolPhase.FirstPhase input D := {
    infoEq:=by intro id;rw [phaseMemory]
    addresses:=phaseAddresses
    tape:=by change sourceMachine.user.payload.payload.user.choices=before.user.payload.payload.user.choices;rw [user];rfl
    thread:=by change sourceMachine.threads.activeThread=before.threads.activeThread;rw [threads];rfl
    roots:=by intro id;rfl
    spent:=2,reserve:=14,room:=by decide,positive:=by decide
    counter:=by
      have next:=GenericFunctionEntryNumerics.successor_value sourceTracker.global.nextPointerTag freshB
      change (TypedRetagEmpty.successorTag sourceTracker.global.nextPointerTag D.fresh).value.toNat≤_
      rw [GenericFunctionEntryNumerics.successor_value,counter];omega
    metadata:=by
      intro id member
      have old:=CurrentCallOrdinaryConversionSelected.targets_metadata input id member
      unfold RelocationTargetMetadata at old ⊢
      rw [phaseMemory,phaseAddresses]
      exact old
    rest:=[],head:=head}
  exact ⟨D,family,offset,P,rfl⟩

private theorem repack {post : RootState} {frames : Array CompilerFrameContext.ActualFrame}
    {frame : CompilerFrameContext.ActualFrame} {machine : Before}
    (stackEq : post.stack=(Storage.withCurrent frames frame machine).stack) :
    post=Storage.withCurrent frames frame post.machine := by
  cases post with
  | mk stackMachine machine=>change stackMachine=_ at stackEq;cases stackEq;rfl

private theorem model_move {options remaining span before after tracker}
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (user : after.user=before.user) (threads : after.threads=before.threads)
    (race : after.dataRace=before.dataRace) (tracked : after.borrowTracker=some tracker)
    (mode : tracker.retagMode=.Default) : DuplicatePrefixCallModel.Model options remaining span after := by
  refine ⟨model.debugOff,model.preciseOff,model.implicitOff,?_,?_,⟨tracker,tracked,mode⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
  · rw [user];exact model.ghostOff
  · rw [user];exact model.shallow
  · rw [race];exact model.noDataRace
  · rw [user];exact model.noBackend
  · rw [user];exact model.metadata
  · rw [threads];exact model.fixedScheduler
  · rw [user];exact model.unchecked
  · rw [user];exact model.noGc

private theorem two_nodes_absent {machine tracker place}
    (R : CurrentCallPostEntryCheckpoint.Return machine tracker place) (tag : BorTag)
    (short : R.window.allocation.extra.nodes.size≤2)
    (rootBelow : ∀node,R.window.allocation.extra.nodes.get allocationRoot=some node→node.tag.value.toNat<tag.value.toNat)
    (beforeChild : tag.value.toNat<R.node.tag.value.toNat) :
    ∀index node,R.window.allocation.extra.nodes.get index=some node→node.tag≠tag := by
  have grantBound:=GeneralBorrowNodeUpdate.lookup_valid _ _ _ R.nodeAt
  have grantNe : R.window.pointer.grant≠allocationRoot := by
    intro same
    have edge:=R.edge
    rw [same,R.window.parents.primaryNone] at edge
    cases edge
  have grantNat : R.window.pointer.grant.toNat=1 := by
    have ne : R.window.pointer.grant.toNat≠0 := by intro equal;exact grantNe (GeneralBorrowNodeUpdate.index_injective _ _ equal)
    change R.window.pointer.grant.toNat<R.window.allocation.extra.nodes.data.size at grantBound
    change R.window.allocation.extra.nodes.data.size≤2 at short
    omega
  intro index node found same
  have bound:=GeneralBorrowNodeUpdate.lookup_valid _ _ _ found
  change index.toNat<R.window.allocation.extra.nodes.data.size at bound
  change R.window.allocation.extra.nodes.data.size≤2 at short
  by_cases zero : index.toNat=0
  · have atRoot : index=allocationRoot:=GeneralBorrowNodeUpdate.index_injective _ _ zero
    subst index
    have old:=rootBelow node found
    rw [same] at old
    exact Nat.lt_irrefl _ old
  · have equal : index=R.window.pointer.grant:=GeneralBorrowNodeUpdate.index_injective _ _ (by omega)
    subst index
    have nodeEq : node=R.node:=Option.some.inj (found.symm.trans R.nodeAt)
    rw [nodeEq] at same
    rw [same] at beforeChild
    exact Nat.lt_irrefl _ beforeChild


private theorem invoke {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (sourceId : AllocId) (parentTag : BorTag) (base sourceOffset count : UInt64)
    (nonnull : base+sourceOffset≠0)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory sourceId (some parentTag))
    (absent : before.memory.live.find? (fun row=>row.1==sourceId)=none)
    (query : CurrentCallConversionPlan.sourceQuery before argument 0=.ok (some sourceId)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (base+sourceOffset)))) 0 count place := by
  let prepared:=CurrentCallPush.preparedMachine before #[]
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  have preparedModel:=CurrentCallResourcePreparedEntry.model input.model #[]
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have frameBorrow : root.frame.extra.borrowTracker=some ({} : FrameState):=
    RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot before).2 input.tracker input.runtime.enabled
  have fresh : input.tracker.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have room:=input.resources.tagRoom
    change input.tracker.global.nextPointerTag.value.toNat<18446744073709551615
    omega
  have workPositive : 0<DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
  let dynamicFuel:=options.place.dynamicFuel-1
  let validationFuel:=options.limits.validation-1
  let budget:=limits.callDispatch-1
  have dynamicEq : options.place.dynamicFuel=dynamicFuel+1 := by have room:=input.resources.dynamicFuel;dsimp only [dynamicFuel];omega
  have validationEq : options.limits.validation=validationFuel+1 := by have room:=input.resources.configuredFuel.2.2.2;dsimp only [validationFuel];omega
  have dispatchEq : limits.callDispatch=budget+1 := by have room:=input.resources.executionFuel.1;dsimp only [budget];omega
  obtain ⟨copyCtx⟩:=(DuplicatePrefixCallModel.contexts options remaining span before input.model).1
  obtain ⟨sourceFn,copy,sourceMemory,sourceUser,sourceThreads,sourceRace,sourceTracked⟩:=
    CurrentCallEmptyNonliveCopy.copy options limits remaining span copyCtx prepared input.tracker preparedModel input.cacheOrigins #[] root {} frameBorrow
      sourceId parentTag base sourceOffset nonnull cached metadata absent fresh dynamicFuel validationFuel dynamicEq validationEq
  let next : MachineHooks.BorrowState:=⟨(registered input.tracker.global {} sourceId fresh).1,.FnEntry⟩
  let source : Before:={sourceFn with borrowTracker:=some {next with retagMode:=input.tracker.retagMode}}
  let sourceFrame:=({} : FrameState).addProtector sourceId input.tracker.global.nextPointerTag
  let inputValue:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
  let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId input.tracker.global.nextPointerTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
  let boolFrame:=(atSpan (RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot root updated sourceFrame) count) ⟨601⟩).frame
  have sourceModel : DuplicatePrefixCallModel.Model options remaining span source:=
    model_move preparedModel sourceUser sourceThreads sourceRace rfl input.defaultMode
  have args:=CurrentCallEmptyProtocolControl.arguments options limits remaining span input.model.debugOff validationFuel validationEq #[] root raw
    prepared sourceFn input.tracker next input.runtime.enabled sourceTracked input.model.ghostOff input.model.shallow
    (by rw [sourceUser];exact preparedModel.ghostOff) (by rw [sourceUser];exact preparedModel.shallow)
    inputValue updated sourceFrame count copy
  obtain ⟨D,dFamily,dOffset,P,reserveEq⟩:=phase input latent sourceId (some parentTag) metadata absent query fresh source boolFrame rfl sourceMemory sourceUser sourceThreads
    (sourceRace.trans input.model.noDataRace) (by rfl)
  obtain ⟨retagCtx⟩:=ActualRetagContext.exists_context options (remaining+1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨externStatic,wiring,finalAddresses,finalTape,result,⟨O⟩⟩:=CurrentCallConversionBoolPhase.first input retagCtx D P
  have postEq:=repack O.stack
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
  have different : D.family.allocation≠sourceId := by
    rw [dFamily]
    obtain ⟨retAbsent,retNoFn,retNoVa,_,_,retSource,retCurrent,_,_,_⟩:=latent
    have payload:=CurrentCallConversionPlanAdequacy.payload_of_current before _ retSource retAbsent retNoFn retNoVa retCurrent
    intro same
    rw [same,payload_none metadata absent] at payload
    cases payload
  have currentAbsent : O.post.machine.memory.live.find? (fun row=>row.1==sourceId)=none := by
    rw [CurrentCallConversionBoolModel.memory_other O sourceId (Ne.symm different),sourceMemory]
    exact absent
  have currentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata O.post.machine.memory sourceId (some parentTag) := by
    rw [currentMemory]
    exact S03NonliveEmptyMetadata.replace source.memory sourceId D.family.allocation (some parentTag) _
      (by rw [sourceMemory];exact metadata) (by rw [sourceMemory];exact absent) different
  have sourceCounter : next.global.nextPointerTag.value.toNat=input.tracker.global.nextPointerTag.value.toNat+1 :=
    GenericFunctionEntryNumerics.successor_value _ fresh
  have rootHit : result.global.rootTag? D.family.allocation=some D.root := result.roots _ _ D.rootCached
  have initialRoot : input.tracker.global.rootTag? D.family.allocation=some D.root := D.rootCached
  have rootBeforeSource:=cached_below input D.family.allocation D.root initialRoot
  have sourceHidden : ∀index node,R.window.allocation.extra.nodes.get index=some node→
      node.tag=input.tracker.global.nextPointerTag→node.isExposed=false := by
    have absentTag:=two_nodes_absent R input.tracker.global.nextPointerTag O.nodes (by
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
    .nonlive sourceId input.tracker.global.nextPointerTag (some parentTag) currentMetadata currentAbsent sourceHidden
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
    · have done:=CurrentCallEmptyContinuation.nonlive core limits root raw sourceFrame borrowCore rfl rfl rfl sourceId input.tracker.global.nextPointerTag
        (some parentTag) base sourceOffset count nonnull zero currentMetadata currentAbsent currentBase sourceBelow bodyRoom R.runtime.below.protectors bodyFresh
        currentOrigins dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq (by
          have room:=bodyRoom
          change result.global.nextPointerTag.value.toNat+4<2^64 at room
          change result.global.nextPointerTag.value.toNat+1<18446744073709551615
          omega) rfl
      simpa only [updated,actual_access_runtime,show core.node.tag=R.node.tag from rfl] using done
  let start:=Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root updated sourceFrame count R.id R.node.tag) O.post.machine
  have entered' : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
        (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (base+sourceOffset)))) 0),.Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=.ok () start := by
    simpa only [start,R,O.id,O.tag,CurrentCallEmptyProtocolControl.frame,root,next,inputValue,DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue] using entered
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [empty];decide
  exact ⟨start,final,entered',trace,terminal,empty,SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩


/-- Metadata-backed absent concrete source and CURRENT latent Bool. Every
actual entry/body/return operation is derived internally for every count. -/
theorem concrete {options limits remaining span before place}
    (sourceId : AllocId) (parentTag : BorTag) (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address))) 0 place)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory sourceId (some parentTag))
    (absent : before.memory.live.find? (fun row=>row.1==sourceId)=none)
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
  let offset:=address-base
  have addressEq : base+offset=address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address base
  have query : CurrentCallConversionPlan.sourceQuery before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address))) 0=.ok (some sourceId) :=
    CurrentCallConversionPlanAdequacy.query_concrete before _ 0 sourceId parentTag base rfl cached
  have result:=invoke input latent sourceId parentTag base offset count (by rw [addressEq];exact nonnull) cached metadata absent query
  simpa only [addressEq] using result

/-- Exposed wildcard HIT on a metadata-backed absent source uses the SAME
initialization computation as its concrete normalization. The CURRENT Bool is
ensured once and then follows the common all-count continuation. -/
theorem wildcard {options limits remaining span before place}
    (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (hit : CurrentCallEmptyClassification.Hit before input.tracker address)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory hit.id none)
    (absent : before.memory.live.find? (fun row=>row.1==hit.id)=none)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  have empty : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.pointer (Pointer.new .wildcard (Size.ofBytes address)))) := by
    rcases input.source with empty|positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  change address≠0 ∧before.user.addresses.provenanceMode≠.strict ∧GlobalAddressRecurringFormation.State before.memory before.user.addresses ∧_ at empty
  obtain ⟨nonnull,nonstrict,coherent,_⟩:=empty
  let offset:=address-hit.base
  have addressEq : hit.base+offset=address := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address hit.base
  let parentTag:=input.tracker.global.nextPointerTag
  have concreteMetadata:=S03NonliveMetadataTag.changeTag before.memory hit.id none (some parentTag) metadata absent
  have allocLive : before.memory.isAllocLive hit.id=true:=coherent.live.2 hit.id (Array.contains_iff_mem.mp hit.exposed)
  have query : CurrentCallConversionPlan.sourceQuery before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0=.ok (some hit.id) :=
    CurrentCallConversionPlanAdequacy.query_wildcard before _ 0 hit.id hit.base hit.info rfl (by decide)
      hit.geometry nonstrict hit.exposed hit.cached hit.known allocLive
  have result:=invoke input latent hit.id parentTag hit.base offset count (by rw [addressEq];exact nonnull) hit.cached concreteMetadata absent query
  obtain ⟨info,known,notLive⟩:=S03NonliveEmptyMetadata.known before.memory hit.id none metadata absent
  have infoEq : info=hit.info:=Except.ok.inj (known.symm.trans hit.known)
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span before input.model).1
  have positive : 0<DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
  have dynamicEq : options.place.dynamicFuel=(options.place.dynamicFuel-1)+1 := by have fuel:=input.resources.dynamicFuel;omega
  have validationEq : options.limits.validation=(options.limits.validation-1)+1 := by have fuel:=input.resources.configuredFuel.2.2.2;omega
  have fresh : input.tracker.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have room:=input.resources.tagRoom
    change input.tracker.global.nextPointerTag.value.toNat<18446744073709551615
    omega
  have equal:=CurrentCallEmptyNonliveEncoding.call_equal options limits remaining span ctx input.model.debugOff input.model.nullComparator
    (options.place.dynamicFuel-1) (options.limits.validation-1) dynamicEq validationEq hit.id parentTag input.tracker hit.base offset count
    (by rw [addressEq];exact nonnull) before input.model.ghostOff input.model.shallow hit.cached hit.info hit.known
    (by rw [←infoEq];exact notLive) (by rw [addressEq];exact hit.geometry) nonstrict hit.exposed allocLive input.runtime.enabled fresh
    input.model.noDataRace input.model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ input.model.metadata input.cacheOrigins) place input.stackReady
  obtain ⟨start,final,entered,trace,terminal,empty,noErrors,noUb,prefixes⟩:=result
  refine ⟨start,final,?_,trace,terminal,empty,noErrors,noUb,prefixes⟩
  simpa only [addressEq,DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue] using equal.trans entered

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyNonliveCurrent

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyNonliveCurrent.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary nonlive/current dependency {name}: {dependency}"
