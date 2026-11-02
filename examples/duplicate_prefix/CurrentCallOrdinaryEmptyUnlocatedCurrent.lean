import duplicate_prefix.CurrentCallConversionBoolMetadata
import duplicate_prefix.CurrentCallConversionProtocolOrdered
import duplicate_prefix.CurrentCallBoolRetagBudget
import duplicate_prefix.CurrentCallConversionBoolModel
import duplicate_prefix.CurrentCallConversionBoolPhase
import duplicate_prefix.CurrentCallEmptyUnlocatedCopy
import duplicate_prefix.CurrentCallEmptyProtocolControl
import duplicate_prefix.CurrentCallEmptyReturnCore
import duplicate_prefix.CurrentCallEmptyIntegerBodyControl
import duplicate_prefix.CurrentCallEmptyMissBodyControl
import duplicate_prefix.CurrentCallEmptyIntegerCounterFrame
import duplicate_prefix.CurrentCallConversionMissFrame
import duplicate_prefix.PushThread

namespace DuplicatePrefix.CurrentCallOrdinaryEmptyUnlocatedCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CandidateStableCallOwnership CurrentCallResourceNormalization
open CurrentCallOrdinaryInput CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver GeneralBorrowFnEntryRegistration
open CurrentCallConversionBoolPhase
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

open Lean Elab Tactic in
elab "unlocated_current_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with | [(name,_)]=>return mkConst name | _=>throwError "expected checked unlocated rule {suffix.getString}"

/-- Retain the SAME initial protocol endpoint used by the actual last converter. -/
private theorem first_with_protocol {options limits inputRemaining remaining span before argument place machine tracker frames frame borrowFrame}
    (input : OrdinaryInput options limits inputRemaining span before argument 0 place)
    (ctx : ActualRetagContext.Context options remaining span)
    (D : CurrentData machine tracker frames frame borrowFrame place)
    (phase : FirstPhase input D) (last : phase.rest=[]) :
    ∃externStatic,
      (CurrentCallConversionActualEnsure.hooks options).rootPointer=
        PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic ∧
    ∃finalAddresses finalTape,
    ∃result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic D.registered.machine D.next []
      (addressCharge before) phase.reserve finalAddresses finalTape,
      CurrentCallConversionChoiceProtocol.AddressProtocol D.registered.machine.memory
        (UInt32.ofNat D.registered.machine.threads.activeThread.toNat) D.registered.machine.user.addresses
        (EvalPointerSource.tape.get D.registered.machine)
        (CurrentCallConversionPlan.selectedIds before argument 0 place) finalAddresses finalTape ∧
      Nonempty (Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic []
        (addressCharge before) phase.reserve finalAddresses finalTape result) := by
  have head : CurrentCallConversionPlan.selectedPayloads before argument 0 place=[D.source] := by simpa only [last] using phase.head
  have ids : CurrentCallConversionPlan.selectedIds before argument 0 place=CurrentCallConversionFiniteFold.targets D.source := by
    simp only [CurrentCallConversionPlan.selectedIds,head,List.flatMap_singleton,CurrentCallConversionFiniteFold.targets_eq]
  obtain ⟨externStatic,wiring⟩ := (unlocated_current_rule ".CurrentCallOrdinaryConversionEnsure.root_wiring") options
  obtain ⟨finalAddresses,finalTape,protocol,resources,budget,_⟩:=CurrentCallOrdinaryConversionInitial.phase input D.registered.machine D.next
    phase.infoEq phase.addresses phase.tape phase.thread phase.roots phase.spent phase.reserve phase.room phase.counter phase.metadata
  have selected : D.source∈CurrentCallConversionPlan.selectedPayloads before argument 0 place := by rw [head];simp
  obtain ⟨id,data,_⟩:=CurrentCallOrdinaryConversionSelected.payload_data input D.source selected
  have resources':=resources
  have protocol':=protocol
  have budget':=budget
  rw [ids] at resources' protocol' budget'
  obtain ⟨result⟩:=CurrentCallConversionFiniteFold.invoke D.source PreparedReflection.actual.compiler.runtime.target.base
    (CurrentCallConversionActualEnsure.hooks options).address rfl externStatic D.registered.machine D.next
    (by rfl) [] (addressCharge before) phase.reserve phase.positive finalAddresses finalTape
    (by simpa only [List.append_nil] using protocol') (by simpa only [List.append_nil] using resources')
    (by simpa only [List.append_nil] using budget')
    (fun id member=>phase.metadata id (by rw [ids];exact member)) (by
      intro id member missing info actual
      have selected : id∈CurrentCallConversionPlan.selectedIds before argument 0 place := by rw [ids];exact member
      have oldMissing : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none := by rw [←phase.addresses];exact missing
      have oldActual : before.memory.getAllocInfo id=.ok info := (phase.infoEq id).symm.trans actual
      exact CurrentCallConversionFiniteFold.formation_initial before id
        (CurrentCallOrdinaryConversionSelected.targets_metadata input id selected) oldMissing info oldActual)
    D.race data.2.1 data.2.2.1 rfl
  exact ⟨externStatic,wiring,finalAddresses,finalTape,result,protocol,of_result ctx D externStatic wiring _ _ _ _ _ result⟩

private theorem fresh {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place) :
    input.tracker.global.nextPointerTag.value<18446744073709551615 := by
  have bound:=input.resources.tagRoom
  exact UInt64.lt_iff_toNat_lt.mpr (by change input.tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)

private theorem successor (tag : BorTag) (room : tag.value<18446744073709551615) :
    (TypedRetagEmpty.successorTag tag room).value.toNat=tag.value.toNat+1 := by
  have bound : tag.value.toNat<18446744073709551615 := UInt64.lt_iff_toNat_lt.mp room
  change (tag.value+1).toNat=_
  rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega)]

private theorem cached_below {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (root : BorTag) (cached : input.tracker.global.rootTag? id=some root) :
    root.value.toNat<input.tracker.global.nextPointerTag.value.toNat := by
  cases found : input.tracker.global.rootPointerTags.find? (fun row=>row.1==id) with
  | none=>simp only [GlobalState.rootTag?,found,Option.map_none] at cached;cases cached
  | some row=>
    have same : row.2=root:=Option.some.inj (by simpa only [GlobalState.rootTag?,found,Option.map_some] using cached)
    have bound:=input.resources.cachedRootsBelow row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
    rw [same] at bound
    exact bound

def sourceTracker {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place) : MachineHooks.BorrowState :=
  {input.tracker with global:=advanced input.tracker.global (fresh input)}
def sourceMachine {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place) : Before :=
  {CurrentCallPush.preparedMachine before #[] with borrowTracker:=some (sourceTracker input)}

private theorem current_data {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (count : UInt64) (value : Immediate Provenance) :
    ∃D : CurrentData (sourceMachine input) (sourceTracker input) #[]
      (atSpan (RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot
        (CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace) value {}) count) ⟨601⟩).frame {} place, D.family=input.returnFamily ∧D.offset=input.returnOffset := by
  obtain ⟨absent,noFunction,noVaList,registry,⟨root,concrete,rootCached⟩,source,current,size,format,physical⟩:=latent
  obtain ⟨base,cached,baseRoom,address,nonnull,represented⟩:=input.returnRepresentation
  have offsetBound : input.returnOffset.toNat<input.returnCapacity.toNat := by
    have bound:=physical.2.2.1
    rw [size] at bound
    change input.returnOffset.toNat+1≤input.returnCapacity.toNat at bound
    omega
  have add : (base+input.returnOffset).toNat=base.toNat+input.returnOffset.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have valueEq : input.returnFamily.value=Pointer.new (.concrete input.returnFamily.allocation root) (Size.ofBytes (base+input.returnOffset)) := by
    cases pointer : input.returnFamily.value with
    | mk offset provenance=>
      have prov : provenance=.concrete input.returnFamily.allocation root := by simpa only [pointer] using concrete
      have addr : offset.bytes=base+input.returnOffset := UInt64.toNat_inj.mp (by simpa only [pointer,add] using address)
      cases offset
      cases prov
      cases addr
      rfl
  have nonzero : base+input.returnOffset≠0 := by
    rw [valueEq] at nonnull
    exact nonnull
  have currentFresh : (sourceTracker input).global.nextPointerTag.value<18446744073709551615 := by
    have margin:=input.resources.tagRoom
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag (fresh input)).value.toNat<18446744073709551615
    rw [successor]
    omega
  refine ⟨{
    enabled:=rfl,frameBorrow:=rfl,fresh:=currentFresh,family:=input.returnFamily,root:=root,source:=source,base:=base,
    offset:=input.returnOffset,value:=valueEq,physicalPointer:=input.returnEncoding,layout:=input.returnLayout,aligned:=input.returnAligned,
    physical:=physical,current:=?_,absent:=absent,noFunction:=noFunction,noVaList:=noVaList,cached:=cached,rootCached:=rootCached,
    addressRoom:=?_,nonnull:=nonzero,rootBelow:=?_,protectors:=?_,registry:=registry,race:=input.model.noDataRace,
    ghost:=input.model.ghostOff,backend:=input.model.noBackend},rfl,rfl⟩
  · cases current with
    | memory descriptor=>exact .memory descriptor
    | internalStatic definition descriptor initializer=>exact .internalStatic definition descriptor initializer
  · rw [physical.1.1,size]
    exact baseRoom
  · have old:=cached_below input input.returnFamily.allocation root rootCached
    change root.value.toNat<(TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag (fresh input)).value.toNat
    rw [successor]
    omega
  · intro row member
    have old:=input.protectorsBelow row member
    change row.1.value.toNat<(TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag (fresh input)).value.toNat
    rw [successor]
    omega

private theorem first_phase {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (query : CurrentCallConversionPlan.sourceQuery before argument 0=.ok none)
    (count : UInt64) (value : Immediate Provenance)
    (D : CurrentData (sourceMachine input) (sourceTracker input) #[]
      (atSpan (RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot
        (CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace) value {}) count) ⟨601⟩).frame {} place)
    (family : D.family=input.returnFamily) :
    ∃phase : FirstPhase input D,phase.rest=[] ∧phase.reserve=14 := by
  have current : CurrentPayload before D.family.allocation D.source := by
    cases D.current with
    | memory descriptor=>exact .memory descriptor
    | internalStatic definition descriptor initializer=>exact .internalStatic definition descriptor initializer
  have payload:=CurrentCallConversionPlanAdequacy.payload_of_current before D.family.allocation D.source
    D.absent D.noFunction D.noVaList current
  have returnQuery:=CurrentCallConversionPlanAdequacy.return_query options limits remaining span before argument 0 place input
  rw [←family] at returnQuery
  have head : CurrentCallConversionPlan.selectedPayloads before argument 0 place=[D.source] := by
    simp only [CurrentCallConversionPlan.selectedPayloads,CurrentCallConversionPlan.selectedRows,query,returnQuery,
      Except.toOption,Option.bind_some,id_eq,CurrentCallConversionPlan.rowsFromIds,Option.bind_none,Option.any_none,
      Bool.false_eq_true,ite_false,payload,Option.map_some,Option.toList_none,Option.toList_some,List.nil_append,List.map_singleton]
  refine ⟨{
    infoEq:=fun _=>rfl,addresses:=rfl,tape:=rfl,thread:=rfl,roots:=fun _=>rfl,
    spent:=2,reserve:=14,room:=by decide,positive:=by decide,counter:=?_,metadata:=?_,rest:=[],head:=head},rfl,rfl⟩
  · change (TypedRetagEmpty.successorTag (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag (fresh input)) D.fresh).value.toNat≤_
    rw [successor,successor]
    omega
  · intro id member
    exact CurrentCallOrdinaryConversionSelected.targets_metadata input id member

private theorem frame_with_borrow (frame : CompilerFrameContext.ActualFrame) (borrow : FrameState)
    (held : frame.extra.borrowTracker=some borrow) : TypedRetagEntry.frameWithBorrow frame borrow=frame := by
  cases frame
  simp only [TypedRetagEntry.frameWithBorrow] at *
  congr
  exact held.symm

private theorem source_model {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place) :
    DuplicatePrefixCallModel.Model options remaining span (sourceMachine input) := by
  have control : (config options (remaining+1) span).terminators.getControl (sourceMachine input).user=
      (config options (remaining+1) span).terminators.getControl before.user := by
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  refine ⟨input.model.debugOff,input.model.preciseOff,input.model.implicitOff,input.model.ghostOff,input.model.shallow,
    ⟨sourceTracker input,rfl,input.defaultMode⟩,input.model.noDataRace,input.model.noBackend,input.model.metadata,
    input.model.fixedScheduler,?_,?_,input.model.nullComparator,input.model.sourceMatches⟩
  · rw [control];exact input.model.unchecked
  · rw [control];exact input.model.noGc

private theorem state_of_stack (state : RootState) (frame : CompilerFrameContext.ActualFrame)
    (stack : state.stack=(Storage.withCurrent #[] frame state.machine).stack) :
    state=Storage.withCurrent #[] frame state.machine := by
  cases state
  cases stack
  rfl

private theorem integer_arguments {options limits remaining span before place}
    (address count : UInt64) (input : OrdinaryInput options limits remaining span before (.integer address) 0 place)
    (nonnull : address≠0) :
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let value:=(RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent #[] root.frame (CurrentCallPush.preparedMachine before #[]))=
      .ok (2,2) (Storage.withCurrent #[] (RootArgumentsTwo.result
        (CurrentCallEmptyProtocolControl.sourceRoot root value {}) count).frame (sourceMachine input)) := by
  dsimp only
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let machine:=CurrentCallPush.preparedMachine before #[]
  let frame:=(firstLive root).frame
  let value:=(RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm
  let entered:=ScopedFrame.entered machine input.tracker .FnEntry
  let current : MachineHooks.BorrowState:={input.tracker with retagMode:=.FnEntry}
  let next : MachineHooks.BorrowState:={sourceTracker input with retagMode:=.FnEntry}
  let post : Before:={sourceMachine input with borrowTracker:=some next}
  have dynamicPositive : 0<options.place.dynamicFuel := by
    have room:=input.resources.dynamicFuel;unfold DuplicatePrefixCallSpecification.work at room;omega
  have validationPositive : 0<options.limits.validation := by
    have room:=input.resources.configuredFuel.2.2.2;unfold DuplicatePrefixCallSpecification.work at room;omega
  have localLive : (frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [frame,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have localCached : (frame.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [frame,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,firstCache,RootFrameData.cache,
      LocalOperands.cachedLayoutFrame,atSpan,i1]
  have copied:=ReferenceArgumentCopy.copy_empty_argument options limits remaining span input.model.nullComparator input.model.preciseOff
    input.model.implicitOff input.model.debugOff (options.place.dynamicFuel-1) (options.limits.validation-1) (by omega) (by omega)
    #[] frame entered 1 .uninit ((firstLive root).valid i1) localLive localCached (firstLive root).noClocks input.model.ghostOff input.model.shallow
    address nonnull current rfl rfl (fresh input) input.model.metadata
    (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ input.model.metadata input.cacheOrigins)
    (LocalPlaces.localRuntimePlace 0 frame 1 ActualReferenceMetadata.reference).stackView rfl
  have frameBorrow : frame.extra.borrowTracker=some ({} : FrameState) := by
    change root.frame.extra.borrowTracker=some ({} : FrameState)
    exact RootEntryFrame.raw_borrow _ _ _ input.tracker input.runtime.enabled
  have sourceFrameEq : (CurrentCallEmptyProtocolControl.sourceRoot root value {}).frame=
      {frame with locals:=frame.locals.set 1 {value:=.live (.immediate value),layout:=(frame.locals[1]'((firstLive root).valid i1)).layout} ((firstLive root).valid i1)} := by
    change TypedRetagEntry.frameWithBorrow (write (firstLive root) i1 value).frame {}=_
    exact (frame_with_borrow (write (firstLive root) i1 value).frame {} (by exact frameBorrow)).trans (by rfl)
  have copy : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace 0 frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent #[] frame entered)=.ok ()
      (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.sourceRoot root value {}).frame post) := by
    rw [sourceFrameEq]
    exact copied
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have arguments:=CurrentCallEmptyProtocolControl.arguments options limits remaining span input.model.debugOff (options.limits.validation-1) (by omega)
    #[] root raw machine post input.tracker next input.runtime.enabled rfl input.model.ghostOff input.model.shallow
    input.model.ghostOff input.model.shallow value value {} count copy
  exact arguments

private theorem miss_arguments {options limits remaining span before place}
    (address count : UInt64) (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (nonnull : address≠0) (nonstrict : before.user.addresses.provenanceMode≠.strict)
    (query : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none) :
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent #[] root.frame (CurrentCallPush.preparedMachine before #[]))=
      .ok (2,2) (Storage.withCurrent #[] (RootArgumentsTwo.result
        (CurrentCallEmptyProtocolControl.sourceRoot root value {}) count).frame (sourceMachine input)) := by
  dsimp only
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let machine:=CurrentCallPush.preparedMachine before #[]
  let frame:=(firstLive root).frame
  let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm
  let entered:=ScopedFrame.entered machine input.tracker .FnEntry
  let current : MachineHooks.BorrowState:={input.tracker with retagMode:=.FnEntry}
  let next : MachineHooks.BorrowState:={sourceTracker input with retagMode:=.FnEntry}
  let post : Before:={sourceMachine input with borrowTracker:=some next}
  have dynamicPositive : 0<options.place.dynamicFuel := by
    have room:=input.resources.dynamicFuel;unfold DuplicatePrefixCallSpecification.work at room;omega
  have validationPositive : 0<options.limits.validation := by
    have room:=input.resources.configuredFuel.2.2.2;unfold DuplicatePrefixCallSpecification.work at room;omega
  have localLive : (frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [frame,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have localCached : (frame.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [frame,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,firstCache,RootFrameData.cache,
      LocalOperands.cachedLayoutFrame,atSpan,i1]
  have copied:=S03WildcardMissArgumentCopy.copy_empty_argument options limits remaining span input.model.nullComparator input.model.preciseOff
    input.model.implicitOff input.model.debugOff (options.place.dynamicFuel-1) (options.limits.validation-1) (by omega) (by omega)
    #[] frame entered 1 .uninit ((firstLive root).valid i1) localLive localCached (firstLive root).noClocks input.model.ghostOff input.model.shallow
    address nonnull current rfl rfl (fresh input) nonstrict query input.model.metadata
    (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ input.model.metadata input.cacheOrigins)
    (LocalPlaces.localRuntimePlace 0 frame 1 ActualReferenceMetadata.reference).stackView rfl
  have frameBorrow : frame.extra.borrowTracker=some ({} : FrameState) := by
    change root.frame.extra.borrowTracker=some ({} : FrameState)
    exact RootEntryFrame.raw_borrow _ _ _ input.tracker input.runtime.enabled
  have sourceFrameEq : (CurrentCallEmptyProtocolControl.sourceRoot root value {}).frame=
      {frame with locals:=frame.locals.set 1 {value:=.live (.immediate value),layout:=(frame.locals[1]'((firstLive root).valid i1)).layout} ((firstLive root).valid i1)} := by
    change TypedRetagEntry.frameWithBorrow (write (firstLive root) i1 value).frame {}=_
    exact (frame_with_borrow (write (firstLive root) i1 value).frame {} (by exact frameBorrow)).trans (by rfl)
  have copy : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace 0 frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent #[] frame entered)=.ok ()
      (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.sourceRoot root value {}).frame post) := by
    rw [sourceFrameEq]
    exact copied
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have arguments:=CurrentCallEmptyProtocolControl.arguments options limits remaining span input.model.debugOff (options.limits.validation-1) (by omega)
    #[] root raw machine post input.tracker next input.runtime.enabled rfl input.model.ghostOff input.model.shallow
    input.model.ghostOff input.model.shallow value value {} count copy
  exact arguments

private theorem counter_view {options remaining span place machine tracker data owner id offset original B physical}
    (core : CurrentCallEmptyContinuation.Core options remaining span place machine tracker data owner id offset original B physical)
    (post : Before) (next : MachineHooks.BorrowState) (memory : post.memory=machine.memory)
    (addresses : post.user.addresses=machine.user.addresses)
    (extras : post.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras)
    (global : next.global={tracker.global with nextPointerTag:=next.global.nextPointerTag})
    (counter : tracker.global.nextPointerTag.value.toNat≤next.global.nextPointerTag.value.toNat)
    (model : DuplicatePrefixCallModel.Model options remaining span post) (tracked : post.borrowTracker=some next)
    (thread : Miri.Concurrency.ThreadRecord) (active : post.threads.activeThread?=some thread) :
    ∃Q : UniformWindow post next data owner id offset 1 .ret,∃P : CurrentCallBoolScalarWrite.Window post place,
      ∃result : CurrentCallEmptyContinuation.Core options remaining span place post next data owner id offset original Q P,
        result.borrowFrame=core.borrowFrame ∧result.node=core.node := by
  obtain ⟨Q,pointer,allocation,precise,runtime⟩:=CurrentCallEmptyIntegerCounterFrame.window B core.runtime post next memory global counter
  obtain ⟨P,pointerEq,idEq,offsetEq,entryEq,binding⟩:=CurrentCallRootPhysicalWindow.view (final:=post) physical core.binding addresses (congrArg MemoryState.live memory)
  have present : Present (ActualWorld post) id B.allocation := by unfold Present ActualWorld;rw [memory];exact B.present
  have parent:=CurrentCallAllocationLicense.spatial core.parentIssued post next B.allocation present (by rw [global];rfl) rfl rfl rfl
    (fun _ _ found=>found) (fun _ node found=>⟨node,found,rfl,rfl,rfl,rfl⟩) B.precise.completion (fun _ _ edge=>edge)
  refine ⟨Q,P,{
    originalId:=core.originalId,binding:=binding,idEq:=idEq.trans core.idEq,
    offsetEq:=(congrArg UInt64.toNat offsetEq).trans core.offsetEq,pointerEq:=pointerEq.trans core.pointerEq,
    allocationEq:=(congrArg LocalAllocation.allocation entryEq).trans (core.allocationEq.trans allocation.symm),
    parentIssued:=by rw [allocation,precise];exact parent,parentBinding:=by rw [allocation];exact core.parentBinding,
    runtime:=runtime,roots:=by rw [allocation];exact core.roots,short:=by rw [allocation];exact core.short,
    concrete:=by rw [pointer];exact core.concrete,node:=core.node,nodeAt:=by rw [allocation,pointer];exact core.nodeAt,
    hidden:=core.hidden,active:=by rw [allocation,pointer,offsetEq];exact core.active,
    source:=core.source,ledger:=by rw [allocation];exact core.ledger.transport memory,borrowFrame:=core.borrowFrame,tags:=core.tags,
    edge:=by rw [precise,pointer];exact core.edge,model:=model,tracked:=tracked,thread:=thread,activeThread:=active,
    physicalReady:=by rw [idEq,offsetEq];exact core.physicalReady.transport extras},rfl,rfl⟩

private theorem integer_entry {options limits remaining span before place}
    (address count : UInt64) (input : OrdinaryInput options limits remaining span before (.integer address) 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (nonnull : address≠0) :
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let value:=(RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm
    ∃(post : RootState)(next : MachineHooks.BorrowState)(R : CurrentCallPostEntryCheckpoint.Return post.machine next place),
    ∃core : CurrentCallEmptyContinuation.Core options remaining span place post.machine next R.data R.owner R.id R.offset R.original R.window R.physical,
      core.borrowFrame=({} : FrameState).addProtector R.id R.node.tag ∧core.node=R.node ∧
      core.thread.topUserRelevantFrame=some 0 ∧
      next.global.nextPointerTag.value.toNat+1<18446744073709551615 ∧
      DuplicatePrefixTypeCacheOrigins.Origins post.machine.user.payload.payload.user.types ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.integer address) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=.ok ()
        (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root value {} count R.id R.node.tag) post.machine) := by
  dsimp only
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let value:=(RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm
  let args:=RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot root value {}) count
  have arguments:=integer_arguments address count input nonnull
  obtain ⟨D,family,offset⟩:=current_data input latent count value
  obtain ⟨phase,last,reserve⟩:=first_phase input rfl count value D family
  obtain ⟨ctx⟩:=ActualRetagContext.exists_context options (remaining+1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨externStatic,wiring,finalAddresses,finalTape,result,protocol,⟨O⟩⟩:=first_with_protocol input ctx D phase last
  let R:=O.output
  let next:={D.next with global:=result.global}
  have model:=CurrentCallConversionBoolModel.model O (source_model input)
  have origins:=CurrentCallConversionBoolModel.origins O input.cacheOrigins
  obtain ⟨thread,active,_⟩:=input.stackReady
  let currentThread:={thread with topUserRelevantFrame:=some 0}
  have activeNow : O.post.machine.threads.activeThread?=some currentThread := by
    rw [CurrentCallConversionBoolModel.threads O]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  let frame:FrameState:=({} : FrameState).addProtector R.id R.node.tag
  let core:=CurrentCallEmptyReturnCore.of_return R none .none frame rfl model O.tracked currentThread activeNow
  have finalState : O.post=Storage.withCurrent #[]
      (registeredFrame (atSpan args ⟨601⟩).frame {} D.family.allocation (sourceTracker input).global.nextPointerTag) O.post.machine :=
    state_of_stack O.post _ O.stack
  have protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent #[] (atSpan args ⟨601⟩).frame (sourceMachine input))=.ok ()
      (Storage.withCurrent #[] (registeredFrame (atSpan args ⟨601⟩).frame {} R.id R.node.tag) O.post.machine) := by
    have actual:=O.actual
    rw [finalState] at actual
    rw [O.id,O.tag]
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place _ = _
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining+1) span ctx place input.returnLayout
      options.limits.retag limits.retag) _).symm.trans actual
  have entered:=CurrentCallEmptyProtocolControl.init_of_arguments options limits remaining span before #[] place input.model.noDataRace
    input.model.debugOff input.stackReady value value {} count (sourceMachine input) O.post.machine R.id R.node.tag arguments protection
  have margin:=result.rootBudget
  have room : next.global.nextPointerTag.value.toNat+1<18446744073709551615 := by
    change result.global.nextPointerTag.value.toNat+1<18446744073709551615
    omega
  refine ⟨O.post,next,R,core,rfl,rfl,rfl,room,origins,?_⟩
  exact entered

private theorem integer_frame_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (root : RootFrame) (address count : UInt64) (id : AllocId) (tag : BorTag) :
    CurrentCallEmptyProtocolControl.frame root (RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm {} count id tag=
      CurrentCallEmptyIntegerFacts.frame options remaining span before tracker root address count id tag := by rfl

private theorem miss_frame_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (root : RootFrame) (address count : UInt64) (id : AllocId) (tag : BorTag)
    (miss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none) :
    CurrentCallEmptyProtocolControl.frame root (CurrentCallEmptyMissFacts.value options remaining span address) {} count id tag=
      CurrentCallEmptyMissFacts.frame options remaining span before tracker root address count id tag miss := by rfl

private theorem result_of_run {options limits remaining span before argument count place}
    (frame : CompilerFrameContext.ActualFrame) (machine : Before)
    (entered : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0),.Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=.ok () (Storage.withCurrent #[] frame machine))
    (run : ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[]) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  obtain ⟨final,trace,terminal,empty⟩:=run
  let start:=Storage.withCurrent #[] frame machine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [empty];decide
  exact ⟨start,final,entered,trace,terminal,empty,SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

/-- An integer empty source and a CURRENT Bool destination execute the original call for every count. -/
theorem integer {options limits remaining span before place} (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.integer address) 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 count place := by
  have empty : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.integer address)) := by
    rcases input.source with empty|positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  have nonnull : address≠0:=empty.1
  obtain ⟨post,next,R,core,borrow,node,top,room,origins,entered⟩:=integer_entry address count input latent nonnull
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let value:=(RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have validationPositive : 0<options.limits.validation := by
    have room:=input.resources.configuredFuel.2.2.2;unfold DuplicatePrefixCallSpecification.work at room;omega
  have dynamicPositive : 0<options.place.dynamicFuel := by
    have room:=input.resources.dynamicFuel;unfold DuplicatePrefixCallSpecification.work at room;omega
  have validationEq : options.limits.validation=(options.limits.validation-1)+1:=by omega
  have dynamicEq : options.place.dynamicFuel=(options.place.dynamicFuel-1)+1:=by omega
  apply result_of_run _ _ entered
  by_cases zero : count=0
  · subst count
    have returned:=CurrentCallEmptyContinuation.zero core limits root value {} raw
      (by rw [node];exact borrow) rfl rfl rfl (options.limits.validation-1) validationEq
    simpa only [node] using returned
  · have dispatchPositive : 0<limits.callDispatch := by
      have room:=input.resources.executionFuel.1;unfold DuplicatePrefixCallSpecification.work at room;omega
    have dispatchEq : limits.callDispatch=(limits.callDispatch-1)+1:=by omega
    obtain ⟨frame,finalMachine,finalTracker,trace,body,identity,callee,extra,returnPlace,continuation,varargs,localsIdentity,
      size,located,slot0,immediate,memory,tracked,mode,global,counter,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,
      ⟨thread,active⟩⟩:=CurrentCallEmptyIntegerBodyControl.to_return options limits remaining span (CurrentCallPush.preparedMachine before #[])
      input.tracker root address count R.id R.node.tag raw post.machine next core.tracked core.model origins nonnull zero room
      (options.place.dynamicFuel-1) (options.limits.validation-1) dynamicEq validationEq (limits.callDispatch-1) dispatchEq core.thread core.activeThread top
    have finalMode : finalTracker.retagMode=.Default := by
      obtain ⟨old,enabled,default⟩:=core.model.defaultTracker
      have same : old=next:=Option.some.inj (enabled.symm.trans core.tracked)
      subst old
      exact mode.trans default
    have model : DuplicatePrefixCallModel.Model options remaining span finalMachine :=
      ⟨core.model.debugOff,core.model.preciseOff,core.model.implicitOff,ghost,shallow,⟨finalTracker,tracked,finalMode⟩,race,
        backend.trans core.model.noBackend,by rw [types];exact core.model.metadata,fixed,unchecked,noGc,core.model.nullComparator,core.model.sourceMatches⟩
    obtain ⟨Q,P,current,borrowEq,nodeEq⟩:=counter_view core finalMachine finalTracker memory addresses extras global
      (by rw [counter];omega) model tracked thread active
    have metadata:=CurrentCallEmptyProtocolControl.metadata root value {} count R.id R.node.tag
    have actualExtra : (CurrentCallEmptyIntegerFacts.frame options remaining span (CurrentCallPush.preparedMachine before #[]) input.tracker root address count R.id R.node.tag).extra=
        (CurrentCallEmptyProtocolControl.frame root value {} count R.id R.node.tag).extra := by rw [integer_frame_eq]
    have ready : CurrentCallEmptyContinuation.Ready options remaining span place finalMachine finalTracker R.data R.owner R.id R.offset R.original Q P frame := {
      toCore:=current,frameTracked:=by rw [borrowEq,borrow,extra,actualExtra];exact metadata.2.2.2.2.2.2.2.1,
      body:=by rw [body,←integer_frame_eq];exact metadata.1.trans root.body,
      location:=located,size:=size,noClocks:=by rw [extra,actualExtra];exact metadata.2.2.2.2.2.2.1.trans root.noClocks,
      stop:=by rw [continuation,←integer_frame_eq];exact metadata.2.2.2.1,
      varargs:=by rw [varargs,←integer_frame_eq];exact metadata.2.2.2.2.2.1,
      immediate:=immediate,value:=false,slot0:=slot0,destination:=by rw [returnPlace,←integer_frame_eq];rw [metadata.2.2.2.2.1];rfl}
    obtain ⟨final,returned,terminal,empty⟩:=CurrentCallEmptyContinuation.finish ready limits (options.limits.validation-1) validationEq
    refine ⟨final,SuccessfulTrace.append ?_ returned,terminal,empty⟩
    have frameEq:=integer_frame_eq options remaining span (CurrentCallPush.preparedMachine before #[]) input.tracker root address count R.id R.node.tag
    rw [←frameEq] at trace
    exact trace

private theorem protocol_cached {memory : MemoryState Provenance BorrowTree MiriMemoryKind}
    {thread : Miri.Memory.AllocAddresses.AddressThreadId} {before after : Miri.Memory.AllocAddresses.GlobalAddressState}
    {tape nextTape : ExecutionChoices.Tape} {ids : List AllocId}
    (protocol : CurrentCallConversionChoiceProtocol.AddressProtocol memory thread before tape ids after nextTape)
    (all : ∀id∈ids,∃entry,before.baseAddr.find? (fun row=>row.allocId==id)=some entry) : after=before := by
  induction protocol with
  | nil=>rfl
  | cached addresses tape id rest base hit final tape' tail ih=>
    exact ih (fun id member=>all id (List.mem_cons_of_mem _ member))
  | typeId addresses tape id rest info uncached metadata kind final tape' tail ih=>
    obtain ⟨entry,hit⟩:=all id (by simp)
    rw [uncached] at hit
    cases hit
  | managed addresses tape id rest info uncached metadata kind generation generationEq block final tape' tail ih=>
    obtain ⟨entry,hit⟩:=all id (by simp)
    rw [uncached] at hit
    cases hit

private theorem protocol_nil {memory : MemoryState Provenance BorrowTree MiriMemoryKind}
    {thread : Miri.Memory.AllocAddresses.AddressThreadId} {before after : Miri.Memory.AllocAddresses.GlobalAddressState}
    {tape nextTape : ExecutionChoices.Tape}
    (protocol : CurrentCallConversionChoiceProtocol.AddressProtocol memory thread before tape [] after nextTape) : before=after := by
  cases protocol
  rfl

private theorem miss_preserved {options limits remaining span before place}
    (address : UInt64) (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (nonstrict : before.user.addresses.provenanceMode≠.strict)
    (_coherent : GlobalAddressRecurringFormation.State before.memory before.user.addresses)
    (miss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none)
    (after : Before) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (protocol : CurrentCallConversionChoiceProtocol.AddressProtocol before.memory (UInt32.ofNat before.threads.activeThread.toNat)
      before.user.addresses (EvalPointerSource.tape.get before)
      (CurrentCallConversionPlan.selectedIds before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place) finalAddresses finalTape)
    (addresses : after.user.addresses=finalAddresses)
    (mode : finalAddresses.provenanceMode=before.user.addresses.provenanceMode)
    (info : ∀id,after.memory.getAllocInfo id=before.memory.getAllocInfo id)
    (live : ∀id,after.memory.isAllocLive id=before.memory.isAllocLive id) :
    after.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup after.memory)=.ok none := by
  have budget:=CurrentCallOrdinaryConversionInitial.resources input
  have hooks : GlobalAddressLiveErrorExclusion.lookup after.memory=GlobalAddressLiveErrorExclusion.lookup before.memory := by
    unfold GlobalAddressLiveErrorExclusion.lookup
    congr 1
    · funext id;rw [info]
    · funext id;rw [live]
  rcases budget with cached | ⟨generation,good,aligned,ending,limit⟩
  · have unchanged:=protocol_cached protocol cached
    rw [addresses,unchanged,hooks]
    exact miss
  · rcases good with ⟨ordered,apart,rows,generationEq,managed,cursor,frontier,holes,bounded,pairwise⟩
    have budget:=CurrentCallOrdinaryConversionInitial.resources input
    have metadata:=CurrentCallOrdinaryConversionSelected.targets_metadata input
    have formation := fun id member missing info known => CurrentCallConversionFiniteFold.formation_initial before id
      (metadata id member) missing info known
    have nextOrdered:=CurrentCallConversionProtocolOrdered.protocol before _ _ _ finalAddresses finalTape protocol budget ordered metadata formation
    have nextRows:=CurrentCallConversionProtocolOrdered.protocol_info_rows before _ _ _ finalAddresses finalTape protocol budget ordered rows metadata formation
    have retained:=CurrentCallConversionMissFrame.protocol_rows before.memory _ before.user.addresses finalAddresses _ finalTape _ protocol input.exposedCached
    have oldKnown : ∀row∈before.user.addresses.intToPtrMap,
        (GlobalAddressLiveErrorExclusion.lookup before.memory).sizeOf row.allocId=some (CurrentCallConversionInfoRows.sizes before.memory row.allocId) := by
      intro row member
      obtain ⟨known,actual,notDead,size⟩:=rows row member
      simp only [GlobalAddressLiveErrorExclusion.lookup,actual,Except.toOption,Option.map_some,size]
    have nextKnown : ∀row∈finalAddresses.intToPtrMap,
        (GlobalAddressLiveErrorExclusion.lookup after.memory).sizeOf row.allocId=some (CurrentCallConversionInfoRows.sizes before.memory row.allocId) := by
      intro row member
      obtain ⟨known,actual,notDead,size⟩:=nextRows row member
      simp only [GlobalAddressLiveErrorExclusion.lookup,info,actual,Except.toOption,Option.map_some,size]
    rw [addresses]
    exact CurrentCallConversionMissFrame.lookup_miss before.user.addresses finalAddresses _ ordered apart nextOrdered retained.2.1 retained.2.2
      (GlobalAddressLiveErrorExclusion.lookup before.memory) (GlobalAddressLiveErrorExclusion.lookup after.memory) address nonstrict mode oldKnown nextKnown miss

private theorem miss_finish {options limits remaining span before place} (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (initialMiss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none)
    (nonnull : address≠0) (post : RootState) (next : MachineHooks.BorrowState)
    (R : CurrentCallPostEntryCheckpoint.Return post.machine next place)
    (core : CurrentCallEmptyContinuation.Core options remaining span place post.machine next R.data R.owner R.id R.offset R.original R.window R.physical)
    (borrow : core.borrowFrame=({} : FrameState).addProtector R.id R.node.tag) (node : core.node=R.node)
    (top : core.thread.topUserRelevantFrame=some 0)
    (room : next.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins post.machine.user.payload.payload.user.types)
    (postMode : post.machine.user.addresses.provenanceMode≠.strict)
    (postMiss : post.machine.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup post.machine.memory)=.ok none)
    (entered : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0),.Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=.ok () (Storage.withCurrent #[]
        (CurrentCallEmptyProtocolControl.frame (CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace)
          (CurrentCallEmptyMissFacts.value options remaining span address) {} count R.id R.node.tag) post.machine)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let value:=CurrentCallEmptyMissFacts.value options remaining span address
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have validationPositive : 0<options.limits.validation := by
    have room:=input.resources.configuredFuel.2.2.2;unfold DuplicatePrefixCallSpecification.work at room;omega
  have dynamicPositive : 0<options.place.dynamicFuel := by
    have room:=input.resources.dynamicFuel;unfold DuplicatePrefixCallSpecification.work at room;omega
  have validationEq : options.limits.validation=(options.limits.validation-1)+1:=by omega
  have dynamicEq : options.place.dynamicFuel=(options.place.dynamicFuel-1)+1:=by omega
  apply result_of_run _ _ entered
  by_cases zero : count=0
  · subst count
    have returned:=CurrentCallEmptyContinuation.zero core limits root value {} raw
      (by rw [node];exact borrow) rfl rfl rfl (options.limits.validation-1) validationEq
    simpa only [node] using returned
  · have dispatchPositive : 0<limits.callDispatch := by
      have room:=input.resources.executionFuel.1;unfold DuplicatePrefixCallSpecification.work at room;omega
    have dispatchEq : limits.callDispatch=(limits.callDispatch-1)+1:=by omega
    obtain ⟨frame,finalMachine,finalTracker,trace,body,identity,callee,extra,returnPlace,continuation,varargs,localsIdentity,
      size,located,slot0,immediate,memory,tracked,mode,global,counter,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,
      ⟨thread,active⟩⟩:=CurrentCallEmptyMissBodyControl.to_return options limits remaining span before
      input.tracker root address count R.id R.node.tag initialMiss raw post.machine next core.tracked core.model origins nonnull zero postMode postMiss room
      (options.place.dynamicFuel-1) (options.limits.validation-1) dynamicEq validationEq (limits.callDispatch-1) dispatchEq core.thread core.activeThread top
    have finalMode : finalTracker.retagMode=.Default := by
      obtain ⟨old,enabled,default⟩:=core.model.defaultTracker
      have same : old=next:=Option.some.inj (enabled.symm.trans core.tracked)
      subst old
      exact mode.trans default
    have model : DuplicatePrefixCallModel.Model options remaining span finalMachine :=
      ⟨core.model.debugOff,core.model.preciseOff,core.model.implicitOff,ghost,shallow,⟨finalTracker,tracked,finalMode⟩,race,
        backend.trans core.model.noBackend,by rw [types];exact core.model.metadata,fixed,unchecked,noGc,core.model.nullComparator,core.model.sourceMatches⟩
    obtain ⟨Q,P,current,borrowEq,nodeEq⟩:=counter_view core finalMachine finalTracker memory addresses extras global
      (by rw [counter];omega) model tracked thread active
    have metadata:=CurrentCallEmptyProtocolControl.metadata root value {} count R.id R.node.tag
    have actualExtra : (CurrentCallEmptyMissFacts.frame options remaining span before input.tracker root address count R.id R.node.tag initialMiss).extra=
        (CurrentCallEmptyProtocolControl.frame root value {} count R.id R.node.tag).extra := by rw [miss_frame_eq]
    have ready : CurrentCallEmptyContinuation.Ready options remaining span place finalMachine finalTracker R.data R.owner R.id R.offset R.original Q P frame := {
      toCore:=current,frameTracked:=by rw [borrowEq,borrow,extra,actualExtra];exact metadata.2.2.2.2.2.2.2.1,
      body:=by rw [body,←miss_frame_eq];exact metadata.1.trans root.body,
      location:=located,size:=size,noClocks:=by rw [extra,actualExtra];exact metadata.2.2.2.2.2.2.1.trans root.noClocks,
      stop:=by rw [continuation,←miss_frame_eq];exact metadata.2.2.2.1,
      varargs:=by rw [varargs,←miss_frame_eq];exact metadata.2.2.2.2.2.1,
      immediate:=immediate,value:=false,slot0:=slot0,destination:=by rw [returnPlace,←miss_frame_eq];rw [metadata.2.2.2.2.1];rfl}
    obtain ⟨final,returned,terminal,empty⟩:=CurrentCallEmptyContinuation.finish ready limits (options.limits.validation-1) validationEq
    refine ⟨final,SuccessfulTrace.append ?_ returned,terminal,empty⟩
    have frameEq:=miss_frame_eq options remaining span before input.tracker root address count R.id R.node.tag initialMiss
    rw [←frameEq] at trace
    exact trace

private theorem miss_entry {options limits remaining span before place}
    (address count : UInt64) (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (nonnull : address≠0) (nonstrict : before.user.addresses.provenanceMode≠.strict)
    (coherent : GlobalAddressRecurringFormation.State before.memory before.user.addresses)
    (initialMiss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none) :
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let value:=(CurrentCallEmptyMissFacts.value options remaining span address)
    ∃(post : RootState)(next : MachineHooks.BorrowState)(R : CurrentCallPostEntryCheckpoint.Return post.machine next place),
    ∃core : CurrentCallEmptyContinuation.Core options remaining span place post.machine next R.data R.owner R.id R.offset R.original R.window R.physical,
      core.borrowFrame=({} : FrameState).addProtector R.id R.node.tag ∧core.node=R.node ∧
      core.thread.topUserRelevantFrame=some 0 ∧
      next.global.nextPointerTag.value.toNat+1<18446744073709551615 ∧
      DuplicatePrefixTypeCacheOrigins.Origins post.machine.user.payload.payload.user.types ∧
      post.machine.user.addresses.provenanceMode≠.strict ∧
      post.machine.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup post.machine.memory)=.ok none ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=.ok ()
        (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root value {} count R.id R.node.tag) post.machine) := by
  dsimp only
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let value:=(CurrentCallEmptyMissFacts.value options remaining span address)
  let args:=RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot root value {}) count
  have arguments:=miss_arguments address count input nonnull nonstrict initialMiss
  obtain ⟨D,family,offset⟩:=current_data input latent count value
  have queryNone : CurrentCallConversionPlan.sourceQuery before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0=.ok none := by
    unfold CurrentCallConversionPlan.sourceQuery CurrentCallConversionPlan.query
    simp [Miri.Memory.AllocAddresses.GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,initialMiss]
    rfl
  obtain ⟨phase,last,reserve⟩:=first_phase input queryNone count value D family
  obtain ⟨ctx⟩:=ActualRetagContext.exists_context options (remaining+1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨externStatic,wiring,finalAddresses,finalTape,result,protocol,⟨O⟩⟩:=first_with_protocol input ctx D phase last
  let R:=O.output
  let next:={D.next with global:=result.global}
  have model:=CurrentCallConversionBoolModel.model O (source_model input)
  have origins:=CurrentCallConversionBoolModel.origins O input.cacheOrigins
  obtain ⟨thread,active,_⟩:=input.stackReady
  let currentThread:={thread with topUserRelevantFrame:=some 0}
  have activeNow : O.post.machine.threads.activeThread?=some currentThread := by
    rw [CurrentCallConversionBoolModel.threads O]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  let frame:FrameState:=({} : FrameState).addProtector R.id R.node.tag
  let core:=CurrentCallEmptyReturnCore.of_return R none .none frame rfl model O.tracked currentThread activeNow
  have finalState : O.post=Storage.withCurrent #[]
      (registeredFrame (atSpan args ⟨601⟩).frame {} D.family.allocation (sourceTracker input).global.nextPointerTag) O.post.machine :=
    state_of_stack O.post _ O.stack
  have protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent #[] (atSpan args ⟨601⟩).frame (sourceMachine input))=.ok ()
      (Storage.withCurrent #[] (registeredFrame (atSpan args ⟨601⟩).frame {} R.id R.node.tag) O.post.machine) := by
    have actual:=O.actual
    rw [finalState] at actual
    rw [O.id,O.tag]
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place _ = _
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining+1) span ctx place input.returnLayout
      options.limits.retag limits.retag) _).symm.trans actual
  have entered:=CurrentCallEmptyProtocolControl.init_of_arguments options limits remaining span before #[] place input.model.noDataRace
    input.model.debugOff input.stackReady value value {} count (sourceMachine input) O.post.machine R.id R.node.tag arguments protection
  have margin:=result.rootBudget
  have room : next.global.nextPointerTag.value.toNat+1<18446744073709551615 := by
    change result.global.nextPointerTag.value.toNat+1<18446744073709551615
    omega
  have endAddresses : result.addresses=finalAddresses := protocol_nil result.protocol
  have actualAddresses : O.post.machine.user.addresses=finalAddresses :=
    (CurrentCallConversionBoolModel.addresses O).trans endAddresses
  have finalMode : finalAddresses.provenanceMode=before.user.addresses.provenanceMode := by
    rw [←endAddresses,result.provenanceMode]
    rfl
  have postMode : O.post.machine.user.addresses.provenanceMode≠.strict := by
    rw [actualAddresses,finalMode];exact nonstrict
  have info := CurrentCallConversionBoolMetadata.getAllocInfo ctx wiring O
  have live := CurrentCallConversionBoolMetadata.isAllocLive O
  have initialProtocol : CurrentCallConversionChoiceProtocol.AddressProtocol before.memory
      (UInt32.ofNat before.threads.activeThread.toNat) before.user.addresses (EvalPointerSource.tape.get before)
      (CurrentCallConversionPlan.selectedIds before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
      finalAddresses finalTape := protocol
  have postMiss:=miss_preserved address input nonstrict coherent initialMiss O.post.machine finalAddresses finalTape
    initialProtocol actualAddresses finalMode info live
  refine ⟨O.post,next,R,core,rfl,rfl,rfl,room,origins,postMode,postMiss,?_⟩
  exact entered


/-- An unresolved wildcard empty source and a CURRENT Bool execute the original call for every count. -/
theorem miss {options limits remaining span before place} (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (initialMiss : before.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  have empty : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer
      (.pointer (Pointer.new .wildcard (Size.ofBytes address)))) := by
    rcases input.source with empty|positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  change address≠0 ∧ before.user.addresses.provenanceMode≠.strict ∧
    GlobalAddressRecurringFormation.State before.memory before.user.addresses ∧ _ at empty
  obtain ⟨nonnull,nonstrict,coherent,_⟩:=empty
  obtain ⟨post,next,R,core,borrow,node,top,room,origins,postMode,postMiss,entered⟩:=
    miss_entry address count input latent nonnull nonstrict coherent initialMiss
  exact miss_finish address count input initialMiss nonnull post next R core borrow node top room origins postMode postMiss entered

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyUnlocatedCurrent

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyUnlocatedCurrent.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty unlocated CURRENT dependency {name}: {dependency}"
