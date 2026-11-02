import duplicate_prefix.CurrentCallOrdinaryConversionEnsure
import duplicate_prefix.CurrentCallEmptyMaterializedCopy
import duplicate_prefix.CurrentCallEmptyMaterializedWildcardCopy
import duplicate_prefix.CurrentCallEmptyProtocolControl
import duplicate_prefix.CurrentCallPreparedResources
import duplicate_prefix.StaticGlobalAllocInfo
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private theorem fresh {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    input.tracker.global.nextPointerTag.value<18446744073709551615 := by
  have room:=input.resources.tagRoom
  simpa [UInt64.lt_iff_toNat_lt] using (show input.tracker.global.nextPointerTag.value.toNat<18446744073709551615 by omega)
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
private theorem successor_nat (tag : BorTag) (room : tag.value<18446744073709551615) :
    (TypedRetagEmpty.successorTag tag room).value.toNat=tag.value.toNat+1 := by
  have bound : tag.value.toNat<18446744073709551615 := by simpa [UInt64.lt_iff_toNat_lt] using room
  change (tag.value+1).toNat=_
  rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega)]
def finalMachine (options : EvalConfigurationCore.Options) (after : Before)
    (id : AllocId) (root tag : BorTag) (converted : Allocation Provenance Unit) : Before :=
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root converted.byteSize)⟩
  let installed:=CurrentCallConversionMaterialize.installed
    (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) after id ⟨none,#[]⟩) id .global entry.allocation
  let raw:={installed with memory:=(RetagEntry.updatedMemory installed.memory id entry
    (TypedRetagConcreteEmpty.lazyTree root tag converted.byteSize.bytes))}
  {raw with user:={raw.user with payload:={raw.user.payload with ghost:=false}}}

def registered {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (pointer : Pointer Provenance) : RootState :=
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let frame:=(firstLive root).frame
  let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 reference).imm
  let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame frame 1 value ((firstLive root).valid i1)
  let machine:=ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry
  let active:={machine with user:={machine.user with payload:={machine.user.payload with ghost:=true}}}
  registeredState #[] copied {} (allocatedMachine active ⟨input.tracker.global,.FnEntry⟩ (fresh input))
    (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) id input.tracker.global.nextPointerTag

def nextTracker {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place) : MachineHooks.BorrowState :=
  registeredTracker (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) input.tracker.global.nextPointerTag

/-- Real CURRENT empty copy from initial metadata and the real converter. -/
theorem concrete {options limits remaining span before place}
    (id : AllocId) (rootTag : BorTag) (base offset : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0 place)
    (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (registry : InitialRegistryVacant before id)
    (cachedRoot : input.tracker.global.rootTag? id=some rootTag)
    (cachedBase : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (nonnull : base+offset≠0) :
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let frame:=(firstLive root).frame
    let machine:=ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry
    let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) 0 reference).imm
    let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame frame 1 value ((firstLive root).valid i1)
    let active:={machine with user:={machine.user with payload:={machine.user.payload with ghost:=true}}}
    let phase:=registeredState #[] copied {} (allocatedMachine active ⟨input.tracker.global,.FnEntry⟩ (fresh input))
      (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) id input.tracker.global.nextPointerTag
    ∃rest : List (Allocation CtfeProvenance Unit),∃externStatic finalAddresses finalTape,
    ∃result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic phase.machine
      (registeredTracker (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) input.tracker.global.nextPointerTag)
      (rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) 15 finalAddresses finalTape,
    ∃afterFrame,
      (CurrentCallConversionActualEnsure.hooks options).rootPointer=
        PointerSource.globalRootPointer Miri.Input.EvalPointerSource.tape
          (CurrentCallConversionActualEnsure.hooks options).address externStatic ∧
      CurrentCallConversionPlan.selectedPayloads before
        (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0 place=source::rest ∧
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate value,reference⟩ (LocalPlaces.localRuntimePlace 0 frame 1 reference).stackView
        (Storage.withCurrent #[] frame machine)=.ok () (Storage.withCurrent #[] afterFrame
          (finalMachine options result.machine id rootTag input.tracker.global.nextPointerTag result.converted)) ∧
      afterFrame=(CurrentCallEmptyProtocolControl.sourceRoot root
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
        (({} : FrameState).addProtector id input.tracker.global.nextPointerTag)).frame := by
  dsimp only
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let frame:=(firstLive root).frame
  let machine:=ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry
  let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) 0 reference).imm
  let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame frame 1 value ((firstLive root).valid i1)
  let active:={machine with user:={machine.user with payload:={machine.user.payload with ghost:=true}}}
  let phase:=registeredState #[] copied {} (allocatedMachine active ⟨input.tracker.global,.FnEntry⟩ (fresh input))
    (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) id input.tracker.global.nextPointerTag
  let tracker:=registeredTracker (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) input.tracker.global.nextPointerTag
  have payload:=CurrentCallConversionPlanAdequacy.payload_of_current before id source absent noFunction noVaList current
  have query : CurrentCallConversionPlan.sourceQuery before
      (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0=.ok (some id) :=
    CurrentCallConversionPlanAdequacy.query_concrete before _ 0 id rootTag base rfl cachedBase
  obtain ⟨rest,head,_⟩:=CurrentCallOrdinaryConversionSelected.source_first before _ 0 place id source query payload
  have currentPhase : CurrentPayload phase.machine id source := by
    cases current with
    | memory descriptor=>exact .memory descriptor
    | internalStatic definition descriptor initializer=>exact .internalStatic definition descriptor initializer
  obtain ⟨externStatic,wiring,finalAddresses,finalTape,result,ensure⟩:=CurrentCallOrdinaryConversionEnsure.first input phase tracker
    (by intro query;rfl) rfl rfl rfl (by intro query;rfl) 1 15 (by decide) (by decide)
    (by change (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag (fresh input)).value.toNat≤_;rw [successor_nat];exact Nat.le_refl _)
    rfl (fun target member=>CurrentCallOrdinaryConversionSelected.targets_metadata input target member)
    id rootTag source rest head currentPhase absent cachedRoot registry input.model.noDataRace
  obtain ⟨ctx,actualPointers⟩:=GlobalEmptyReferenceContext.exists_context options remaining span input.model.preciseOff input.model.implicitOff
  have distinct : rootTag≠input.tracker.global.nextPointerTag := by
    have below:=cached_below input id rootTag cachedRoot
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  have info : machine.memory.getAllocInfo id=.ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩ := by
    cases current with
    | memory descriptor=>exact GlobalDataOnlyMaterialize.alloc_info machine id source absent noFunction noVaList descriptor
    | internalStatic definition descriptor initializer=>exact StaticGlobalAllocInfo.alloc_info machine id source definition absent noFunction noVaList descriptor
  have afterGhost : (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) result.machine id ⟨none,#[]⟩).user.payload.ghost=true := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
    rfl
  have frameBorrow : frame.extra.borrowTracker=some ({} : FrameState) := by
    change root.frame.extra.borrowTracker=some ({} : FrameState)
    exact RootEntryFrame.raw_borrow _ _ _ input.tracker input.runtime.enabled
  have live : (frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [frame,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached : (frame.locals[1]'((firstLive root).valid i1)).layout=some reference := by
    simp only [frame,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,firstCache,
      RootFrameData.cache,LocalOperands.cachedLayoutFrame,atSpan,i1]
  have dynamicPositive : 0<options.place.dynamicFuel := by have room:=input.resources.dynamicFuel;unfold DuplicatePrefixCallSpecification.work at room;omega
  have validationPositive : 0<options.limits.validation := by have room:=input.resources.configuredFuel.2.2.2;unfold DuplicatePrefixCallSpecification.work at room;omega
  have copy:=CurrentCallEmptyMaterializedCopy.concrete options limits remaining span ctx actualPointers input.model.debugOff
    input.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1) (by omega) (by omega)
    #[] frame machine 1 ((firstLive root).valid i1) .uninit live cached (firstLive root).noClocks input.model.ghostOff input.model.shallow
    {} frameBorrow input.tracker.global (by rfl) (fresh input) id rootTag base offset nonnull cachedBase distinct
    _ info rfl result.converted
    (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) result.machine id ⟨none,#[]⟩) afterGhost
    input.model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ input.model.metadata input.cacheOrigins)
    (LocalPlaces.localRuntimePlace 0 frame 1 reference).stackView rfl ensure
  refine ⟨rest,externStatic,finalAddresses,finalTape,result,_,wiring,head,copy,?_⟩
  simp only [CurrentCallEmptyProtocolControl.sourceRoot,ConcreteEmptyReferenceArgumentCopy.copiedFrame,
    registeredFrame,TypedRetagEntry.frameWithBorrow,frame,RootFrameData.write,firstLive,firstCache,
    RootFrameData.live,RootFrameData.cache,atSpan,LocalOperands.cachedLayoutFrame,Array.set_set,Array.getElem_set_self,i1]
  rfl
def finalWildcardMachine (options : EvalConfigurationCore.Options) (after : Before)
    (id : AllocId) (root tag : BorTag) (converted : Allocation Provenance Unit) : Before :=
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root converted.byteSize)⟩
  let installed:=CurrentCallConversionMaterialize.installed
    (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) after id ⟨none,#[]⟩) id .global entry.allocation
  let raw:={installed with memory:=(RetagEntry.updatedMemory installed.memory id entry
    (CurrentCallEmptyMaterializedWildcard.finalTree root tag converted.byteSize))}
  {raw with user:={raw.user with payload:={raw.user.payload with ghost:=false}}}

/-- Real CURRENT empty copy from initial metadata and the real converter. -/
theorem wildcard {options limits remaining span before place}
    (id : AllocId) (rootTag : BorTag) (base offset : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset)))) 0 place)
    (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (registry : InitialRegistryVacant before id)
    (cachedRoot : input.tracker.global.rootTag? id=some rootTag)
    (cachedBase : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (nonnull : base+offset≠0)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : before.user.addresses.exposed.contains id=true) :
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let frame:=(firstLive root).frame
    let machine:=ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry
    let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference).imm
    let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame frame 1 value ((firstLive root).valid i1)
    let active:={machine with user:={machine.user with payload:={machine.user.payload with ghost:=true}}}
    let phase:=registeredState #[] copied {} (allocatedMachine active ⟨input.tracker.global,.FnEntry⟩ (fresh input))
      (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) id input.tracker.global.nextPointerTag
    ∃rest : List (Allocation CtfeProvenance Unit),∃externStatic finalAddresses finalTape,
    ∃result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic phase.machine
      (registeredTracker (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) input.tracker.global.nextPointerTag)
      (rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) 15 finalAddresses finalTape,
    ∃afterFrame,
      (CurrentCallConversionActualEnsure.hooks options).rootPointer=
        PointerSource.globalRootPointer Miri.Input.EvalPointerSource.tape
          (CurrentCallConversionActualEnsure.hooks options).address externStatic ∧
      CurrentCallConversionPlan.selectedPayloads before
        (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset)))) 0 place=source::rest ∧
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate value,reference⟩ (LocalPlaces.localRuntimePlace 0 frame 1 reference).stackView
        (Storage.withCurrent #[] frame machine)=.ok () (Storage.withCurrent #[] afterFrame
          (finalWildcardMachine options result.machine id rootTag input.tracker.global.nextPointerTag result.converted)) ∧
      afterFrame=(CurrentCallEmptyProtocolControl.sourceRoot root
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
        (({} : FrameState).addProtector id input.tracker.global.nextPointerTag)).frame := by
  dsimp only
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let frame:=(firstLive root).frame
  let machine:=ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry
  let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference).imm
  let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame frame 1 value ((firstLive root).valid i1)
  let active:={machine with user:={machine.user with payload:={machine.user.payload with ghost:=true}}}
  let phase:=registeredState #[] copied {} (allocatedMachine active ⟨input.tracker.global,.FnEntry⟩ (fresh input))
    (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) id input.tracker.global.nextPointerTag
  let tracker:=registeredTracker (allocatedTracker ⟨input.tracker.global,.FnEntry⟩ (fresh input)) input.tracker.global.nextPointerTag
  have payload:=CurrentCallConversionPlanAdequacy.payload_of_current before id source absent noFunction noVaList current
  have physical : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset))))) := by
    rcases input.source with empty | positive
    · exact empty.2.1
    · exact (positive.1 rfl).elim
  have nonstrict:=physical.2.1
  have allocLive : before.memory.isAllocLive id=true:=physical.2.2.1.live.2 id (Array.contains_iff_mem.mp exposed)
  have initialInfo : before.memory.getAllocInfo id=.ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩ := by
    cases current with
    | memory descriptor=>exact GlobalDataOnlyMaterialize.alloc_info before id source absent noFunction noVaList descriptor
    | internalStatic definition descriptor initializer=>exact StaticGlobalAllocInfo.alloc_info before id source definition absent noFunction noVaList descriptor
  have query : CurrentCallConversionPlan.sourceQuery before
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset)))) 0=.ok (some id) :=
    CurrentCallConversionPlanAdequacy.query_wildcard before _ 0 id base ⟨source.byteSize,source.align,.liveData,source.mutability⟩ rfl (by decide) geometry nonstrict exposed cachedBase initialInfo allocLive
  obtain ⟨rest,head,_⟩:=CurrentCallOrdinaryConversionSelected.source_first before _ 0 place id source query payload
  have currentPhase : CurrentPayload phase.machine id source := by
    cases current with
    | memory descriptor=>exact .memory descriptor
    | internalStatic definition descriptor initializer=>exact .internalStatic definition descriptor initializer
  obtain ⟨externStatic,wiring,finalAddresses,finalTape,result,ensure⟩:=CurrentCallOrdinaryConversionEnsure.first input phase tracker
    (by intro query;rfl) rfl rfl rfl (by intro query;rfl) 1 15 (by decide) (by decide)
    (by change (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag (fresh input)).value.toNat≤_;rw [successor_nat];exact Nat.le_refl _)
    rfl (fun target member=>CurrentCallOrdinaryConversionSelected.targets_metadata input target member)
    id rootTag source rest head currentPhase absent cachedRoot registry input.model.noDataRace
  obtain ⟨ctx,actualPointers⟩:=GlobalEmptyReferenceContext.exists_context options remaining span input.model.preciseOff input.model.implicitOff
  have distinct : rootTag≠input.tracker.global.nextPointerTag := by
    have below:=cached_below input id rootTag cachedRoot
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  have info : machine.memory.getAllocInfo id=.ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩ := by
    cases current with
    | memory descriptor=>exact GlobalDataOnlyMaterialize.alloc_info machine id source absent noFunction noVaList descriptor
    | internalStatic definition descriptor initializer=>exact StaticGlobalAllocInfo.alloc_info machine id source definition absent noFunction noVaList descriptor
  have afterGhost : (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) result.machine id ⟨none,#[]⟩).user.payload.ghost=true := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
    rfl
  have frameBorrow : frame.extra.borrowTracker=some ({} : FrameState) := by
    change root.frame.extra.borrowTracker=some ({} : FrameState)
    exact RootEntryFrame.raw_borrow _ _ _ input.tracker input.runtime.enabled
  have live : (frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [frame,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached : (frame.locals[1]'((firstLive root).valid i1)).layout=some reference := by
    simp only [frame,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,firstCache,
      RootFrameData.cache,LocalOperands.cachedLayoutFrame,atSpan,i1]
  have dynamicPositive : 0<options.place.dynamicFuel := by have room:=input.resources.dynamicFuel;unfold DuplicatePrefixCallSpecification.work at room;omega
  have validationPositive : 0<options.limits.validation := by have room:=input.resources.configuredFuel.2.2.2;unfold DuplicatePrefixCallSpecification.work at room;omega
  have copy:=CurrentCallEmptyMaterializedWildcardCopy.wildcard options limits remaining span ctx actualPointers input.model.debugOff
    input.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1) (by omega) (by omega)
    #[] frame machine 1 ((firstLive root).valid i1) .uninit live cached (firstLive root).noClocks input.model.ghostOff input.model.shallow
    {} frameBorrow input.tracker.global (by rfl) (fresh input) id rootTag base offset nonnull cachedBase distinct
    _ info rfl nonstrict geometry exposed allocLive result.converted
    (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) result.machine id ⟨none,#[]⟩) afterGhost
    input.model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ input.model.metadata input.cacheOrigins)
    (LocalPlaces.localRuntimePlace 0 frame 1 reference).stackView rfl ensure
  refine ⟨rest,externStatic,finalAddresses,finalTape,result,_,wiring,head,copy,?_⟩
  simp only [CurrentCallEmptyProtocolControl.sourceRoot,ConcreteEmptyReferenceArgumentCopy.copiedFrame,
    registeredFrame,TypedRetagEntry.frameWithBorrow,frame,RootFrameData.write,firstLive,firstCache,
    RootFrameData.live,RootFrameData.cache,atSpan,LocalOperands.cachedLayoutFrame,Array.set_set,Array.getElem_set_self,i1]
  rfl
end
end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentCopy
