import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentState
import duplicate_prefix.CurrentCallOrdinaryReturnLive
import duplicate_prefix.CurrentCallOrdinaryEmptyQuietFinish
import duplicate_prefix.CurrentCallLiveBoolTransport
import duplicate_prefix.CurrentCallEmptyNonliveResources
import duplicate_prefix.CurrentCallConversionBoolPhase
import duplicate_prefix.CurrentCallConversionBoolModel
import duplicate_prefix.CurrentCallSelectedBorrowTagOrigin
import duplicate_prefix.CurrentCallConversionEntryFrame
import duplicate_prefix.CurrentCallBoolRetagBudget

namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentLive
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallOrdinaryInput CurrentCallSpatialCover CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
open Lean Elab Term in
elab "empty_current_live_rule " suffix:str : term => do
  let found:=(←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected unique checked empty CURRENT/LIVE helper {suffix.getString}"

private theorem repack {post : RootState} {frames : Array CompilerFrameContext.ActualFrame}
    {frame : CompilerFrameContext.ActualFrame} {machine : Before}
    (stack : post.stack=(Storage.withCurrent frames frame machine).stack) :
    post=Storage.withCurrent frames frame post.machine := by
  cases post with
  | mk actual machine=>change actual=_ at stack;cases stack;rfl

section
variable {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (pointer : Pointer Provenance) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (tail : List AllocId) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic
      (CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
      (CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input) tail (addressCharge before) 15 finalAddresses finalTape)
    (tree : BorrowTree)

private theorem live_data (initial : CurrentCallOrdinaryReturnLive.Packet input)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (frame : CompilerFrameContext.ActualFrame)
    (frameBorrow : frame.extra.borrowTracker=some (({} : FrameState).addProtector id input.tracker.global.nextPointerTag)) :
    let machine:=CurrentCallOrdinaryEmptyCurrentState.closed options result.machine id root result.converted tree result.global input.tracker.retagMode
    let tracker : MachineHooks.BorrowState:=⟨result.global,input.tracker.retagMode⟩
    ∃D : CurrentCallConversionBoolPhase.LiveData machine tracker frame (({} : FrameState).addProtector id input.tracker.global.nextPointerTag) place,
      D.window.allocation=initial.B.allocation ∧D.physical.id=initial.physical.id ∧D.physical.offset=initial.physical.offset := by
  intro machine tracker
  have different : initial.physical.id≠id := by
    intro same
    have live:=initial.physical.live
    rw [same,absent] at live
    cases live
  have fresh : input.tracker.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have room:=input.resources.tagRoom
    change input.tracker.global.nextPointerTag.value.toNat<18446744073709551615
    omega
  let phase:=(CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
  obtain ⟨Q,qPointer,qAllocation,qPrecise,qRuntime⟩:=CurrentCallEmptyNonliveResources.registered initial.B initial.runtime {} id fresh phase rfl
  let P : CandidateCurrentBoolUninitWrite.PhysicalWindow phase place:={initial.physical with live:=initial.physical.live,cachedBase:=initial.physical.cachedBase}
  have binding : CandidateCallBindings.WindowBinding phase P.pointer P.id P.offset.toNat 1 := by
    change CandidateCallBindings.WindowBinding phase initial.physical.pointer initial.physical.id initial.physical.offset.toNat 1
    unfold CandidateCallBindings.WindowBinding
    change CandidateCallBindings.WindowBinding before initial.physical.pointer initial.physical.id initial.physical.offset.toNat 1
    exact initial.binding
  have ready : CurrentCallBoolProtection.WindowReady phase P.id P.offset.toNat 1 := by
    change CurrentCallBoolProtection.WindowReady before initial.physical.id initial.physical.offset.toNat 1
    exact initial.ready
  have postLive : machine.memory.live.find? (fun row=>row.1==initial.physical.id)=some (initial.physical.id,initial.physical.entry) :=
    (CurrentCallOrdinaryEmptyCurrentState.live_other input id pointer root source externStatic tail finalAddresses finalTape result tree initial.physical.id different).trans initial.physical.live
  have postBase : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==initial.physical.id)=some ⟨initial.physical.id,initial.physical.base⟩ := by
    rw [CurrentCallOrdinaryEmptyCurrentState.addresses]
    exact result.bases _ _ initial.physical.cachedBase
  have wild : CurrentCallLiveBoolTransport.WildcardQuery machine P := by
    intro wildcard
    obtain ⟨entry,base,live,cached,storage,room,bounds,address,nonnull,provenance⟩:=initial.binding
    have entryEq : entry=initial.physical.entry:=congrArg Prod.snd (Option.some.inj (live.symm.trans initial.physical.live))
    have baseEq : base=initial.physical.base:=congrArg (fun row : AllocAddresses.BaseAddressEntry=>row.address)
      (Option.some.inj (cached.symm.trans initial.physical.cachedBase))
    subst entry
    subst base
    change initial.physical.pointer.provenance=.wildcard at wildcard
    rw [wildcard] at provenance
    change machine.user.addresses.provenanceMode≠.strict ∧machine.user.addresses.exposed.contains initial.physical.id=true ∧
      WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap initial.physical.pointer.offset.bytes initial.physical.base initial.physical.id initial.physical.entry.allocation.byteSize
    rw [CurrentCallOrdinaryEmptyCurrentState.addresses]
    refine ⟨?_,?_,?_⟩
    · rw [result.provenanceMode];exact provenance.1
    · rw [result.exposed];exact provenance.2.1
    · apply result.geometry _ _ _ _ ?_ provenance.2.2
      apply CurrentCallConversionBoolQueryFrame.size_of_info (info:=⟨initial.physical.entry.allocation.byteSize,initial.physical.entry.allocation.align,.liveData,initial.physical.entry.allocation.mutability⟩)
      · change before.memory.getAllocInfo initial.physical.id=_
        simp only [MemoryState.getAllocInfo,initial.physical.live]
        rfl
      · rfl
  obtain ⟨T⟩:=CurrentCallLiveBoolTransport.transport Q qRuntime P rfl rfl (initial.allocation.trans qAllocation.symm) binding ready machine tracker
    (by change machine.memory.live.find? (fun row=>row.1==initial.physical.id)=_;exact postLive.trans initial.physical.live.symm)
    result.flags result.counter (by intro tag cached;exact result.roots _ _ cached)
    (by exact postBase.trans initial.physical.cachedBase.symm)
    (CurrentCallOrdinaryEmptyCurrentState.extras_other input id pointer root source externStatic tail finalAddresses finalTape result tree _ different) wild
  let physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place:={initial.physical with live:=postLive,cachedBase:=postBase}
  have currentBinding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1 := by
    have b:=T.binding
    rw [T.physicalPointer,T.physicalId,T.physicalOffset] at b
    exact b
  have currentReady : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1 := by
    have ready:=T.ready
    rw [T.physicalId,T.physicalOffset] at ready
    exact ready
  let D : CurrentCallConversionBoolPhase.LiveData machine tracker frame (({} : FrameState).addProtector id input.tracker.global.nextPointerTag) place := {
    data:=initial.data,owner:=0,physical:=physical,window:=T.window,enabled:=rfl,frameBorrow:=frameBorrow,
    pointer:=by rw [T.pointer,qPointer];exact initial.pointer,
    allocation:=by rw [T.allocation,qAllocation];exact initial.allocation,
    runtime:=T.runtime,binding:=currentBinding,
    distinct:=by rw [T.allocation,qAllocation];exact initial.distinct,
    fresh:=CurrentCallOrdinaryEmptyCurrentState.fresh input id pointer source externStatic tail finalAddresses finalTape result,
    short:=by rw [T.allocation,qAllocation];exact initial.nodeRoom,
    ghost:=rfl,race:=(CurrentCallOrdinaryEmptyCurrentState.model input id pointer root source externStatic tail finalAddresses finalTape result tree).noDataRace,
    backend:=(CurrentCallOrdinaryEmptyCurrentState.model input id pointer root source externStatic tail finalAddresses finalTape result tree).noBackend,
    ready:=currentReady}
  exact ⟨D,T.allocation.trans qAllocation,rfl,rfl⟩

private theorem finish_result (initial : CurrentCallOrdinaryReturnLive.Packet input)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (base offset count : UInt64) (nonnull : base+offset≠0)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree result.global)
    (sourceLeaf : CurrentCallEmptyEntrySourceData.Leaf tree input.tracker.global.nextPointerTag)
    (growth : tree.nodes.size≤2) :
    let rootFrame:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let inputValue:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 reference).imm
    let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
    let sourceFrame:=({} : FrameState).addProtector id input.tracker.global.nextPointerTag
    let sourceFn:=CurrentCallOrdinaryEmptyCurrentState.closed options result.machine id root result.converted tree result.global .FnEntry
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate inputValue,reference⟩ (LocalPlaces.localRuntimePlace 0 (firstLive rootFrame).frame 1 reference).stackView
      (Storage.withCurrent #[] (firstLive rootFrame).frame (ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry))=
      .ok () (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.sourceRoot rootFrame updated sourceFrame).frame sourceFn)→
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  intro rootFrame inputValue updated sourceFrame sourceFn copy
  let machine:=CurrentCallOrdinaryEmptyCurrentState.closed options result.machine id root result.converted tree result.global input.tracker.retagMode
  let tracker : MachineHooks.BorrowState:=⟨result.global,input.tracker.retagMode⟩
  have sourceModel:=CurrentCallOrdinaryEmptyCurrentState.model input id pointer root source externStatic tail finalAddresses finalTape result tree
  have sourceOrigins:=CurrentCallOrdinaryEmptyCurrentState.origins input id pointer root source externStatic tail finalAddresses finalTape result tree
  have sourceThreads:=CurrentCallOrdinaryEmptyCurrentState.threads input id pointer root source externStatic tail finalAddresses finalTape result tree
  have raw : rootFrame.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have dynamicEq : options.place.dynamicFuel=(options.place.dynamicFuel-1)+1 := by have p:=initial.dynamicPositive;omega
  have validationEq : options.limits.validation=(options.limits.validation-1)+1 := by have p:=initial.validationPositive;omega
  have dispatchEq : limits.callDispatch=(limits.callDispatch-1)+1 := by have p:=initial.dispatchPositive;omega
  have args:=CurrentCallEmptyProtocolControl.arguments options limits remaining span input.model.debugOff (options.limits.validation-1) validationEq #[] rootFrame raw
    (CurrentCallPush.preparedMachine before #[]) sourceFn input.tracker ⟨result.global,.FnEntry⟩ input.runtime.enabled rfl input.model.ghostOff input.model.shallow
    (by exact sourceModel.ghostOff) (by exact sourceModel.shallow) inputValue updated sourceFrame count copy
  let boolFrame:=(atSpan (RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot rootFrame updated sourceFrame) count) ⟨601⟩).frame
  obtain ⟨D,allocation,idEq,offsetEq⟩:=live_data input id pointer root source externStatic tail finalAddresses finalTape result tree initial absent boolFrame rfl
  obtain ⟨ctx⟩:=ActualRetagContext.exists_context options (remaining+1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨O⟩:=CurrentCallConversionBoolPhase.live ctx D #[]
  have postEq:=repack O.stack
  have protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent #[] boolFrame machine)=.ok () (Storage.withCurrent #[]
      (registeredFrame boolFrame sourceFrame D.physical.id tracker.global.nextPointerTag) O.post.machine) := by
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place _=_
    rw [←postEq]
    have actual:=O.actual
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag options.limits.retag place _=_ at actual
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining+1) span ctx place input.returnLayout options.limits.retag limits.retag) _).symm.trans actual
  have entered:=CurrentCallEmptyProtocolControl.init_of_arguments options limits remaining span before #[] place input.model.noDataRace input.model.debugOff input.stackReady
    inputValue updated sourceFrame count machine O.post.machine D.physical.id tracker.global.nextPointerTag args protection
  let R:=O.output
  let next : MachineHooks.BorrowState:=⟨O.operation.global,input.tracker.retagMode⟩
  have model:=CurrentCallConversionBoolModel.live_model O sourceModel
  have origins:=CurrentCallConversionBoolModel.live_origins O sourceOrigins
  have threads:= (CurrentCallConversionBoolModel.live_threads O).trans sourceThreads
  have different : id≠D.physical.id := by
    rw [idEq]
    intro same
    have found:=initial.physical.live
    rw [←same,absent] at found
    cases found
  let sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨.machine .global,result.converted.mapExtra (fun _=>tree)⟩
  have oldSourceLive : machine.memory.live.find? (fun row=>row.1==id)=some (id,sourceEntry):=
    CurrentCallOrdinaryEmptyCurrentState.live input id pointer root source externStatic tail finalAddresses finalTape result tree
  have sourceLive : O.post.machine.memory.live.find? (fun row=>row.1==id)=some (id,sourceEntry) := by
    have frame:=CurrentCallConversionEntryFrame.live #[] boolFrame sourceFrame D.fresh D.physical.id D.physical.entry O.operation.child.tree
      O.output.window.allocation O.post.machine O.machineEq id
    simp only [different,↓reduceIte] at frame
    exact frame.trans oldSourceLive
  obtain ⟨_,_,_,registeredRuntime,_,_⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global sourceFrame D.physical.id D.fresh sourceRuntime
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree O.operation.global := by rw [O.global];exact registeredRuntime
  have beforeFresh : input.tracker.global.nextPointerTag.value.toNat<tracker.global.nextPointerTag.value.toNat := by
    have advance:=CurrentCallOrdinaryEmptyCurrentState.advanced input id pointer source externStatic tail finalAddresses finalTape result
    change input.tracker.global.nextPointerTag.value.toNat<result.global.nextPointerTag.value.toNat
    omega
  have bounds : D.physical.offset.toNat+1≤D.window.allocation.extra.locations.size.bytes.toNat := by
    have first:=(D.window.window (D.physical.id,D.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [D.window.issued.capability.treeExtent,←D.window.issued.capability.extent]
    omega
  have keys:=CurrentCallSelectedBorrowTagOrigin.operation D.window D.runtime sourceFrame D.fresh rfl D.distinct (by have h:=D.short;omega)
    (by have h:=D.short;omega) D.physical.offset 1 rfl rfl (by decide) bounds O.operation O.raw
  have hiddenOnBool : ∀index node,R.window.allocation.extra.nodes.get index=some node→node.tag=input.tracker.global.nextPointerTag→node.isExposed=false := by
    intro index node found same
    have tagged:=R.runtime.formed.allocator.nodeTags index node found
    change O.output.window.allocation.extra.tagMapping.get node.tag=some index at tagged
    rw [O.tagMapping] at tagged
    obtain ⟨oldIndex,member⟩:=(empty_current_live_rule "CurrentCallSelectedBorrowTagOrigin.lookup_member") _ _ _ tagged
    rcases keys node.tag oldIndex member with fresh|old
    · rw [same] at fresh
      have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) fresh
      change input.tracker.global.nextPointerTag.value.toNat=result.global.nextPointerTag.value.toNat at equal
      have less:=beforeFresh
      change input.tracker.global.nextPointerTag.value.toNat<result.global.nextPointerTag.value.toNat at less
      exact False.elim (by omega)
    · obtain ⟨oldIndex,old⟩:=old
      rw [allocation] at old
      have below:=initial.runtime.below.mapping (node.tag,oldIndex) old
      rw [same] at below
      exact False.elim (Nat.lt_irrefl _ below)
  obtain ⟨oldThread,oldActive,_⟩:=input.stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : O.post.machine.threads.activeThread?=some thread := by
    rw [threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  have tagRoom : next.global.nextPointerTag.value.toNat+1<18446744073709551615 := by
    have room:=result.rootBudget
    change O.operation.global.nextPointerTag.value.toNat+1<18446744073709551615
    rw [O.global]
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag D.fresh).value.toNat+1<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value]
    change result.global.nextPointerTag.value.toNat+1+1<18446744073709551615
    omega
  apply CurrentCallOrdinaryEmptyQuietFinish.finish count R id input.tracker.global.nextPointerTag sourceEntry sourceLive
    (by rw [O.id];exact different) currentRuntime (by change tree.nodes.size+2≤4294967295;omega) sourceLeaf hiddenOnBool base offset nonnull
    (by rw [CurrentCallConversionBoolModel.live_addresses];exact CurrentCallOrdinaryEmptyCurrentState.base input id pointer root source externStatic tail finalAddresses finalTape result tree base cached)
    rootFrame raw rfl rfl rfl model origins O.tracked thread active rfl tagRoom
    (options.place.dynamicFuel-1) (options.limits.validation-1) (limits.callDispatch-1) dynamicEq validationEq dispatchEq
  simpa only [R,O.id,O.tag,CurrentCallEmptyProtocolControl.frame,inputValue,DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue] using entered

end

/-- CURRENT concrete empty source and initially LIVE Bool, from the adopted
input and its actual initial metadata selectors. No converter or body outcome
is a public premise; the original Result covers every count. -/
theorem concrete_raw {options limits remaining span before place}
    (id : AllocId) (rootTag : BorTag) (base offset : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0 place)
    (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (registry : InitialRegistryVacant before id)
    (cachedRoot : input.tracker.global.rootTag? id=some rootTag)
    (cachedBase : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (nonnull : base+offset≠0)
    (liveReturn : LiveRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0 count place := by
  obtain ⟨initial⟩:=CurrentCallOrdinaryReturnLive.form input liveReturn
  obtain ⟨rest,externStatic,finalAddresses,finalTape,result,afterFrame,wiring,head,copy,frameEq⟩:=
    CurrentCallOrdinaryEmptyCurrentCopy.concrete id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull
  let pointer : Pointer Provenance:=Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))
  have older:=CurrentCallOrdinaryEmptyCurrentState.cached_below input id rootTag cachedRoot
  let tree:=TypedRetagConcreteEmpty.lazyTree rootTag input.tracker.global.nextPointerTag result.converted.byteSize.bytes
  have runtime:=CurrentCallOrdinaryEmptyCurrentState.concrete_runtime input id pointer rootTag source externStatic
    (rest.flatMap CurrentCallConversionFiniteFold.targets) finalAddresses finalTape result older offset
  have different : rootTag≠input.tracker.global.nextPointerTag := by
    intro same
    have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  have leaf:=CurrentCallEmptyMaterializedSourceFacts.concrete_leaf rootTag input.tracker.global.nextPointerTag result.converted.byteSize different
  rw [frameEq] at copy
  rw [CurrentCallOrdinaryEmptyCurrentState.concrete_eq input id pointer rootTag source externStatic
    (rest.flatMap CurrentCallConversionFiniteFold.targets) finalAddresses finalTape result] at copy
  exact finish_result input id pointer rootTag source externStatic (rest.flatMap CurrentCallConversionFiniteFold.targets)
    finalAddresses finalTape result tree initial absent base offset count nonnull cachedBase runtime leaf (by change (2 : Nat)≤2;decide) copy

/-- CURRENT wildcard HIT source and initially LIVE Bool. The actual zero q
constructor is parentless, with no invented source family or byte authority. -/
theorem wildcard_raw {options limits remaining span before place}
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
    (exposed : before.user.addresses.exposed.contains id=true)
    (liveReturn : LiveRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset)))) 0 count place := by
  obtain ⟨initial⟩:=CurrentCallOrdinaryReturnLive.form input liveReturn
  obtain ⟨rest,externStatic,finalAddresses,finalTape,result,afterFrame,wiring,head,copy,frameEq⟩:=
    CurrentCallOrdinaryEmptyCurrentCopy.wildcard id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull geometry exposed
  let pointer : Pointer Provenance:=Pointer.new .wildcard (Size.ofBytes (base+offset))
  have older:=CurrentCallOrdinaryEmptyCurrentState.cached_below input id rootTag cachedRoot
  let tree:=CurrentCallEmptyMaterializedWildcard.finalTree rootTag input.tracker.global.nextPointerTag result.converted.byteSize
  have runtime:=CurrentCallOrdinaryEmptyCurrentState.wildcard_runtime input id pointer rootTag source externStatic
    (rest.flatMap CurrentCallConversionFiniteFold.targets) finalAddresses finalTape result older offset
  have different : rootTag≠input.tracker.global.nextPointerTag := by
    intro same
    have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  have rootBelow:=CurrentCallOrdinaryEmptyCurrentState.root_below input id pointer rootTag source externStatic
    (rest.flatMap CurrentCallConversionFiniteFold.targets) finalAddresses finalTape result older
  have protectors:=CurrentCallOrdinaryEmptyCurrentState.protectors input id pointer source externStatic
    (rest.flatMap CurrentCallConversionFiniteFold.targets) finalAddresses finalTape result
  have seed:=S03MaterializableRootRuntime.initial rootTag result.converted.byteSize.bytes result.global rootBelow protectors
  have leaf:=CurrentCallEmptyMaterializedSourceFacts.wildcard_leaf rootTag input.tracker.global.nextPointerTag result.converted.byteSize different
    (DuplicatePrefixBorrowContract.vacant_clean seed)
  rw [frameEq] at copy
  rw [CurrentCallOrdinaryEmptyCurrentState.wildcard_eq input id pointer rootTag source externStatic
    (rest.flatMap CurrentCallConversionFiniteFold.targets) finalAddresses finalTape result] at copy
  exact finish_result input id pointer rootTag source externStatic (rest.flatMap CurrentCallConversionFiniteFold.targets)
    finalAddresses finalTape result tree initial absent base offset count nonnull cachedBase runtime leaf (by change (2 : Nat)≤2;decide) copy

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentLive

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyCurrentLive.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary empty CURRENT/LIVE dependency {name}: {dependency}"
