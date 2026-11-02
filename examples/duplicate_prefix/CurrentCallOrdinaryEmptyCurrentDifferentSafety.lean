import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentBool
import duplicate_prefix.CurrentCallOrdinaryEmptyQuietFinish
import duplicate_prefix.CurrentCallConversionBoolModel
import duplicate_prefix.CurrentCallOrdinarySameAllocationBool
import duplicate_prefix.CurrentCallOrdinaryEmptyNonliveCurrent
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentDifferentSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallOrdinaryEmptyCurrentState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
open Lean Elab Term in
elab "empty_current_different_rule" suffix:str : term => do
  let candidates := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix.getString then some name else none
  match candidates with
  | [name] => return ← Lean.Meta.mkConstWithFreshMVarLevels name
  | _ => throwError "expected one checked declaration ending in {suffix.getString}"

private theorem finish_source {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (pointer : Pointer Provenance) (rootTag : BorTag) (base sourceOffset count : UInt64)
    (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (nonnull : base+sourceOffset≠0)
    (query : CurrentCallConversionPlan.sourceQuery before argument 0=.ok (some id))
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (different : id≠input.returnFamily.allocation)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (rest : List (Allocation CtfeProvenance Unit))
    (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic
      (CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
      (CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input) (rest.flatMap CurrentCallConversionFiniteFold.targets)
      (addressCharge before) 15 finalAddresses finalTape)
    (wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
      PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic)
    (head : CurrentCallConversionPlan.selectedPayloads before argument 0 place=source::rest)
    (tree : BorrowTree)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree result.global)
    (leaf : CurrentCallEmptyEntrySourceData.Leaf tree input.tracker.global.nextPointerTag)
    (nodeRoom : tree.nodes.size+2≤4294967295) :
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let frame:=(firstLive root).frame
    let initial:=ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry
    let value:=(DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument 0 reference).imm
    let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id input.tracker.global.nextPointerTag) (Size.ofBytes (base+sourceOffset))) 0 reference).imm
    let sourceFrame:=({} : FrameState).addProtector id input.tracker.global.nextPointerTag
    let sourceFn:=closed options result.machine id rootTag result.converted tree result.global .FnEntry
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,reference⟩ (LocalPlaces.localRuntimePlace 0 frame 1 reference).stackView
      (Storage.withCurrent #[] frame initial)=.ok ()
      (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.sourceRoot root updated sourceFrame).frame sourceFn) →
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  intro root frame initial value updated sourceFrame sourceFn copy
  let prepared:=CurrentCallPush.preparedMachine before #[]
  let sourceMachine:=closed options result.machine id rootTag result.converted tree result.global input.tracker.retagMode
  let tracker : MachineHooks.BorrowState:=⟨result.global,input.tracker.retagMode⟩
  let boolFrame:=(atSpan (RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot root updated sourceFrame) count) ⟨601⟩).frame
  have sourceModel:=model input id pointer rootTag source externStatic _ finalAddresses finalTape result tree
  have sourceOrigins:=origins input id pointer rootTag source externStatic _ finalAddresses finalTape result tree
  have sourceThreads:=threads input id pointer rootTag source externStatic _ finalAddresses finalTape result tree
  have sourceTypes:=types input id pointer rootTag source externStatic _ finalAddresses finalTape result tree
  have sourceTracked : sourceMachine.borrowTracker=some tracker:=rfl
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have workPositive : 0<DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
  let validationFuel:=options.limits.validation-1
  let dynamicFuel:=options.place.dynamicFuel-1
  let budget:=limits.callDispatch-1
  have validationEq : options.limits.validation=validationFuel+1:=by have old:=input.resources.configuredFuel.2.2.2;dsimp only[validationFuel];omega
  have dynamicEq : options.place.dynamicFuel=dynamicFuel+1:=by have old:=input.resources.dynamicFuel;dsimp only[dynamicFuel];omega
  have dispatchEq : limits.callDispatch=budget+1:=by have old:=input.resources.executionFuel.1;dsimp only[budget];omega
  have args:=CurrentCallEmptyProtocolControl.arguments options limits remaining span input.model.debugOff validationFuel validationEq #[] root raw
    prepared sourceFn input.tracker ⟨result.global,.FnEntry⟩ input.runtime.enabled rfl input.model.ghostOff input.model.shallow
    sourceModel.ghostOff sourceModel.shallow value updated sourceFrame count copy
  obtain ⟨D,dFamily,dOffset,dCurrent⟩:=CurrentCallOrdinaryEmptyCurrentBool.current_data input id pointer rootTag source externStatic _ finalAddresses finalTape result tree
    latent (Ne.symm different) boolFrame sourceFrame rfl
  have sourcePayload:=CurrentCallConversionPlanAdequacy.payload_of_current before id source absent noFunction noVaList current
  have returnPayload:=CurrentCallConversionPlanAdequacy.payload_of_current before input.returnFamily.allocation D.source latent.1 latent.2.1 latent.2.2.1 dCurrent
  have returnQuery:=CurrentCallConversionPlanAdequacy.return_query options limits remaining span before argument 0 place input
  have headBoth : CurrentCallConversionPlan.selectedPayloads before argument 0 place=source::D.source::[] := by
    unfold CurrentCallConversionPlan.selectedPayloads
    rw [CurrentCallConversionPlan.selected_of_queries before argument 0 place _ _ query returnQuery,
      CurrentCallConversionPlan.distinct_ids before id input.returnFamily.allocation source D.source different sourcePayload returnPayload]
    rfl
  have restEq : rest=[D.source]:=(List.cons.inj (head.symm.trans headBoth)).2
  obtain ⟨P,reserveEq⟩:=CurrentCallOrdinaryEmptyCurrentBool.next_phase input id pointer rootTag source externStatic _ finalAddresses finalTape result tree
    boolFrame sourceFrame D current absent noFunction noVaList base cached D.source rfl [] headBoth
    (by simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using congrArg (List.flatMap CurrentCallConversionFiniteFold.targets) restEq) wiring
  obtain ⟨retagCtx⟩:=ActualRetagContext.exists_context options (remaining+1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨boolResult,⟨O⟩⟩:=CurrentCallConversionBoolPhase.next input retagCtx D P
  have postEq:=(empty_current_different_rule "CurrentCallOrdinaryEmptyNonliveCurrent.repack") O.stack
  have protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent #[] boolFrame sourceMachine)=.ok ()
      (Storage.withCurrent #[] (registeredFrame boolFrame sourceFrame D.family.allocation tracker.global.nextPointerTag) O.post.machine) := by
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place _=_
    rw [←postEq]
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining+1) span retagCtx place input.returnLayout options.limits.retag limits.retag) _).symm.trans O.actual
  have entered:=CurrentCallEmptyProtocolControl.init_of_arguments options limits remaining span before #[] place input.model.noDataRace input.model.debugOff input.stackReady
    value updated sourceFrame count sourceMachine O.post.machine D.family.allocation tracker.global.nextPointerTag args protection
  let R:=O.output
  have postModel:=CurrentCallConversionBoolModel.model O sourceModel
  have postOrigins:=CurrentCallConversionBoolModel.origins O sourceOrigins
  have postThreads:=(CurrentCallConversionBoolModel.threads O).trans sourceThreads
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨.machine .global,result.converted.mapExtra (fun _=>tree)⟩
  have sourceLive : sourceMachine.memory.live.find? (fun row=>row.1==id)=some (id,entry):=live input id pointer rootTag source externStatic _ finalAddresses finalTape result tree
  have differentB : id≠D.family.allocation:=by rw[dFamily];exact different
  have postLive : O.post.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry):=by
    rw[CurrentCallConversionBoolModel.memory_other O id differentB];exact sourceLive
  obtain ⟨_,_,_,registeredRuntime,_,_⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global sourceFrame D.family.allocation D.fresh runtime
  have postRuntime:=CurrentCallZeroSharedBoolWindow.runtime_mono tree D.next.global boolResult.global registeredRuntime boolResult.flags boolResult.counter
  have rootHit:=boolResult.roots _ _ D.rootCached
  have initialRoot : input.tracker.global.rootTag? D.family.allocation=some D.root := by
    obtain ⟨tag,_,cachedRoot⟩:=latent.2.2.2.2.1
    have kept:=result.roots _ _ cachedRoot
    have sameCache : result.global.rootTag? D.family.allocation=some tag := by rw[dFamily];exact kept
    have equal : D.root=tag:=Option.some.inj (D.rootCached.symm.trans sameCache)
    simpa only[dFamily,equal] using cachedRoot
  have rootOldInitial : D.root.value.toNat<input.tracker.global.nextPointerTag.value.toNat:=by
    have old:=(empty_current_different_rule "CurrentCallOrdinaryEmptyNonliveCurrent.cached_below") input D.family.allocation D.root initialRoot
    exact old
  have postHidden : ∀index node,R.window.allocation.extra.nodes.get index=some node→node.tag=input.tracker.global.nextPointerTag→node.isExposed=false := by
    have absentTag:=(empty_current_different_rule "CurrentCallOrdinaryEmptyNonliveCurrent.two_nodes_absent") R input.tracker.global.nextPointerTag O.nodes (by
      intro node found
      obtain ⟨rootNode,rootAt,_,_,cachedRoot⟩:=R.window.issued.capability.rootNode
      have equal : node=rootNode:=Option.some.inj (found.symm.trans rootAt)
      rw[O.id] at cachedRoot
      have tagEq : rootNode.tag=D.root:=Option.some.inj (cachedRoot.symm.trans rootHit)
      rw[equal,tagEq]
      exact rootOldInitial) (by
        rw[O.tag]
        have advance:=advanced input id pointer source externStatic _ finalAddresses finalTape result
        change input.tracker.global.nextPointerTag.value.toNat<result.global.nextPointerTag.value.toNat
        omega)
    intro index node found equal
    exact False.elim (absentTag index node found equal)
  obtain ⟨oldThread,oldActive,_⟩:=input.stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : O.post.machine.threads.activeThread?=some thread:=by
    rw[postThreads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  have currentBase : O.post.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩:=
    CurrentCallConversionBoolModel.base_hit O id ⟨id,base⟩ (CurrentCallOrdinaryEmptyCurrentState.base input id pointer rootTag source externStatic _ finalAddresses finalTape result tree base cached)
  apply CurrentCallOrdinaryEmptyQuietFinish.finish count R id input.tracker.global.nextPointerTag entry postLive
    (by rw[O.id];exact differentB) postRuntime nodeRoom leaf postHidden base sourceOffset nonnull currentBase root raw rfl rfl rfl
    postModel postOrigins O.tracked thread active rfl
    (by have room:=boolResult.rootBudget;have reserved:=reserveEq;change boolResult.global.nextPointerTag.value.toNat+1<18446744073709551615;omega)
    dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
  simpa only[R,O.id,O.tag,CurrentCallEmptyProtocolControl.frame,root,tracker,value,DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue] using entered

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
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (different : id≠input.returnFamily.allocation) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0 count place := by
  obtain ⟨rest,externStatic,finalAddresses,finalTape,result,afterFrame,wiring,head,copy,frameEq⟩:=
    CurrentCallOrdinaryEmptyCurrentCopy.concrete id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull
  have older : rootTag.value.toNat<input.tracker.global.nextPointerTag.value.toNat :=
    (empty_current_different_rule "CurrentCallOrdinaryEmptyNonliveCurrent.cached_below") input id rootTag cachedRoot
  have distinct : rootTag≠input.tracker.global.nextPointerTag := by
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  let tree:=TypedRetagConcreteEmpty.lazyTree rootTag input.tracker.global.nextPointerTag result.converted.byteSize.bytes
  have runtime:=CurrentCallOrdinaryEmptyCurrentState.concrete_runtime input id (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result older offset
  have leaf:=CurrentCallEmptyMaterializedSourceFacts.concrete_leaf rootTag input.tracker.global.nextPointerTag result.converted.byteSize distinct
  have query:=CurrentCallConversionPlanAdequacy.query_concrete before (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) 0 id rootTag base rfl cachedBase
  apply finish_source input id (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) rootTag base offset count source current absent noFunction noVaList cachedBase nonnull query latent different externStatic rest finalAddresses finalTape result wiring head tree runtime leaf (by change 2+2≤4294967295;decide)
  rw[frameEq] at copy
  rw[CurrentCallOrdinaryEmptyCurrentState.concrete_eq input id (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result] at copy
  simpa only[tree,DuplicatePrefixSliceArgument.rawValue] using copy

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
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (different : id≠input.returnFamily.allocation) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset)))) 0 count place := by
  obtain ⟨rest,externStatic,finalAddresses,finalTape,result,afterFrame,wiring,head,copy,frameEq⟩:=
    CurrentCallOrdinaryEmptyCurrentCopy.wildcard id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull geometry exposed
  have older : rootTag.value.toNat<input.tracker.global.nextPointerTag.value.toNat :=
    (empty_current_different_rule "CurrentCallOrdinaryEmptyNonliveCurrent.cached_below") input id rootTag cachedRoot
  have distinct : rootTag≠input.tracker.global.nextPointerTag := by
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  let tree:=CurrentCallEmptyMaterializedWildcard.finalTree rootTag input.tracker.global.nextPointerTag result.converted.byteSize
  have runtime:=CurrentCallOrdinaryEmptyCurrentState.wildcard_runtime input id (Pointer.new .wildcard (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result older offset
  have leaf:=CurrentCallEmptyMaterializedSourceFacts.wildcard_leaf rootTag input.tracker.global.nextPointerTag result.converted.byteSize distinct (GeneralBorrowGcVacantClean.initial rootTag result.converted.byteSize)
  have physical : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset))))) := by
    rcases input.source with empty|positive
    · exact empty.2.1
    · exact (positive.1 rfl).elim
  have initialInfo : before.memory.getAllocInfo id=.ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩ := by
    cases current with
    | memory descriptor=>exact GlobalDataOnlyMaterialize.alloc_info before id source absent noFunction noVaList descriptor
    | internalStatic definition descriptor initializer=>exact StaticGlobalAllocInfo.alloc_info before id source definition absent noFunction noVaList descriptor
  have query := CurrentCallConversionPlanAdequacy.query_wildcard before (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 id base ⟨source.byteSize,source.align,.liveData,source.mutability⟩ rfl (by decide) geometry physical.2.1 exposed cachedBase initialInfo (physical.2.2.1.live.2 id (Array.contains_iff_mem.mp exposed))
  apply finish_source input id (Pointer.new .wildcard (Size.ofBytes (base+offset))) rootTag base offset count source current absent noFunction noVaList cachedBase nonnull query latent different externStatic rest finalAddresses finalTape result wiring head tree runtime leaf (by change 2+2≤4294967295;decide)
  rw[frameEq] at copy
  rw[CurrentCallOrdinaryEmptyCurrentState.wildcard_eq input id (Pointer.new .wildcard (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result] at copy
  simpa only[tree,DuplicatePrefixSliceArgument.rawValue] using copy

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentDifferentSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyCurrentDifferentSafety.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty CURRENT different-allocation dependency {name}: {dependency}"
