import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentSameBool
import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentArguments
import duplicate_prefix.CurrentCallEmptyLiveBoolQuiet
import duplicate_prefix.CurrentCallOrdinaryEmptySameQuietFinish
import duplicate_prefix.CurrentCallConversionBoolModel
import duplicate_prefix.CurrentCallBoolRetagBudget
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentSameSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallOrdinaryInput
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallOrdinaryEmptyCurrentState CurrentCallOrdinaryEmptyCurrentSameBool
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
private theorem repack {post : RootState} {frames : Array CompilerFrameContext.ActualFrame}
    {frame : CompilerFrameContext.ActualFrame} {machine : Before}
    (stackEq : post.stack=(Storage.withCurrent frames frame machine).stack) :
    post=Storage.withCurrent frames frame post.machine := by
  cases post with
  | mk stackMachine machine=>change stackMachine=_ at stackEq;cases stackEq;rfl

variable {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {argument : DuplicatePrefixSliceArgument.Argument}
    {place : MPlaceTy Provenance}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (pointer : Pointer Provenance) (root : BorTag)
    (source : Allocation CtfeProvenance Unit)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (tail : List AllocId) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic
      (CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
      (CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input) tail (addressCharge before) 15 finalAddresses finalTape)
    (tree : BorrowTree)

theorem finish_source
    (argumentPointer : argument=.pointer pointer)
    (same : id=input.returnFamily.allocation)
    (base offset count : UInt64) (nonnull : base+offset≠0)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (cachedRoot : input.tracker.global.rootTag? id=some root)
    (older : root.value.toNat<input.tracker.global.nextPointerTag.value.toNat)
    (P : CurrentCallMaterializedRootBoolFrame.Packet
      (closed options result.machine id root result.converted tree result.global input.tracker.retagMode)
      ⟨result.global,input.tracker.retagMode⟩ input.returnFamily result.converted tree input.returnOffset place)
    (leaf : CurrentCallEmptyEntrySourceData.Leaf tree input.tracker.global.nextPointerTag)
    (nodes : tree.nodes.size=2) :
    let rootFrame:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let rawValue:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 reference).imm
    let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
    let sourceFrame:=({} : FrameState).addProtector id input.tracker.global.nextPointerTag
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate rawValue,reference⟩ (LocalPlaces.localRuntimePlace 0 (firstLive rootFrame).frame 1 reference).stackView
      (Storage.withCurrent #[] (firstLive rootFrame).frame (ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry))=
      .ok () (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.sourceRoot rootFrame updated sourceFrame).frame
        (closed options result.machine id root result.converted tree result.global .FnEntry))→
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  intro rootFrame rawValue updated sourceFrame copy
  let post:=closed options result.machine id root result.converted tree result.global input.tracker.retagMode
  let boolFrame:=(atSpan (RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot rootFrame updated sourceFrame) count) ⟨601⟩).frame
  have sourceModel:=model input id pointer root source externStatic tail finalAddresses finalTape result tree
  let D:=live_data P boolFrame sourceFrame sourceModel rfl rfl
    (fresh input id pointer source externStatic tail finalAddresses finalTape result) (by rw [nodes];decide)
  have args:=CurrentCallOrdinaryEmptyCurrentArguments.arguments input id pointer root source externStatic tail finalAddresses finalTape result tree updated count copy
  obtain ⟨ctx⟩:=ActualRetagContext.exists_context options (remaining+1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨O⟩:=CurrentCallConversionBoolPhase.live ctx D #[]
  have stack : O.post=Storage.withCurrent #[] (registeredFrame boolFrame sourceFrame D.physical.id result.global.nextPointerTag) O.post.machine := by
    exact repack O.stack
  have protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent #[] boolFrame post)=.ok ()
      (Storage.withCurrent #[] (registeredFrame boolFrame sourceFrame D.physical.id result.global.nextPointerTag) O.post.machine) := by
    rw [←stack]
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place _=_
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining+1) span ctx place input.returnLayout options.limits.retag limits.retag) _).symm.trans O.actual
  have entered:=CurrentCallEmptyProtocolControl.init_of_arguments options limits remaining span before #[] place input.model.noDataRace input.model.debugOff input.stackReady
    rawValue updated sourceFrame count post O.post.machine D.physical.id result.global.nextPointerTag args protection
  have currentModel:=CurrentCallConversionBoolModel.live_model O sourceModel
  have currentOrigins:=CurrentCallConversionBoolModel.live_origins O (origins input id pointer root source externStatic tail finalAddresses finalTape result tree)
  have currentThreads : O.post.machine.threads=(CurrentCallPush.preparedMachine before #[]).threads:=
    (CurrentCallConversionBoolModel.live_threads O).trans (threads input id pointer root source externStatic tail finalAddresses finalTape result tree)
  obtain ⟨query,qnode,qtagged,qAt,qTag,qChildren,qHidden,qInactive⟩:=leaf
  have qPresent : D.window.allocation.extra.nodes.get query=some qnode := by
    change P.window.allocation.extra.nodes.get query=some qnode;rw [P.allocation];exact qAt
  have qInactive' : GeneralRangeMapState.Every (fun row=>(GeneralBorrowWildcardVirtualLeaf.effective row query qnode).accessed=false) D.window.allocation.extra.locations := by
    change GeneralRangeMapState.Every _ P.window.allocation.extra.locations;rw [P.allocation];exact qInactive
  have different : query≠D.window.pointer.grant := by
    change query≠P.window.pointer.grant
    rw [P.pointer]
    change query≠allocationRoot
    intro equal
    obtain ⟨rnode,rootAt,_,_,rootCached⟩:=P.window.issued.capability.rootNode
    have rootHere : result.global.rootTag? input.returnFamily.allocation=some root := by
      rw [←same];exact result.roots _ _ cachedRoot
    have rootTag : rnode.tag=root:=Option.some.inj (rootCached.symm.trans rootHere)
    have qAt' : P.window.allocation.extra.nodes.get allocationRoot=some qnode := by
      rw [P.allocation];change tree.nodes.get allocationRoot=some qnode;simpa only [equal,BorrowTree.nodeAt] using qAt
    have nodeEq : qnode=rnode:=Option.some.inj (qAt'.symm.trans rootAt)
    have tagEq : input.tracker.global.nextPointerTag=root:=qTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans rootTag)
    have eq:=congrArg (fun tag : BorTag=>tag.value.toNat) tagEq
    omega
  have afterLeaf:=CurrentCallEmptyLiveBoolQuiet.retain D O query qnode input.tracker.global.nextPointerTag qPresent qTag qChildren qHidden different qInactive'
  have physicalId : D.physical.id=id:=P.physicalId.trans same.symm
  have retId : O.output.id=id:=O.id.trans physicalId
  have currentBase : O.post.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==O.output.id)=some ⟨O.output.id,base⟩ := by
    rw [retId,CurrentCallConversionBoolModel.live_addresses O]
    exact CurrentCallOrdinaryEmptyCurrentState.base input id pointer root source externStatic tail finalAddresses finalTape result tree base cached
  obtain ⟨oldThread,oldActive,_⟩:=input.stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : O.post.machine.threads.activeThread?=some thread := by
    rw [currentThreads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  have room : O.output.window.allocation.extra.nodes.size+2<65536 := by
    have bound:=O.nodes
    change O.output.window.allocation.extra.nodes.size≤P.window.allocation.extra.nodes.size+1 at bound
    rw [P.allocation] at bound
    change O.output.window.allocation.extra.nodes.size≤tree.nodes.size+1 at bound
    omega
  have qOlder : input.tracker.global.nextPointerTag.value.toNat<O.output.node.tag.value.toNat := by
    rw [O.tag]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (advanced input id pointer source externStatic tail finalAddresses finalTape result)
  have tagRoom : O.operation.global.nextPointerTag.value.toNat+1<18446744073709551615 := by
    have budget:=result.rootBudget
    rw [O.global]
    change (TypedRetagEmpty.successorTag result.global.nextPointerTag D.fresh).value.toNat+1<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have workPositive : 0<DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
  let dynamicFuel:=options.place.dynamicFuel-1
  let validationFuel:=options.limits.validation-1
  let budget:=limits.callDispatch-1
  have dynamicEq : options.place.dynamicFuel=dynamicFuel+1 := by have fuel:=input.resources.dynamicFuel;dsimp only [dynamicFuel];omega
  have validationEq : options.limits.validation=validationFuel+1 := by have fuel:=input.resources.configuredFuel.2.2.2;dsimp only [validationFuel];omega
  have dispatchEq : limits.callDispatch=budget+1 := by have fuel:=input.resources.executionFuel.1;dsimp only [budget];omega
  apply CurrentCallOrdinaryEmptySameQuietFinish.finish count O.output input.tracker.global.nextPointerTag room afterLeaf qOlder base offset nonnull currentBase rootFrame
    (RootEntryFrame.raw_locals _ _ _) rfl rfl rfl currentModel currentOrigins O.tracked thread active rfl tagRoom
    dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
  simpa only [retId,physicalId,O.tag,rootFrame,CurrentCallEmptyProtocolControl.frame,argumentPointer,DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,rawValue,updated,sourceFrame] using entered


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
    (same : id=input.returnFamily.allocation) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset)))) 0 count place := by
  obtain ⟨rest,externStatic,finalAddresses,finalTape,result,afterFrame,wiring,head,copy,frameEq⟩:=
    CurrentCallOrdinaryEmptyCurrentCopy.concrete id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull
  have older : rootTag.value.toNat<input.tracker.global.nextPointerTag.value.toNat :=
    CurrentCallOrdinaryEmptyCurrentState.cached_below input id rootTag cachedRoot
  have distinct : rootTag≠input.tracker.global.nextPointerTag := by
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  let tree:=TypedRetagConcreteEmpty.lazyTree rootTag input.tracker.global.nextPointerTag result.converted.byteSize.bytes
  have leaf:=CurrentCallEmptyMaterializedSourceFacts.concrete_leaf rootTag input.tracker.global.nextPointerTag result.converted.byteSize distinct
  obtain ⟨P⟩:=CurrentCallOrdinaryEmptyCurrentSameBool.concrete input id (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result same latent current cachedRoot base offset cachedBase older
  apply finish_source input id (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result tree rfl same base offset count nonnull cachedBase cachedRoot older P leaf (by change (2 : Nat)=2;rfl)
  rw [frameEq] at copy
  rw [CurrentCallOrdinaryEmptyCurrentState.concrete_eq input id (Pointer.new (.concrete id rootTag) (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result] at copy
  exact copy

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
    (same : id=input.returnFamily.allocation) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+offset)))) 0 count place := by
  obtain ⟨rest,externStatic,finalAddresses,finalTape,result,afterFrame,wiring,head,copy,frameEq⟩:=
    CurrentCallOrdinaryEmptyCurrentCopy.wildcard id rootTag base offset input source current absent noFunction noVaList registry cachedRoot cachedBase nonnull geometry exposed
  have older : rootTag.value.toNat<input.tracker.global.nextPointerTag.value.toNat :=
    CurrentCallOrdinaryEmptyCurrentState.cached_below input id rootTag cachedRoot
  have distinct : rootTag≠input.tracker.global.nextPointerTag := by
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  let tree:=CurrentCallEmptyMaterializedWildcard.finalTree rootTag input.tracker.global.nextPointerTag result.converted.byteSize
  have leaf:=CurrentCallEmptyMaterializedSourceFacts.wildcard_leaf rootTag input.tracker.global.nextPointerTag result.converted.byteSize distinct (GeneralBorrowGcVacantClean.initial rootTag result.converted.byteSize)
  obtain ⟨P⟩:=CurrentCallOrdinaryEmptyCurrentSameBool.wildcard input id (Pointer.new .wildcard (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result same latent current cachedRoot base offset cachedBase older
  apply finish_source input id (Pointer.new .wildcard (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result tree rfl same base offset count nonnull cachedBase cachedRoot older P leaf (by change (2 : Nat)=2;rfl)
  rw [frameEq] at copy
  rw [CurrentCallOrdinaryEmptyCurrentState.wildcard_eq input id (Pointer.new .wildcard (Size.ofBytes (base+offset))) rootTag source externStatic _ finalAddresses finalTape result] at copy
  exact copy
end
end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentSameSafety
