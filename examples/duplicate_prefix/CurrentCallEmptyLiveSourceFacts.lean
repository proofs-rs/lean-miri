import duplicate_prefix.CurrentCallEmptyLiveConcreteEntry
import duplicate_prefix.CurrentCallEmptyLiveWildcardEntry
import duplicate_prefix.S04ZeroConcreteRuntime
import duplicate_prefix.S04ZeroWildcardRuntime
namespace DuplicatePrefix.CurrentCallEmptyLiveSourceFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Current metadata from the same two real entry operations. This does not
assert full post-clear provenance well-formedness or any source byte grant. -/
structure Facts (initial : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (sourceId : AllocId)
    (oldSource : LocalAllocation Provenance BorrowTree MiriMemoryKind) (sourceBase : UInt64)
    (machine : Before) (global : GlobalState) (boolTag : BorTag)
    (source : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (oldBool currentBool : Allocation Provenance BorrowTree) (sourceAllowance boolAllowance : Nat) : Prop where
  user : machine.user=(CurrentCallPush.preparedMachine initial frames).user
  types : machine.user.payload.payload.user.types=initial.user.payload.payload.user.types
  origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types
  addresses : machine.user.addresses=initial.user.addresses
  extras : machine.user.payload.payload.user.runtime.extras=initial.user.payload.payload.user.runtime.extras
  cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,sourceBase⟩
  sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts source.allocation.extra global
  sourceSize : source.allocation.byteSize=oldSource.allocation.byteSize
  sourceLen : source.allocation.len=oldSource.allocation.len
  sourceKind : source.kind=oldSource.kind
  sourceGrowth : source.allocation.extra.nodes.size≤oldSource.allocation.extra.nodes.size+sourceAllowance
  boolGrowth : currentBool.extra.nodes.size≤oldBool.extra.nodes.size+boolAllowance
  counter : global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2
  flags : global.protectedTags=(tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert boolTag .StrongProtector
  rootTags : global.rootPointerTags=tracker.global.rootPointerTags
  trackedTags : global.trackedPointerTags=tracker.global.trackedPointerTags

private theorem operation_facts {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (room : W.allocation.extra.nodes.size+1<65536)
    (start : UInt64) (startEq : start.toNat=offset)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start 1=.ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1) (tag : output.tag=tracker.global.nextPointerTag)
    (constructor : Before) (constructorPresent : Present (ActualWorld constructor) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id=tracker.global.rootTag? id) :
    output.global=(registered tracker.global frame id fresh).1 ∧
    (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree.nodes.size≤W.allocation.extra.nodes.size+1 ∧
    (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree.locations.size=W.allocation.extra.locations.size := by
  have literal : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id fresh W.pointer.value.provenance start 1 :=
    Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ fresh _ _ _))
  have bounds : start.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have bound:=(W.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [W.issued.capability.treeExtent,←W.issued.capability.extent]
    omega
  have growth:=(quiet_source_rule "CurrentCallSelectedBoolCurrent.growth") W runtime frame fresh rfl distinct (by omega) (by omega) start 1 startEq rfl (by decide) bounds output actual
  have write:=CurrentCallSelectedBoolCurrent.operation_runtime W runtime frame fresh distinct room start startEq output child actual witness tag constructor constructorPresent rootTag .VisitChildrenOfAccessed
  refine ⟨by rw [literal];rfl,?_,write.2.2.2.2.2.2.2.trans witness.capacity⟩
  rw [write.2.2.2.2.1]
  exact growth

namespace Concrete
private def scopeWindow {before tracker data owner id offset} (frames : Array CompilerFrameContext.ActualFrame)
    (B : UniformWindow before tracker data owner id offset 1 .ret) :
    UniformWindow (ScopedFrame.entered (CurrentCallPush.preparedMachine before frames) tracker .FnEntry)
      ⟨tracker.global,.FnEntry⟩ data owner id offset 1 .ret := {
  B with
  issued:=by
    apply CurrentCallAllocationLicense.spatial B.issued
      (ScopedFrame.entered (CurrentCallPush.preparedMachine before frames) tracker .FnEntry) ⟨tracker.global,.FnEntry⟩ B.allocation (by exact B.present) rfl rfl rfl rfl
    · intro position root found;exact found
    · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
    · intro child parent edge;exact edge }

/-- Live concrete zero-byte entry when source and Bool share an allocation.
The actual empty source constructor is retained; no source content grant is
needed. Both typed source copying and typed Bool protection are conclusions. -/
theorem same (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span initial)
    (enabled : initial.borrowTracker=some tracker)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness initial frames)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow initial place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow initial tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : physical.entry.allocation.extra.indexOfTag parentTag=some parent)
    (parentAt : physical.entry.allocation.extra.nodeAt parent=some parentNode)
    (start count : UInt64) (nonzero : physical.base+start≠0)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+2<65536)
    (ready : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins initial.user.payload.payload.user.types) :
    ∃(output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (machine : Before) (frame : CompilerFrameContext.ActualFrame),
    ∃nextData nextOwner,∃Q : UniformWindow machine ⟨output.global,tracker.retagMode⟩ nextData nextOwner physical.id physical.offset.toNat 1 .ret,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete physical.id parentTag) (Size.ofBytes (physical.base+start)))) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=.ok () (Storage.withCurrent frames frame machine) ∧
      machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      Q.pointer.grant=child ∧Q.pointer.value.provenance=.concrete physical.id output.tag ∧
      tracker.global.nextPointerTag.value<output.tag.value ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra output.global ∧
      Q.allocation.extra.roots.toList.Nodup ∧Q.allocation.extra.nodes.size<65536 ∧
      SpatialDelegation machine ⟨output.global,tracker.retagMode⟩ physical.id Q.allocation Q.precise.completion B.pointer.grant ∧
      PointerBinds Q.allocation B.pointer ∧
      Q.precise.completion.parents[child.toNat]?=some (some B.pointer.grant) ∧
      frame.returnPlace=.memory place ∧
      frame.extra.borrowTracker=some ((({} : FrameState).addProtector physical.id tracker.global.nextPointerTag).addProtector physical.id output.tag) ∧
      frame=PositiveRootInstalledFrame.installed (CurrentCallSpatialEntryControl.root initial frames place model.noDataRace)
        (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete physical.id tracker.global.nextPointerTag) (Size.ofBytes (physical.base+start)))) 0 ActualReferenceMetadata.reference).imm
        count {} physical.id tracker.global.nextPointerTag physical.id output.tag ∧
      (∀index node,Q.allocation.extra.nodes.get index=some node→node.tag=tracker.global.nextPointerTag→node.isExposed=false) ∧
      DuplicatePrefixCallModel.Model options remaining span machine ∧
      machine.threads=(CurrentCallPush.preparedMachine initial frames).threads ∧
      (∃window : CurrentCallBoolScalarWrite.Window machine place,
        window.pointer=physical.pointer ∧window.id=physical.id ∧window.offset=physical.offset ∧window.entry.allocation=Q.allocation ∧
        CandidateCallBindings.WindowBinding machine window.pointer window.id window.offset.toNat 1 ∧
        CurrentCallBoolProtection.WindowReady machine window.id window.offset.toNat 1) ∧
      (∃sourceEntry,machine.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,sourceEntry) ∧
        CurrentCallEmptyEntrySourceData.Leaf sourceEntry.allocation.extra tracker.global.nextPointerTag ∧
        Facts initial tracker frames physical.id physical.entry physical.base machine output.global output.tag sourceEntry B.allocation Q.allocation 2 2) ∧
      ∃node,Q.allocation.extra.nodes.get child=some node ∧node.tag=output.tag ∧node.children=#[] ∧node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra child .Write physical.offset (physical.offset+1) := by
  let prepared:=CurrentCallPush.preparedMachine initial frames
  let root:=CurrentCallSpatialEntryControl.root initial frames place model.noDataRace
  let activeInput:=ScopedFrame.entered prepared tracker .FnEntry
  let fresh : tracker.global.nextPointerTag.value<18446744073709551615:=UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  let room : physical.entry.allocation.extra.nodes.size+1≤4294967295:=by rw [allocation];omega
  have sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra tracker.global := by rw [allocation];exact runtime
  let input:=ConcreteEmptyRuntimeEntry.form physical.entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag
    sourceRuntime.formed parent parentNode tagged parentAt (ConcreteEmptyRuntimeEntry.counter_fresh _ _ sourceRuntime.below) room
  let argument:=DuplicatePrefixSliceArgument.Argument.pointer (Pointer.new (.concrete physical.id parentTag) (Size.ofBytes (physical.base+start)))
  let effect : Effect options prepared tracker argument:=.concreteLive (physical.base+start) physical.id parentTag physical.entry input.after physical.live
    ⟨physical.base,start,physical.cachedBase,rfl,input.child start⟩
  let fn:=resultMachine effect fresh remaining span frames (firstLive root).frame {} 1 ((firstLive root).valid i1)
  let next:MachineHooks.BorrowState:=⟨(registered tracker.global {} physical.id fresh).1,.FnEntry⟩
  let source:Before:={fn with borrowTracker:=some {next with retagMode:=tracker.retagMode}}
  let sourceFrame:FrameState:=({} : FrameState).addProtector physical.id tracker.global.nextPointerTag
  have frameBorrow : (firstLive root).frame.extra.borrowTracker=some {}:=RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot initial).2 tracker enabled
  have live1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  obtain ⟨copyCtx⟩:=(DuplicatePrefixCallModel.contexts options remaining span initial model).1
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span initial model).2.2.2
  obtain ⟨copy,technical,P,ptr,alloc,run⟩:=CurrentCallEmptyConcreteCopy.copy_same_bool options limits remaining span copyCtx model.debugOff model.nullComparator
    dynamicFuel validationFuel dynamicEq validationEq physical.id parentTag tracker.global physical.base start nonzero physical.entry
    frames (firstLive root).frame activeInput 1 ((firstLive root).valid i1) .uninit live1 cached1 (firstLive root).noClocks
    model.ghostOff model.shallow physical.cachedBase physical.live {} frameBorrow rfl fresh sourceRuntime parent parentNode tagged parentAt room
    data owner physical.offset.toNat (scopeWindow frames B) allocation.symm model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView rfl
  have copyStep : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallEmptyEntryControl.value options remaining span argument).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame activeInput)=.ok () (Storage.withCurrent frames
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root {}).frame fn) := copy
  let current : UniformWindow source {next with retagMode:=tracker.retagMode} technical owner physical.id physical.offset.toNat 1 .ret := {P with
    issued:=by
      apply CurrentCallAllocationLicense.spatial P.issued source {next with retagMode:=tracker.retagMode} P.allocation (by exact P.present) rfl rfl rfl rfl
      · intro position root found;exact found
      · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
      · intro child parent edge;exact edge }
  have present : source.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra input.after}) :=
    MemoryCopyBridge.live_lookup_replaced prepared.memory physical.id _
  let physicalSource:=CurrentCallBoolWindow.tree_only physical source input.after rfl present
  have bindingSource : CandidateCallBindings.WindowBinding source physical.pointer physical.id physical.offset.toNat 1 :=
    CurrentCallBoolWindow.replace_binding initial source physical.pointer physical.id physical.offset.toNat 1 binding physical.id physical.entry
      {physical.entry with allocation:=physical.entry.allocation.setExtra input.after} physical.live rfl rfl rfl rfl
  have readySource:=CurrentCallBoolProtection.WindowReady.transport (before:=initial) (after:=source) ready rfl
  have childEq : physical.entry.allocation.extra.newChild (Size.ofBytes start) (.concrete parentTag) tracker.global.nextPointerTag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true=⟨input.after,.ok ()⟩ := input.child start
  have growth:= (CurrentCallEmptyConcreteResources.installed (scopeWindow frames B) runtime parentTag parent parentNode
    (by change B.allocation.extra.indexOfTag parentTag=some parent;rw [←allocation];exact tagged) (by change B.allocation.extra.nodeAt parent=some parentNode;rw [←allocation];exact parentAt) {} fresh (by change B.allocation.extra.nodes.size+1≤4294967295;rw [←allocation];exact room) start source
    (by dsimp only [scopeWindow];rw [←allocation, childEq];change Present (ActualWorld source) physical.id (physical.entry.allocation.setExtra input.after);rw [←alloc];exact current.present)).2.2.1
  have rootEq : input.after.roots=B.allocation.extra.roots := by
    rw [←allocation];exact S04ZeroChildMetadata.roots physical.entry.allocation.extra parentTag tracker.global.nextPointerTag input
  have freshAfter : next.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value];exact tagRoom
  obtain ⟨output,child,machine,nextData,nextOwner,Q,entered,tracked,pointerQ,runtimeQ,rootsQ,shortQ,node,nodeAt,nodeTag,leaf,hidden,activity,parentIssued,parentBinding,_,edge,actual,⟨witness⟩,tag,constructor,constructorPresent,rootTag,extra,postLive,scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady,userEq,threadsEq,raceEq⟩:=
    CurrentCallEmptyLiveEntryCurrent.init_current_of_copy options limits remaining span ctx initial tracker frames place model.noDataRace stackReady model.debugOff
      argument effect {} count fn source next sourceFrame enabled rfl rfl model.ghostOff model.shallow rfl model.shallow model.noDataRace model.noBackend validationFuel validationEq copyStep
      physicalSource technical owner current (pointer.trans (congrArg PointerInstance.value ptr).symm) alloc.symm run bindingSource
      (by rw [alloc];exact rootEq ▸ distinct) freshAfter (by rw [alloc];change input.after.nodes.size+1<65536;have h:=growth;dsimp only [scopeWindow] at h;rw [←allocation,childEq] at h;change input.after.nodes.size≤physical.entry.allocation.extra.nodes.size+1 at h;have rhs:=congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.nodes.size) allocation;omega)
      readySource rfl
  have sourceLeaf : CurrentCallEmptyEntrySourceData.Leaf current.allocation.extra tracker.global.nextPointerTag := by
    rw [alloc]
    exact (quiet_source_rule "CurrentCallEmptyEntrySourceData.pool_leaf") input
  obtain ⟨qIndex,qNode,qTagged,qAt,qTag,qLeaf,qHidden,qInactive⟩:=sourceLeaf
  have currentPointer : current.pointer=B.pointer:=ptr
  have qDifferent:=CurrentCallSelectedBoolQuietSource.different B runtime current currentPointer qIndex qNode qAt qTag qHidden
  obtain ⟨qNext,qNextAt,qNextTag,qParent,qChildren,qExposure,qQuiet⟩:=CurrentCallSelectedBoolQuietSource.operation current run sourceFrame freshAfter
    (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact rootEq ▸ distinct)
    (by
      change P.allocation.extra.nodes.size+1<65536
      rw [alloc]
      change input.after.nodes.size+1<65536
      have h:=growth
      dsimp only [scopeWindow] at h
      rw [←allocation,childEq] at h
      change input.after.nodes.size≤physical.entry.allocation.extra.nodes.size+1 at h
      have rhs:=congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.nodes.size) allocation
      omega)
    physical.offset rfl output child actual witness tag constructor constructorPresent rootTag qIndex qNode qAt qLeaf qHidden qDifferent qInactive
  have sourceFinal : CurrentCallEmptyEntrySourceData.Leaf Q.allocation.extra tracker.global.nextPointerTag := by
    have found : Q.allocation.extra.nodes.get qIndex=some qNext:=by rw [extra];exact qNextAt
    have tagQ : qNext.tag=tracker.global.nextPointerTag:=qNextTag.trans qTag
    refine ⟨qIndex,qNext,?_,found,tagQ,qChildren.trans qLeaf,qExposure.trans qHidden,?_⟩
    · rw [←tagQ];exact runtimeQ.formed.allocator.nodeTags _ _ found
    · rw [extra];exact qQuiet
  have sourceHidden : ∀index node,Q.allocation.extra.nodes.get index=some node→node.tag=tracker.global.nextPointerTag→node.isExposed=false := by
    obtain ⟨qi,qn,qt,qa,qtag,_,qh,_⟩:=sourceFinal
    intro index node found nodeTag
    have mapped:=runtimeQ.formed.allocator.nodeTags _ _ found
    rw [nodeTag] at mapped
    have indexEq : index=qi:=Option.some.inj (mapped.symm.trans qt)
    rw [indexEq] at found
    have nodeEq : node=qn:=Option.some.inj (found.symm.trans qa)
    rw [nodeEq];exact qh
  have sourceFinalLive : machine.memory.live.find? (fun row=>row.1==physical.id)=
      some (physical.id,{physicalSource.entry with allocation:=Q.allocation}) := by
    rw [postLive];exact MemoryCopyBridge.live_lookup_replaced source.memory physical.id _
  rw [currentPointer] at parentIssued parentBinding edge
  have sourceOlder : tracker.global.nextPointerTag.value<output.tag.value := by
    rw [tag]
    apply UInt64.lt_iff_toNat_lt.mpr
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have preparedModel:=CurrentCallResourcePreparedEntry.model model frames
  have sourceUser : source.user=prepared.user := by
    change {prepared.user with payload:={prepared.user.payload with ghost:=false}}=prepared.user
    rw [←preparedModel.ghostOff]
  have mode : tracker.retagMode=.Default := by
    obtain ⟨old,found,mode⟩:=model.defaultTracker
    have eq : old=tracker:=Option.some.inj (found.symm.trans enabled)
    simpa only [eq] using mode
  have modelAfter : DuplicatePrefixCallModel.Model options remaining span machine := by
    refine ⟨model.debugOff,model.preciseOff,model.implicitOff,?_,?_,⟨⟨output.global,tracker.retagMode⟩,tracked,mode⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
    · rw [userEq];rfl
    · rw [userEq];exact preparedModel.shallow
    · rw [raceEq];exact model.noDataRace
    · rw [userEq];exact preparedModel.noBackend
    · rw [userEq];exact preparedModel.metadata
    · rw [threadsEq];exact preparedModel.fixedScheduler
    · rw [userEq,sourceUser];exact preparedModel.unchecked
    · rw [userEq,sourceUser];exact preparedModel.noGc
  obtain ⟨globalEq,boolGrowthRaw,boolCapacity⟩:=operation_facts current run sourceFrame freshAfter
    (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact rootEq ▸ distinct) (by
      change P.allocation.extra.nodes.size+1<65536
      rw [alloc]
      change input.after.nodes.size+1<65536
      have h:=growth
      dsimp only [scopeWindow] at h
      rw [←allocation,childEq] at h
      change input.after.nodes.size≤physical.entry.allocation.extra.nodes.size+1 at h
      have rhs:=congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.nodes.size) allocation
      omega) physical.offset rfl output child actual witness tag constructor constructorPresent rootTag
  have boolGrowth : Q.allocation.extra.nodes.size≤current.allocation.extra.nodes.size+1 := by rw [extra];exact boolGrowthRaw
  have userPrepared : machine.user=prepared.user:=userEq.trans sourceUser
  have typesEq : machine.user.payload.payload.user.types=initial.user.payload.payload.user.types := by rw [userPrepared];rfl
  have addressesEq : machine.user.addresses=initial.user.addresses := by rw [userPrepared];rfl
  have extrasEq : machine.user.payload.payload.user.runtime.extras=initial.user.payload.payload.user.runtime.extras := by rw [userPrepared];rfl
  have counterEq : output.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 := by
    have firstCounter : next.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 := by
      change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat=_
      exact GenericFunctionEntryNumerics.successor_value _ _
    have secondCounter : output.global.nextPointerTag.value.toNat=next.global.nextPointerTag.value.toNat+1 := by
      rw [globalEq]
      change (TypedRetagEmpty.successorTag next.global.nextPointerTag freshAfter).value.toNat=_
      exact GenericFunctionEntryNumerics.successor_value _ _
    omega
  have flagsEq : output.global.protectedTags=(tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert output.tag .StrongProtector := by rw [globalEq,tag];rfl
  have rootsEq : output.global.rootPointerTags=tracker.global.rootPointerTags := by rw [globalEq];rfl
  have trackedEq : output.global.trackedPointerTags=tracker.global.trackedPointerTags := by rw [globalEq];rfl
  have bytesEq : Q.allocation.byteSize=current.allocation.byteSize := by
    calc
      Q.allocation.byteSize=Q.allocation.extra.locations.size:=Q.issued.capability.treeExtent.symm
      _=current.allocation.extra.locations.size:=by rw [extra];exact boolCapacity
      _=current.allocation.byteSize:=current.issued.capability.treeExtent
  have lengthEq : Q.allocation.len=current.allocation.len := by
    rw [Q.issued.capability.extent,bytesEq]
    exact current.issued.capability.extent.symm
  have qGrowth : input.after.nodes.size≤B.allocation.extra.nodes.size+1 := by
    have h:=growth
    dsimp only [scopeWindow] at h
    rw [←allocation,childEq] at h
    change input.after.nodes.size≤physical.entry.allocation.extra.nodes.size+1 at h
    have rhs:=congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.nodes.size) allocation
    omega
  have allGrowth : Q.allocation.extra.nodes.size≤B.allocation.extra.nodes.size+2 := by
    change Q.allocation.extra.nodes.size≤P.allocation.extra.nodes.size+1 at boolGrowth
    rw [alloc] at boolGrowth
    change Q.allocation.extra.nodes.size≤input.after.nodes.size+1 at boolGrowth
    omega
  have facts : Facts initial tracker frames physical.id physical.entry physical.base machine output.global output.tag
      {physicalSource.entry with allocation:=Q.allocation} B.allocation Q.allocation 2 2 := {
    user:=userPrepared,types:=typesEq,origins:=by rw [typesEq];exact origins,addresses:=addressesEq,extras:=extrasEq,
    cached:=by rw [addressesEq];exact physical.cachedBase,sourceRuntime:=runtimeQ,
    sourceSize:=by change Q.allocation.byteSize=physical.entry.allocation.byteSize;rw [bytesEq];change P.allocation.byteSize=_;rw [alloc];rfl
    sourceLen:=by change Q.allocation.len=physical.entry.allocation.len;rw [lengthEq];change P.allocation.len=_;rw [alloc];rfl
    sourceKind:=rfl,sourceGrowth:=by change Q.allocation.extra.nodes.size≤physical.entry.allocation.extra.nodes.size+2;have rhs:=congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.nodes.size) allocation;omega
    boolGrowth:=allGrowth,counter:=counterEq,flags:=flagsEq,rootTags:=rootsEq,trackedTags:=trackedEq}
  exact ⟨output,child,machine,_,nextData,nextOwner,Q,entered,tracked,(by rw [pointerQ];rfl),(by rw [pointerQ];rfl),sourceOlder,runtimeQ,rootsQ,shortQ,parentIssued,parentBinding,edge,rfl,rfl,
    CurrentCallEmptyLiveFrames.installed_eq effect remaining span root count {} _ physical.id output.tag rfl,sourceHidden,
    modelAfter,threadsEq,⟨scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady⟩,
    ⟨{physicalSource.entry with allocation:=Q.allocation},sourceFinalLive,sourceFinal,facts⟩,node,nodeAt,nodeTag,leaf,hidden,activity⟩

/-- The different-allocation live concrete branch retains the original Bool allocation. -/
theorem different (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span initial)
    (enabled : initial.borrowTracker=some tracker)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness initial frames)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow initial place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow initial tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (sourceId : AllocId) (different : sourceId≠physical.id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : initial.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry))
    (sourceBase : UInt64)
    (sourceCached : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,sourceBase⟩)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (sourceRoom : entry.allocation.extra.nodes.size+1≤4294967295)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag parentTag=some parent)
    (parentAt : entry.allocation.extra.nodeAt parent=some parentNode)
    (start count : UInt64) (nonzero : sourceBase+start≠0)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins initial.user.payload.payload.user.types) :
    ∃(output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (machine : Before) (frame : CompilerFrameContext.ActualFrame),
    ∃nextData nextOwner,∃Q : UniformWindow machine ⟨output.global,tracker.retagMode⟩ nextData nextOwner physical.id physical.offset.toNat 1 .ret,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (sourceBase+start)))) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=.ok () (Storage.withCurrent frames frame machine) ∧
      machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      Q.pointer.grant=child ∧Q.pointer.value.provenance=.concrete physical.id output.tag ∧
      tracker.global.nextPointerTag.value<output.tag.value ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra output.global ∧
      Q.allocation.extra.roots.toList.Nodup ∧Q.allocation.extra.nodes.size<65536 ∧
      SpatialDelegation machine ⟨output.global,tracker.retagMode⟩ physical.id Q.allocation Q.precise.completion B.pointer.grant ∧
      PointerBinds Q.allocation B.pointer ∧
      Q.precise.completion.parents[child.toNat]?=some (some B.pointer.grant) ∧
      frame.returnPlace=.memory place ∧
      frame.extra.borrowTracker=some ((({} : FrameState).addProtector sourceId tracker.global.nextPointerTag).addProtector physical.id output.tag) ∧
      frame=PositiveRootInstalledFrame.installed (CurrentCallSpatialEntryControl.root initial frames place model.noDataRace)
        (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete sourceId tracker.global.nextPointerTag) (Size.ofBytes (sourceBase+start)))) 0 ActualReferenceMetadata.reference).imm
        count {} sourceId tracker.global.nextPointerTag physical.id output.tag ∧
      (∀index node,Q.allocation.extra.nodes.get index=some node→node.tag=tracker.global.nextPointerTag→node.isExposed=false) ∧
      DuplicatePrefixCallModel.Model options remaining span machine ∧
      machine.threads=(CurrentCallPush.preparedMachine initial frames).threads ∧
      (∃window : CurrentCallBoolScalarWrite.Window machine place,
        window.pointer=physical.pointer ∧window.id=physical.id ∧window.offset=physical.offset ∧window.entry.allocation=Q.allocation ∧
        CandidateCallBindings.WindowBinding machine window.pointer window.id window.offset.toNat 1 ∧
        CurrentCallBoolProtection.WindowReady machine window.id window.offset.toNat 1) ∧
      (∃sourceEntry,machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry) ∧
        CurrentCallEmptyEntrySourceData.Leaf sourceEntry.allocation.extra tracker.global.nextPointerTag ∧
        Facts initial tracker frames sourceId entry sourceBase machine output.global output.tag sourceEntry B.allocation Q.allocation 1 1) ∧
      ∃node,Q.allocation.extra.nodes.get child=some node ∧node.tag=output.tag ∧node.children=#[] ∧node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra child .Write physical.offset (physical.offset+1) := by
  let prepared:=CurrentCallPush.preparedMachine initial frames
  let root:=CurrentCallSpatialEntryControl.root initial frames place model.noDataRace
  let activeInput:=ScopedFrame.entered prepared tracker .FnEntry
  let fresh : tracker.global.nextPointerTag.value<18446744073709551615:=UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  let input:=ConcreteEmptyRuntimeEntry.form entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag
    sourceRuntime.formed parent parentNode tagged parentAt (ConcreteEmptyRuntimeEntry.counter_fresh _ _ sourceRuntime.below) sourceRoom
  let argument:=DuplicatePrefixSliceArgument.Argument.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (sourceBase+start)))
  let effect : Effect options prepared tracker argument:=.concreteLive (sourceBase+start) sourceId parentTag entry input.after sourceLive
    ⟨sourceBase,start,sourceCached,rfl,input.child start⟩
  let fn:=resultMachine effect fresh remaining span frames (firstLive root).frame {} 1 ((firstLive root).valid i1)
  let next:MachineHooks.BorrowState:=⟨(registered tracker.global {} sourceId fresh).1,.FnEntry⟩
  let source:Before:={fn with borrowTracker:=some {next with retagMode:=tracker.retagMode}}
  let sourceFrame:FrameState:=({} : FrameState).addProtector sourceId tracker.global.nextPointerTag
  have frameBorrow : (firstLive root).frame.extra.borrowTracker=some {}:=RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot initial).2 tracker enabled
  have live1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  obtain ⟨copyCtx⟩:=(DuplicatePrefixCallModel.contexts options remaining span initial model).1
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span initial model).2.2.2
  obtain ⟨copy,P,ptr,alloc,precise,run⟩:=CurrentCallEmptyOtherBool.concrete options limits remaining span copyCtx model.debugOff model.nullComparator
    dynamicFuel validationFuel dynamicEq validationEq sourceId parentTag tracker.global sourceBase start nonzero entry
    frames (firstLive root).frame activeInput 1 ((firstLive root).valid i1) .uninit live1 cached1 (firstLive root).noClocks
    model.ghostOff model.shallow sourceCached sourceLive {} frameBorrow rfl fresh sourceRuntime parent parentNode tagged parentAt sourceRoom
    data owner physical.id physical.offset.toNat (scopeWindow frames B) runtime different model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView rfl
  have copyStep : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallEmptyEntryControl.value options remaining span argument).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame activeInput)=.ok () (Storage.withCurrent frames
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root {}).frame fn) := copy
  let current : UniformWindow source {next with retagMode:=tracker.retagMode} data owner physical.id physical.offset.toNat 1 .ret := {P with
    issued:=by
      apply CurrentCallAllocationLicense.spatial P.issued source {next with retagMode:=tracker.retagMode} P.allocation (by exact P.present) rfl rfl rfl rfl
      · intro position root found;exact found
      · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
      · intro child parent edge;exact edge }
  have present : source.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,physical.entry) := by
    change ((initial.memory.live.filter (fun row=>row.1!=sourceId)).push
      (sourceId,{entry with allocation:=entry.allocation.setExtra input.after})).find? (fun row=>row.1==physical.id)=_
    rw [Array.find?_push,Array.find?_filter]
    have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind => decide ((row.1!=sourceId)=true ∧ (row.1==physical.id)=true))=
        (fun row=>row.1==physical.id) := by
      funext row
      by_cases equal : row.1=physical.id
      · simp [equal,Ne.symm different]
      · simp [equal]
    rw [predicate,physical.live]
    simp [different]
  let physicalSource : CandidateCurrentBoolUninitWrite.PhysicalWindow source place:={physical with live:=present}
  have bindingSource : CandidateCallBindings.WindowBinding source physical.pointer physical.id physical.offset.toNat 1 :=
    CurrentCallBoolWindow.replace_binding initial source physical.pointer physical.id physical.offset.toNat 1 binding sourceId entry
      {entry with allocation:=entry.allocation.setExtra input.after} sourceLive rfl rfl rfl rfl
  have readySource:=CurrentCallBoolProtection.WindowReady.transport (before:=initial) (after:=source) ready rfl
  have freshAfter : next.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value];exact tagRoom
  obtain ⟨output,child,machine,nextData,nextOwner,Q,entered,tracked,pointerQ,runtimeQ,rootsQ,shortQ,node,nodeAt,nodeTag,leaf,hidden,activity,parentIssued,parentBinding,_,edge,actual,⟨witness⟩,tag,constructor,constructorPresent,rootTag,extra,postLive,scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady,userEq,threadsEq,raceEq⟩:=
    CurrentCallEmptyLiveEntryCurrent.init_current_of_copy options limits remaining span ctx initial tracker frames place model.noDataRace stackReady model.debugOff
      argument effect {} count fn source next sourceFrame enabled rfl rfl model.ghostOff model.shallow rfl model.shallow model.noDataRace model.noBackend validationFuel validationEq copyStep
      physicalSource data owner current (pointer.trans (congrArg PointerInstance.value ptr).symm) (allocation.trans alloc.symm) run bindingSource
      (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact distinct) freshAfter
      (by change P.allocation.extra.nodes.size+1<65536;rw [alloc];exact nodeRoom)
      readySource rfl
  have oldBelow : ∀row∈current.allocation.extra.tagMapping.mapping,row.1.value.toNat<tracker.global.nextPointerTag.value.toNat := by
    intro row member
    change row∈P.allocation.extra.tagMapping.mapping at member
    rw [alloc] at member
    exact runtime.below.mapping row member
  have beforeFresh : tracker.global.nextPointerTag.value.toNat<next.global.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have absent:=CurrentCallSelectedBorrowTagOrigin.written_node_absent current run sourceFrame freshAfter
    (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact distinct)
    (by change P.allocation.extra.nodes.size+1<65536;rw [alloc];exact nodeRoom)
    physical.offset rfl output child actual witness tracker.global.nextPointerTag oldBelow beforeFresh
  have sourceHidden : ∀index node,Q.allocation.extra.nodes.get index=some node→node.tag=tracker.global.nextPointerTag→node.isExposed=false := by
    intro index node found same
    exact False.elim (absent index node (by rw [←extra];exact found) same)
  have sourceOld : CurrentCallEmptyEntrySourceData.Leaf input.after tracker.global.nextPointerTag := (quiet_source_rule "CurrentCallEmptyEntrySourceData.pool_leaf") input
  have sourceOldLive : source.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,{entry with allocation:=entry.allocation.setExtra input.after}) :=
    MemoryCopyBridge.live_lookup_replaced prepared.memory sourceId _
  have sourceFinalLive : machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,{entry with allocation:=entry.allocation.setExtra input.after}) := by
    rw [postLive,Array.find?_push,Array.find?_filter]
    have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind=>decide ((row.1!=physical.id)=true ∧(row.1==sourceId)=true))=
        (fun row=>row.1==sourceId) := by
      funext row
      by_cases equal : row.1=sourceId
      · simp [equal,different]
      · simp [equal]
    rw [predicate,sourceOldLive]
    simp
  have currentPointer : current.pointer=B.pointer:=ptr
  rw [currentPointer] at parentIssued parentBinding edge
  have sourceOlder : tracker.global.nextPointerTag.value<output.tag.value := by
    rw [tag]
    apply UInt64.lt_iff_toNat_lt.mpr
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have preparedModel:=CurrentCallResourcePreparedEntry.model model frames
  have sourceUser : source.user=prepared.user := by
    change {prepared.user with payload:={prepared.user.payload with ghost:=false}}=prepared.user
    rw [←preparedModel.ghostOff]
  have mode : tracker.retagMode=.Default := by
    obtain ⟨old,found,mode⟩:=model.defaultTracker
    have eq : old=tracker:=Option.some.inj (found.symm.trans enabled)
    simpa only [eq] using mode
  have modelAfter : DuplicatePrefixCallModel.Model options remaining span machine := by
    refine ⟨model.debugOff,model.preciseOff,model.implicitOff,?_,?_,⟨⟨output.global,tracker.retagMode⟩,tracked,mode⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
    · rw [userEq];rfl
    · rw [userEq];exact preparedModel.shallow
    · rw [raceEq];exact model.noDataRace
    · rw [userEq];exact preparedModel.noBackend
    · rw [userEq];exact preparedModel.metadata
    · rw [threadsEq];exact preparedModel.fixedScheduler
    · rw [userEq,sourceUser];exact preparedModel.unchecked
    · rw [userEq,sourceUser];exact preparedModel.noGc
  obtain ⟨globalEq,boolGrowthRaw,boolCapacity⟩:=operation_facts current run sourceFrame freshAfter
    (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact distinct) (by change P.allocation.extra.nodes.size+1<65536;rw [alloc];exact nodeRoom) physical.offset rfl output child actual witness tag constructor constructorPresent rootTag
  have boolGrowth : Q.allocation.extra.nodes.size≤current.allocation.extra.nodes.size+1 := by rw [extra];exact boolGrowthRaw
  have userPrepared : machine.user=prepared.user:=userEq.trans sourceUser
  have typesEq : machine.user.payload.payload.user.types=initial.user.payload.payload.user.types := by rw [userPrepared];rfl
  have addressesEq : machine.user.addresses=initial.user.addresses := by rw [userPrepared];rfl
  have extrasEq : machine.user.payload.payload.user.runtime.extras=initial.user.payload.payload.user.runtime.extras := by rw [userPrepared];rfl
  have counterEq : output.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 := by
    have firstCounter : next.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 := by
      change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat=_
      exact GenericFunctionEntryNumerics.successor_value _ _
    have secondCounter : output.global.nextPointerTag.value.toNat=next.global.nextPointerTag.value.toNat+1 := by
      rw [globalEq]
      change (TypedRetagEmpty.successorTag next.global.nextPointerTag freshAfter).value.toNat=_
      exact GenericFunctionEntryNumerics.successor_value _ _
    omega
  have flagsEq : output.global.protectedTags=(tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert output.tag .StrongProtector := by rw [globalEq,tag];rfl
  have rootsEq : output.global.rootPointerTags=tracker.global.rootPointerTags := by rw [globalEq];rfl
  have trackedEq : output.global.trackedPointerTags=tracker.global.trackedPointerTags := by rw [globalEq];rfl
  obtain ⟨_,heldQ,_,registeredRuntime,_,freshQ⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra tracker.global {} sourceId fresh sourceRuntime
  have qBound : tracker.global.nextPointerTag.value.toNat<next.global.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have qHeld : next.global.protectedTags.contains tracker.global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    rw [heldQ]
    rfl
  have qConstruct:=S04ZeroConcreteRuntime.construct entry.allocation.extra next.global registeredRuntime parentTag parent parentNode tagged parentAt
    tracker.global.nextPointerTag freshQ sourceRoom qBound qHeld start
  have qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts input.after next.global := by
    have rr:=qConstruct.2.1
    rw [input.child start] at rr
    exact rr
  have qGrowth : input.after.nodes.size≤entry.allocation.extra.nodes.size+1 := by
    have g:=qConstruct.2.2.2
    rw [input.child start] at g
    exact g
  have sourceRuntimeFinal : DuplicatePrefixBorrowContract.RuntimeFacts input.after output.global := by
    rw [globalEq]
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare input.after next.global sourceFrame physical.id freshAfter qRuntime).2.2.2.1
  have allGrowth : Q.allocation.extra.nodes.size≤B.allocation.extra.nodes.size+1 := by
    change Q.allocation.extra.nodes.size≤P.allocation.extra.nodes.size+1 at boolGrowth
    rw [alloc] at boolGrowth
    exact boolGrowth
  have facts : Facts initial tracker frames sourceId entry sourceBase machine output.global output.tag
      {entry with allocation:=entry.allocation.setExtra input.after} B.allocation Q.allocation 1 1 := {
    user:=userPrepared,types:=typesEq,origins:=by rw [typesEq];exact origins,addresses:=addressesEq,extras:=extrasEq,
    cached:=by rw [addressesEq];exact sourceCached,sourceRuntime:=sourceRuntimeFinal,
    sourceSize:=rfl,sourceLen:=rfl,sourceKind:=rfl,sourceGrowth:=qGrowth,boolGrowth:=allGrowth,
    counter:=counterEq,flags:=flagsEq,rootTags:=rootsEq,trackedTags:=trackedEq}
  exact ⟨output,child,machine,_,nextData,nextOwner,Q,entered,tracked,(by rw [pointerQ];rfl),(by rw [pointerQ];rfl),sourceOlder,runtimeQ,rootsQ,shortQ,parentIssued,parentBinding,edge,rfl,rfl,
    CurrentCallEmptyLiveFrames.installed_eq effect remaining span root count {} _ physical.id output.tag rfl,sourceHidden,
    modelAfter,threadsEq,⟨scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady⟩,
    ⟨_,sourceFinalLive,sourceOld,facts⟩,node,nodeAt,nodeTag,leaf,hidden,activity⟩
end Concrete

namespace Wildcard
private def scopeWindow {before tracker data owner id offset} (frames : Array CompilerFrameContext.ActualFrame)
    (B : UniformWindow before tracker data owner id offset 1 .ret) :
    UniformWindow (ScopedFrame.entered (CurrentCallPush.preparedMachine before frames) tracker .FnEntry)
      ⟨tracker.global,.FnEntry⟩ data owner id offset 1 .ret := {
  B with
  issued:=by
    apply CurrentCallAllocationLicense.spatial B.issued
      (ScopedFrame.entered (CurrentCallPush.preparedMachine before frames) tracker .FnEntry) ⟨tracker.global,.FnEntry⟩ B.allocation (by exact B.present) rfl rfl rfl rfl
    · intro position root found;exact found
    · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
    · intro child parent edge;exact edge }

/-- Live wildcard zero-byte entry when source and Bool share an allocation.
The actual empty source constructor is retained; no source content grant is
needed. Both typed source copying and typed Bool protection are conclusions. -/
theorem same (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span initial)
    (enabled : initial.borrowTracker=some tracker)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness initial frames)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow initial place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow initial tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (start count : UInt64) (nonzero : physical.base+start≠0)
    (addressMode : initial.user.addresses.provenanceMode≠.strict)
    (inverse : WildcardGeneralHitReborrow.Geometry initial.user.addresses.intToPtrMap (physical.base+start) physical.base physical.id physical.entry.allocation.byteSize)
    (exposed : initial.user.addresses.exposed.contains physical.id=true)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+2<65536)
    (ready : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins initial.user.payload.payload.user.types) :
    ∃(output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (machine : Before) (frame : CompilerFrameContext.ActualFrame),
    ∃nextData nextOwner,∃Q : UniformWindow machine ⟨output.global,tracker.retagMode⟩ nextData nextOwner physical.id physical.offset.toNat 1 .ret,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes (physical.base+start)))) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=.ok () (Storage.withCurrent frames frame machine) ∧
      machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      Q.pointer.grant=child ∧Q.pointer.value.provenance=.concrete physical.id output.tag ∧
      tracker.global.nextPointerTag.value<output.tag.value ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra output.global ∧
      Q.allocation.extra.roots.toList.Nodup ∧Q.allocation.extra.nodes.size<65536 ∧
      SpatialDelegation machine ⟨output.global,tracker.retagMode⟩ physical.id Q.allocation Q.precise.completion B.pointer.grant ∧
      PointerBinds Q.allocation B.pointer ∧
      Q.precise.completion.parents[child.toNat]?=some (some B.pointer.grant) ∧
      frame.returnPlace=.memory place ∧
      frame.extra.borrowTracker=some ((({} : FrameState).addProtector physical.id tracker.global.nextPointerTag).addProtector physical.id output.tag) ∧
      frame=PositiveRootInstalledFrame.installed (CurrentCallSpatialEntryControl.root initial frames place model.noDataRace)
        (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete physical.id tracker.global.nextPointerTag) (Size.ofBytes (physical.base+start)))) 0 ActualReferenceMetadata.reference).imm
        count {} physical.id tracker.global.nextPointerTag physical.id output.tag ∧
      (∀index node,Q.allocation.extra.nodes.get index=some node→node.tag=tracker.global.nextPointerTag→node.isExposed=false) ∧
      DuplicatePrefixCallModel.Model options remaining span machine ∧
      machine.threads=(CurrentCallPush.preparedMachine initial frames).threads ∧
      (∃window : CurrentCallBoolScalarWrite.Window machine place,
        window.pointer=physical.pointer ∧window.id=physical.id ∧window.offset=physical.offset ∧window.entry.allocation=Q.allocation ∧
        CandidateCallBindings.WindowBinding machine window.pointer window.id window.offset.toNat 1 ∧
        CurrentCallBoolProtection.WindowReady machine window.id window.offset.toNat 1) ∧
      (∃sourceEntry,machine.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,sourceEntry) ∧
        CurrentCallEmptyEntrySourceData.Leaf sourceEntry.allocation.extra tracker.global.nextPointerTag ∧
        Facts initial tracker frames physical.id physical.entry physical.base machine output.global output.tag sourceEntry B.allocation Q.allocation 2 2) ∧
      ∃node,Q.allocation.extra.nodes.get child=some node ∧node.tag=output.tag ∧node.children=#[] ∧node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra child .Write physical.offset (physical.offset+1) := by
  let prepared:=CurrentCallPush.preparedMachine initial frames
  let root:=CurrentCallSpatialEntryControl.root initial frames place model.noDataRace
  let activeInput:=ScopedFrame.entered prepared tracker .FnEntry
  let fresh : tracker.global.nextPointerTag.value<18446744073709551615:=UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  let room : physical.entry.allocation.extra.nodes.size+1≤4294967295:=by rw [allocation];omega
  have sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra tracker.global := by rw [allocation];exact runtime
  let slot : WildcardHitPoolRoot.Slot physical.entry.allocation.extra:=WildcardHitPoolRoot.factory physical.entry.allocation.extra
    sourceRuntime.formed.allocator.pool sourceRuntime.formed.allocator.accounting (by
      have balance:=sourceRuntime.formed.allocator.accounting
      unfold GeneralBorrowFreshStagePool.Accounting at balance
      omega)
  let hit : S03WildcardEmptyClassification.Hit (DuplicatePrefixCallSpecification.imageContext options prepared tracker)
      prepared.memory prepared.user.addresses (physical.base+start):=⟨physical.id,physical.base,
        ⟨physical.entry.allocation.byteSize,physical.entry.allocation.align,.liveData,physical.entry.allocation.mutability⟩,
        MemoryCopyBridge.live_alloc_info _ _ _ physical.live,inverse,exposed,physical.cachedBase,Or.inl (.live physical.entry physical.live True.intro)⟩
  let argument:=DuplicatePrefixSliceArgument.Argument.pointer (Pointer.new .wildcard (Size.ofBytes (physical.base+start)))
  let effect : Effect options prepared tracker argument:=.wildcardLive (physical.base+start) hit physical.entry
    (slot.after tracker.global.nextPointerTag) physical.live ⟨slot,rfl⟩
  let fn:=resultMachine effect fresh remaining span frames (firstLive root).frame {} 1 ((firstLive root).valid i1)
  let next:MachineHooks.BorrowState:=⟨(registered tracker.global {} physical.id fresh).1,.FnEntry⟩
  let source:Before:={fn with borrowTracker:=some {next with retagMode:=tracker.retagMode}}
  let sourceFrame:FrameState:=({} : FrameState).addProtector physical.id tracker.global.nextPointerTag
  have frameBorrow : (firstLive root).frame.extra.borrowTracker=some {}:=RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot initial).2 tracker enabled
  have live1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  obtain ⟨copyCtx⟩:=(DuplicatePrefixCallModel.contexts options remaining span initial model).1
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span initial model).2.2.2
  obtain ⟨copy,technical,P,ptr,alloc,precise,dormant,run⟩:=CurrentCallEmptyWildcardCopy.copy_same_bool options limits remaining span copyCtx model.debugOff model.nullComparator
    dynamicFuel validationFuel dynamicEq validationEq physical.id tracker.global physical.base start nonzero physical.entry
    frames (firstLive root).frame activeInput 1 ((firstLive root).valid i1) .uninit live1 cached1 (firstLive root).noClocks
    model.ghostOff model.shallow physical.cachedBase physical.live {} frameBorrow rfl fresh addressMode inverse exposed sourceRuntime room
    data owner physical.offset.toNat (scopeWindow frames B) allocation.symm model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView rfl
  have copyStep : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallEmptyEntryControl.value options remaining span argument).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame activeInput)=.ok () (Storage.withCurrent frames
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root {}).frame fn) := copy
  let current : UniformWindow source {next with retagMode:=tracker.retagMode} technical owner physical.id physical.offset.toNat 1 .ret := {P with
    issued:=by
      apply CurrentCallAllocationLicense.spatial P.issued source {next with retagMode:=tracker.retagMode} P.allocation (by exact P.present) rfl rfl rfl rfl
      · intro position root found;exact found
      · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
      · intro child parent edge;exact edge }
  have present : source.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)}) :=
    MemoryCopyBridge.live_lookup_replaced prepared.memory physical.id _
  let physicalSource:=CurrentCallBoolWindow.tree_only physical source (slot.after tracker.global.nextPointerTag) rfl present
  have bindingSource : CandidateCallBindings.WindowBinding source physical.pointer physical.id physical.offset.toNat 1 :=
    CurrentCallBoolWindow.replace_binding initial source physical.pointer physical.id physical.offset.toNat 1 binding physical.id physical.entry
      {physical.entry with allocation:=physical.entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)} physical.live rfl rfl rfl rfl
  have readySource:=CurrentCallBoolProtection.WindowReady.transport (before:=initial) (after:=source) ready rfl
  have growth : (slot.after tracker.global.nextPointerTag).nodes.size≤B.allocation.extra.nodes.size+1 := by
    have sizes:=slot.size tracker.global.nextPointerTag
    have grow : slot.growth≤1:=by cases slot <;> simp only [WildcardHitPoolRoot.Slot.growth] <;> omega
    have sizesOld:=congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.nodes.size) allocation
    omega
  have rootsDistinct : (slot.after tracker.global.nextPointerTag).roots.toList.Nodup := by
    have outside : slot.index∉physical.entry.allocation.extra.roots.toList := by
      intro member
      obtain ⟨node,present,_⟩:=sourceRuntime.formed.rootNodes slot.index member
      rw [slot.vacant] at present
      contradiction
    change (physical.entry.allocation.extra.roots.push slot.index).toList.Nodup
    rw [Array.toList_push]
    apply List.nodup_append.mpr
    refine ⟨?_,by simp,?_⟩
    · rw [allocation];exact distinct
    · intro query member other single equal
      have same : other=slot.index:=by simpa using single
      subst other
      subst query
      exact outside member
  have freshAfter : next.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value];exact tagRoom
  obtain ⟨output,child,machine,nextData,nextOwner,Q,entered,tracked,pointerQ,runtimeQ,rootsQ,shortQ,node,nodeAt,nodeTag,leaf,hidden,activity,parentIssued,parentBinding,_,edge,actual,⟨witness⟩,tag,constructor,constructorPresent,rootTag,extra,postLive,scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady,userEq,threadsEq,raceEq⟩:=
    CurrentCallEmptyLiveEntryCurrent.init_current_of_copy options limits remaining span ctx initial tracker frames place model.noDataRace stackReady model.debugOff
      argument effect {} count fn source next sourceFrame enabled rfl rfl model.ghostOff model.shallow rfl model.shallow model.noDataRace model.noBackend validationFuel validationEq copyStep
      physicalSource technical owner current (pointer.trans (congrArg PointerInstance.value ptr).symm) alloc.symm run bindingSource
      (by rw [alloc];exact rootsDistinct) freshAfter
      (by rw [alloc];change (slot.after tracker.global.nextPointerTag).nodes.size+1<65536;omega)
      readySource rfl
  have sourceLeaf : CurrentCallEmptyEntrySourceData.Leaf current.allocation.extra tracker.global.nextPointerTag := by
    rw [alloc]
    exact (quiet_source_rule "CurrentCallEmptyEntrySourceData.slot_leaf") _ slot tracker.global.nextPointerTag
      (ConcreteEmptyRuntimeEntry.counter_fresh _ _ sourceRuntime.below) (DuplicatePrefixBorrowContract.vacant_clean sourceRuntime)
  obtain ⟨qIndex,qNode,qTagged,qAt,qTag,qLeaf,qHidden,qInactive⟩:=sourceLeaf
  have currentPointer : current.pointer=B.pointer:=ptr
  have qDifferent:=CurrentCallSelectedBoolQuietSource.different B runtime current currentPointer qIndex qNode qAt qTag qHidden
  obtain ⟨qNext,qNextAt,qNextTag,qParent,qChildren,qExposure,qQuiet⟩:=CurrentCallSelectedBoolQuietSource.operation current run sourceFrame freshAfter
    (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact rootsDistinct)
    (by change P.allocation.extra.nodes.size+1<65536;rw [alloc];change (slot.after tracker.global.nextPointerTag).nodes.size+1<65536;omega)
    physical.offset rfl output child actual witness tag constructor constructorPresent rootTag qIndex qNode qAt qLeaf qHidden qDifferent qInactive
  have sourceFinal : CurrentCallEmptyEntrySourceData.Leaf Q.allocation.extra tracker.global.nextPointerTag := by
    have found : Q.allocation.extra.nodes.get qIndex=some qNext:=by rw [extra];exact qNextAt
    have tagQ : qNext.tag=tracker.global.nextPointerTag:=qNextTag.trans qTag
    refine ⟨qIndex,qNext,?_,found,tagQ,qChildren.trans qLeaf,qExposure.trans qHidden,?_⟩
    · rw [←tagQ];exact runtimeQ.formed.allocator.nodeTags _ _ found
    · rw [extra];exact qQuiet
  have sourceHidden : ∀index node,Q.allocation.extra.nodes.get index=some node→node.tag=tracker.global.nextPointerTag→node.isExposed=false := by
    obtain ⟨qi,qn,qt,qa,qtag,_,qh,_⟩:=sourceFinal
    intro index node found nodeTag
    have mapped:=runtimeQ.formed.allocator.nodeTags _ _ found
    rw [nodeTag] at mapped
    have indexEq : index=qi:=Option.some.inj (mapped.symm.trans qt)
    rw [indexEq] at found
    have nodeEq : node=qn:=Option.some.inj (found.symm.trans qa)
    rw [nodeEq];exact qh
  have sourceFinalLive : machine.memory.live.find? (fun row=>row.1==physical.id)=
      some (physical.id,{physicalSource.entry with allocation:=Q.allocation}) := by
    rw [postLive];exact MemoryCopyBridge.live_lookup_replaced source.memory physical.id _
  rw [currentPointer] at parentIssued parentBinding edge
  have sourceOlder : tracker.global.nextPointerTag.value<output.tag.value := by
    rw [tag]
    apply UInt64.lt_iff_toNat_lt.mpr
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have preparedModel:=CurrentCallResourcePreparedEntry.model model frames
  have sourceUser : source.user=prepared.user := by
    change {prepared.user with payload:={prepared.user.payload with ghost:=false}}=prepared.user
    rw [←preparedModel.ghostOff]
  have mode : tracker.retagMode=.Default := by
    obtain ⟨old,found,mode⟩:=model.defaultTracker
    have eq : old=tracker:=Option.some.inj (found.symm.trans enabled)
    simpa only [eq] using mode
  have modelAfter : DuplicatePrefixCallModel.Model options remaining span machine := by
    refine ⟨model.debugOff,model.preciseOff,model.implicitOff,?_,?_,⟨⟨output.global,tracker.retagMode⟩,tracked,mode⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
    · rw [userEq];rfl
    · rw [userEq];exact preparedModel.shallow
    · rw [raceEq];exact model.noDataRace
    · rw [userEq];exact preparedModel.noBackend
    · rw [userEq];exact preparedModel.metadata
    · rw [threadsEq];exact preparedModel.fixedScheduler
    · rw [userEq,sourceUser];exact preparedModel.unchecked
    · rw [userEq,sourceUser];exact preparedModel.noGc
  obtain ⟨globalEq,boolGrowthRaw,boolCapacity⟩:=operation_facts current run sourceFrame freshAfter
    (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact rootsDistinct) (by change P.allocation.extra.nodes.size+1<65536;rw [alloc];change (slot.after tracker.global.nextPointerTag).nodes.size+1<65536;omega) physical.offset rfl output child actual witness tag constructor constructorPresent rootTag
  have boolGrowth : Q.allocation.extra.nodes.size≤current.allocation.extra.nodes.size+1 := by rw [extra];exact boolGrowthRaw
  have userPrepared : machine.user=prepared.user:=userEq.trans sourceUser
  have typesEq : machine.user.payload.payload.user.types=initial.user.payload.payload.user.types := by rw [userPrepared];rfl
  have addressesEq : machine.user.addresses=initial.user.addresses := by rw [userPrepared];rfl
  have extrasEq : machine.user.payload.payload.user.runtime.extras=initial.user.payload.payload.user.runtime.extras := by rw [userPrepared];rfl
  have counterEq : output.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 := by
    have firstCounter : next.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 := by
      change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat=_
      exact GenericFunctionEntryNumerics.successor_value _ _
    have secondCounter : output.global.nextPointerTag.value.toNat=next.global.nextPointerTag.value.toNat+1 := by
      rw [globalEq]
      change (TypedRetagEmpty.successorTag next.global.nextPointerTag freshAfter).value.toNat=_
      exact GenericFunctionEntryNumerics.successor_value _ _
    omega
  have flagsEq : output.global.protectedTags=(tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert output.tag .StrongProtector := by rw [globalEq,tag];rfl
  have rootsEq : output.global.rootPointerTags=tracker.global.rootPointerTags := by rw [globalEq];rfl
  have trackedEq : output.global.trackedPointerTags=tracker.global.trackedPointerTags := by rw [globalEq];rfl
  have bytesEq : Q.allocation.byteSize=current.allocation.byteSize := by
    calc
      Q.allocation.byteSize=Q.allocation.extra.locations.size:=Q.issued.capability.treeExtent.symm
      _=current.allocation.extra.locations.size:=by rw [extra];exact boolCapacity
      _=current.allocation.byteSize:=current.issued.capability.treeExtent
  have lengthEq : Q.allocation.len=current.allocation.len := by
    rw [Q.issued.capability.extent,bytesEq]
    exact current.issued.capability.extent.symm
  have qGrowth:=growth
  have allGrowth : Q.allocation.extra.nodes.size≤B.allocation.extra.nodes.size+2 := by
    change Q.allocation.extra.nodes.size≤P.allocation.extra.nodes.size+1 at boolGrowth
    rw [alloc] at boolGrowth
    change Q.allocation.extra.nodes.size≤(slot.after tracker.global.nextPointerTag).nodes.size+1 at boolGrowth
    omega
  have facts : Facts initial tracker frames physical.id physical.entry physical.base machine output.global output.tag
      {physicalSource.entry with allocation:=Q.allocation} B.allocation Q.allocation 2 2 := {
    user:=userPrepared,types:=typesEq,origins:=by rw [typesEq];exact origins,addresses:=addressesEq,extras:=extrasEq,
    cached:=by rw [addressesEq];exact physical.cachedBase,sourceRuntime:=runtimeQ,
    sourceSize:=by change Q.allocation.byteSize=physical.entry.allocation.byteSize;rw [bytesEq];change P.allocation.byteSize=_;rw [alloc];rfl
    sourceLen:=by change Q.allocation.len=physical.entry.allocation.len;rw [lengthEq];change P.allocation.len=_;rw [alloc];rfl
    sourceKind:=rfl,sourceGrowth:=by change Q.allocation.extra.nodes.size≤physical.entry.allocation.extra.nodes.size+2;have rhs:=congrArg (fun a : Allocation Provenance BorrowTree=>a.extra.nodes.size) allocation;omega
    boolGrowth:=allGrowth,counter:=counterEq,flags:=flagsEq,rootTags:=rootsEq,trackedTags:=trackedEq}
  exact ⟨output,child,machine,_,nextData,nextOwner,Q,entered,tracked,(by rw [pointerQ];rfl),(by rw [pointerQ];rfl),sourceOlder,runtimeQ,rootsQ,shortQ,parentIssued,parentBinding,edge,rfl,rfl,
    CurrentCallEmptyLiveFrames.installed_eq effect remaining span root count {} _ physical.id output.tag rfl,sourceHidden,
    modelAfter,threadsEq,⟨scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady⟩,
    ⟨{physicalSource.entry with allocation:=Q.allocation},sourceFinalLive,sourceFinal,facts⟩,node,nodeAt,nodeTag,leaf,hidden,activity⟩

/-- The different-allocation live wildcard branch retains the original Bool allocation. -/
theorem different (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span initial)
    (enabled : initial.borrowTracker=some tracker)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness initial frames)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow initial place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow initial tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (sourceId : AllocId) (different : sourceId≠physical.id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : initial.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry))
    (sourceBase : UInt64)
    (sourceCached : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,sourceBase⟩)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (sourceRoom : entry.allocation.extra.nodes.size+1≤4294967295)
    (start count : UInt64) (nonzero : sourceBase+start≠0)
    (addressMode : initial.user.addresses.provenanceMode≠.strict)
    (inverse : WildcardGeneralHitReborrow.Geometry initial.user.addresses.intToPtrMap (sourceBase+start) sourceBase sourceId entry.allocation.byteSize)
    (exposed : initial.user.addresses.exposed.contains sourceId=true)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins initial.user.payload.payload.user.types) :
    ∃(output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (machine : Before) (frame : CompilerFrameContext.ActualFrame),
    ∃nextData nextOwner,∃Q : UniformWindow machine ⟨output.global,tracker.retagMode⟩ nextData nextOwner physical.id physical.offset.toNat 1 .ret,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes (sourceBase+start)))) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=.ok () (Storage.withCurrent frames frame machine) ∧
      machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      Q.pointer.grant=child ∧Q.pointer.value.provenance=.concrete physical.id output.tag ∧
      tracker.global.nextPointerTag.value<output.tag.value ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra output.global ∧
      Q.allocation.extra.roots.toList.Nodup ∧Q.allocation.extra.nodes.size<65536 ∧
      SpatialDelegation machine ⟨output.global,tracker.retagMode⟩ physical.id Q.allocation Q.precise.completion B.pointer.grant ∧
      PointerBinds Q.allocation B.pointer ∧
      Q.precise.completion.parents[child.toNat]?=some (some B.pointer.grant) ∧
      frame.returnPlace=.memory place ∧
      frame.extra.borrowTracker=some ((({} : FrameState).addProtector sourceId tracker.global.nextPointerTag).addProtector physical.id output.tag) ∧
      frame=PositiveRootInstalledFrame.installed (CurrentCallSpatialEntryControl.root initial frames place model.noDataRace)
        (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete sourceId tracker.global.nextPointerTag) (Size.ofBytes (sourceBase+start)))) 0 ActualReferenceMetadata.reference).imm
        count {} sourceId tracker.global.nextPointerTag physical.id output.tag ∧
      (∀index node,Q.allocation.extra.nodes.get index=some node→node.tag=tracker.global.nextPointerTag→node.isExposed=false) ∧
      DuplicatePrefixCallModel.Model options remaining span machine ∧
      machine.threads=(CurrentCallPush.preparedMachine initial frames).threads ∧
      (∃window : CurrentCallBoolScalarWrite.Window machine place,
        window.pointer=physical.pointer ∧window.id=physical.id ∧window.offset=physical.offset ∧window.entry.allocation=Q.allocation ∧
        CandidateCallBindings.WindowBinding machine window.pointer window.id window.offset.toNat 1 ∧
        CurrentCallBoolProtection.WindowReady machine window.id window.offset.toNat 1) ∧
      (∃sourceEntry,machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry) ∧
        CurrentCallEmptyEntrySourceData.Leaf sourceEntry.allocation.extra tracker.global.nextPointerTag ∧
        Facts initial tracker frames sourceId entry sourceBase machine output.global output.tag sourceEntry B.allocation Q.allocation 1 1) ∧
      ∃node,Q.allocation.extra.nodes.get child=some node ∧node.tag=output.tag ∧node.children=#[] ∧node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra child .Write physical.offset (physical.offset+1) := by
  let prepared:=CurrentCallPush.preparedMachine initial frames
  let root:=CurrentCallSpatialEntryControl.root initial frames place model.noDataRace
  let activeInput:=ScopedFrame.entered prepared tracker .FnEntry
  let fresh : tracker.global.nextPointerTag.value<18446744073709551615:=UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  let slot : WildcardHitPoolRoot.Slot entry.allocation.extra:=WildcardHitPoolRoot.factory entry.allocation.extra
    sourceRuntime.formed.allocator.pool sourceRuntime.formed.allocator.accounting (by
      have balance:=sourceRuntime.formed.allocator.accounting
      unfold GeneralBorrowFreshStagePool.Accounting at balance
      omega)
  let hit : S03WildcardEmptyClassification.Hit (DuplicatePrefixCallSpecification.imageContext options prepared tracker)
      prepared.memory prepared.user.addresses (sourceBase+start):=⟨sourceId,sourceBase,
        ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩,
        MemoryCopyBridge.live_alloc_info _ _ _ sourceLive,inverse,exposed,sourceCached,Or.inl (.live entry sourceLive True.intro)⟩
  let argument:=DuplicatePrefixSliceArgument.Argument.pointer (Pointer.new .wildcard (Size.ofBytes (sourceBase+start)))
  let effect : Effect options prepared tracker argument:=.wildcardLive (sourceBase+start) hit entry
    (slot.after tracker.global.nextPointerTag) sourceLive ⟨slot,rfl⟩
  let fn:=resultMachine effect fresh remaining span frames (firstLive root).frame {} 1 ((firstLive root).valid i1)
  let next:MachineHooks.BorrowState:=⟨(registered tracker.global {} sourceId fresh).1,.FnEntry⟩
  let source:Before:={fn with borrowTracker:=some {next with retagMode:=tracker.retagMode}}
  let sourceFrame:FrameState:=({} : FrameState).addProtector sourceId tracker.global.nextPointerTag
  have frameBorrow : (firstLive root).frame.extra.borrowTracker=some {}:=RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot initial).2 tracker enabled
  have live1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  obtain ⟨copyCtx⟩:=(DuplicatePrefixCallModel.contexts options remaining span initial model).1
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span initial model).2.2.2
  obtain ⟨copy,P,ptr,alloc,precise,run⟩:=CurrentCallEmptyOtherBool.wildcard options limits remaining span copyCtx model.debugOff model.nullComparator
    dynamicFuel validationFuel dynamicEq validationEq sourceId tracker.global sourceBase start nonzero entry
    frames (firstLive root).frame activeInput 1 ((firstLive root).valid i1) .uninit live1 cached1 (firstLive root).noClocks
    model.ghostOff model.shallow sourceCached sourceLive {} frameBorrow rfl fresh addressMode inverse exposed sourceRuntime sourceRoom
    data owner physical.id physical.offset.toNat (scopeWindow frames B) runtime different model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView rfl
  have copyStep : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallEmptyEntryControl.value options remaining span argument).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame activeInput)=.ok () (Storage.withCurrent frames
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root {}).frame fn) := copy
  let current : UniformWindow source {next with retagMode:=tracker.retagMode} data owner physical.id physical.offset.toNat 1 .ret := {P with
    issued:=by
      apply CurrentCallAllocationLicense.spatial P.issued source {next with retagMode:=tracker.retagMode} P.allocation (by exact P.present) rfl rfl rfl rfl
      · intro position root found;exact found
      · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
      · intro child parent edge;exact edge }
  have present : source.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,physical.entry) := by
    change ((initial.memory.live.filter (fun row=>row.1!=sourceId)).push
      (sourceId,{entry with allocation:=entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)})).find? (fun row=>row.1==physical.id)=_
    rw [Array.find?_push,Array.find?_filter]
    have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind => decide ((row.1!=sourceId)=true ∧ (row.1==physical.id)=true))=
        (fun row=>row.1==physical.id) := by
      funext row
      by_cases equal : row.1=physical.id
      · simp [equal,Ne.symm different]
      · simp [equal]
    rw [predicate,physical.live]
    simp [different]
  let physicalSource : CandidateCurrentBoolUninitWrite.PhysicalWindow source place:={physical with live:=present}
  have bindingSource : CandidateCallBindings.WindowBinding source physical.pointer physical.id physical.offset.toNat 1 :=
    CurrentCallBoolWindow.replace_binding initial source physical.pointer physical.id physical.offset.toNat 1 binding sourceId entry
      {entry with allocation:=entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)} sourceLive rfl rfl rfl rfl
  have readySource:=CurrentCallBoolProtection.WindowReady.transport (before:=initial) (after:=source) ready rfl
  have freshAfter : next.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value];exact tagRoom
  obtain ⟨output,child,machine,nextData,nextOwner,Q,entered,tracked,pointerQ,runtimeQ,rootsQ,shortQ,node,nodeAt,nodeTag,leaf,hidden,activity,parentIssued,parentBinding,_,edge,actual,⟨witness⟩,tag,constructor,constructorPresent,rootTag,extra,postLive,scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady,userEq,threadsEq,raceEq⟩:=
    CurrentCallEmptyLiveEntryCurrent.init_current_of_copy options limits remaining span ctx initial tracker frames place model.noDataRace stackReady model.debugOff
      argument effect {} count fn source next sourceFrame enabled rfl rfl model.ghostOff model.shallow rfl model.shallow model.noDataRace model.noBackend validationFuel validationEq copyStep
      physicalSource data owner current (pointer.trans (congrArg PointerInstance.value ptr).symm) (allocation.trans alloc.symm) run bindingSource
      (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact distinct) freshAfter
      (by change P.allocation.extra.nodes.size+1<65536;rw [alloc];exact nodeRoom)
      readySource rfl
  have oldBelow : ∀row∈current.allocation.extra.tagMapping.mapping,row.1.value.toNat<tracker.global.nextPointerTag.value.toNat := by
    intro row member
    change row∈P.allocation.extra.tagMapping.mapping at member
    rw [alloc] at member
    exact runtime.below.mapping row member
  have beforeFresh : tracker.global.nextPointerTag.value.toNat<next.global.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have absent:=CurrentCallSelectedBorrowTagOrigin.written_node_absent current run sourceFrame freshAfter
    (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact distinct)
    (by change P.allocation.extra.nodes.size+1<65536;rw [alloc];exact nodeRoom)
    physical.offset rfl output child actual witness tracker.global.nextPointerTag oldBelow beforeFresh
  have sourceHidden : ∀index node,Q.allocation.extra.nodes.get index=some node→node.tag=tracker.global.nextPointerTag→node.isExposed=false := by
    intro index node found same
    exact False.elim (absent index node (by rw [←extra];exact found) same)
  have sourceOld : CurrentCallEmptyEntrySourceData.Leaf (slot.after tracker.global.nextPointerTag) tracker.global.nextPointerTag := (quiet_source_rule "CurrentCallEmptyEntrySourceData.slot_leaf") _ slot tracker.global.nextPointerTag
      (ConcreteEmptyRuntimeEntry.counter_fresh _ _ sourceRuntime.below) (DuplicatePrefixBorrowContract.vacant_clean sourceRuntime)
  have sourceOldLive : source.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,{entry with allocation:=entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)}) :=
    MemoryCopyBridge.live_lookup_replaced prepared.memory sourceId _
  have sourceFinalLive : machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,{entry with allocation:=entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)}) := by
    rw [postLive,Array.find?_push,Array.find?_filter]
    have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind=>decide ((row.1!=physical.id)=true ∧(row.1==sourceId)=true))=
        (fun row=>row.1==sourceId) := by
      funext row
      by_cases equal : row.1=sourceId
      · simp [equal,different]
      · simp [equal]
    rw [predicate,sourceOldLive]
    simp
  have currentPointer : current.pointer=B.pointer:=ptr
  rw [currentPointer] at parentIssued parentBinding edge
  have sourceOlder : tracker.global.nextPointerTag.value<output.tag.value := by
    rw [tag]
    apply UInt64.lt_iff_toNat_lt.mpr
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have preparedModel:=CurrentCallResourcePreparedEntry.model model frames
  have sourceUser : source.user=prepared.user := by
    change {prepared.user with payload:={prepared.user.payload with ghost:=false}}=prepared.user
    rw [←preparedModel.ghostOff]
  have mode : tracker.retagMode=.Default := by
    obtain ⟨old,found,mode⟩:=model.defaultTracker
    have eq : old=tracker:=Option.some.inj (found.symm.trans enabled)
    simpa only [eq] using mode
  have modelAfter : DuplicatePrefixCallModel.Model options remaining span machine := by
    refine ⟨model.debugOff,model.preciseOff,model.implicitOff,?_,?_,⟨⟨output.global,tracker.retagMode⟩,tracked,mode⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
    · rw [userEq];rfl
    · rw [userEq];exact preparedModel.shallow
    · rw [raceEq];exact model.noDataRace
    · rw [userEq];exact preparedModel.noBackend
    · rw [userEq];exact preparedModel.metadata
    · rw [threadsEq];exact preparedModel.fixedScheduler
    · rw [userEq,sourceUser];exact preparedModel.unchecked
    · rw [userEq,sourceUser];exact preparedModel.noGc
  obtain ⟨globalEq,boolGrowthRaw,boolCapacity⟩:=operation_facts current run sourceFrame freshAfter
    (by change P.allocation.extra.roots.toList.Nodup;rw [alloc];exact distinct) (by change P.allocation.extra.nodes.size+1<65536;rw [alloc];exact nodeRoom) physical.offset rfl output child actual witness tag constructor constructorPresent rootTag
  have boolGrowth : Q.allocation.extra.nodes.size≤current.allocation.extra.nodes.size+1 := by rw [extra];exact boolGrowthRaw
  have userPrepared : machine.user=prepared.user:=userEq.trans sourceUser
  have typesEq : machine.user.payload.payload.user.types=initial.user.payload.payload.user.types := by rw [userPrepared];rfl
  have addressesEq : machine.user.addresses=initial.user.addresses := by rw [userPrepared];rfl
  have extrasEq : machine.user.payload.payload.user.runtime.extras=initial.user.payload.payload.user.runtime.extras := by rw [userPrepared];rfl
  have counterEq : output.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 := by
    have firstCounter : next.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 := by
      change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat=_
      exact GenericFunctionEntryNumerics.successor_value _ _
    have secondCounter : output.global.nextPointerTag.value.toNat=next.global.nextPointerTag.value.toNat+1 := by
      rw [globalEq]
      change (TypedRetagEmpty.successorTag next.global.nextPointerTag freshAfter).value.toNat=_
      exact GenericFunctionEntryNumerics.successor_value _ _
    omega
  have flagsEq : output.global.protectedTags=(tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert output.tag .StrongProtector := by rw [globalEq,tag];rfl
  have rootsEq : output.global.rootPointerTags=tracker.global.rootPointerTags := by rw [globalEq];rfl
  have trackedEq : output.global.trackedPointerTags=tracker.global.trackedPointerTags := by rw [globalEq];rfl
  obtain ⟨_,heldQ,_,registeredRuntime,_,freshQ⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra tracker.global {} sourceId fresh sourceRuntime
  have qBound : tracker.global.nextPointerTag.value.toNat<next.global.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have qHeld : next.global.protectedTags.contains tracker.global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    rw [heldQ]
    rfl
  have qConstruct:=S04ZeroWildcardRuntime.construct entry.allocation.extra next.global registeredRuntime tracker.global.nextPointerTag freshQ sourceRoom qBound qHeld start
  have qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tracker.global.nextPointerTag) next.global := by
    have rr:=qConstruct.2.1
    rw [slot.child tracker.global.nextPointerTag freshQ start] at rr
    exact rr
  have qGrowth : (slot.after tracker.global.nextPointerTag).nodes.size≤entry.allocation.extra.nodes.size+1 := by
    have g:=qConstruct.2.2.2
    rw [slot.child tracker.global.nextPointerTag freshQ start] at g
    exact g
  have sourceRuntimeFinal : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tracker.global.nextPointerTag) output.global := by
    rw [globalEq]
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare (slot.after tracker.global.nextPointerTag) next.global sourceFrame physical.id freshAfter qRuntime).2.2.2.1
  have allGrowth : Q.allocation.extra.nodes.size≤B.allocation.extra.nodes.size+1 := by
    change Q.allocation.extra.nodes.size≤P.allocation.extra.nodes.size+1 at boolGrowth
    rw [alloc] at boolGrowth
    exact boolGrowth
  have facts : Facts initial tracker frames sourceId entry sourceBase machine output.global output.tag
      {entry with allocation:=entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)} B.allocation Q.allocation 1 1 := {
    user:=userPrepared,types:=typesEq,origins:=by rw [typesEq];exact origins,addresses:=addressesEq,extras:=extrasEq,
    cached:=by rw [addressesEq];exact sourceCached,sourceRuntime:=sourceRuntimeFinal,
    sourceSize:=rfl,sourceLen:=rfl,sourceKind:=rfl,sourceGrowth:=qGrowth,boolGrowth:=allGrowth,
    counter:=counterEq,flags:=flagsEq,rootTags:=rootsEq,trackedTags:=trackedEq}
  exact ⟨output,child,machine,_,nextData,nextOwner,Q,entered,tracked,(by rw [pointerQ];rfl),(by rw [pointerQ];rfl),sourceOlder,runtimeQ,rootsQ,shortQ,parentIssued,parentBinding,edge,rfl,rfl,
    CurrentCallEmptyLiveFrames.installed_eq effect remaining span root count {} _ physical.id output.tag rfl,sourceHidden,
    modelAfter,threadsEq,⟨scalar,scalarPointer,scalarId,scalarOffset,scalarAllocation,scalarBinding,scalarReady⟩,
    ⟨_,sourceFinalLive,sourceOld,facts⟩,node,nodeAt,nodeTag,leaf,hidden,activity⟩
end Wildcard

end
end DuplicatePrefix.CurrentCallEmptyLiveSourceFacts
