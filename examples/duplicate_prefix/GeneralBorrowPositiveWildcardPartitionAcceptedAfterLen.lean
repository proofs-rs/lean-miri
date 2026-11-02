import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedLenFrame
import duplicate_prefix.GeneralBorrowExposedScopedAcceptedCallInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedAfterLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure Origin (s : GeneralBorrowPositiveWildcardPartitionAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedLenCallInput.Input) (stage : GeneralBorrowExposedScopedAcceptedAfterLen.Initial) : Prop where
  lenOrigin : GeneralBorrowPositiveWildcardPartitionNonzeroMachinePrefixMetadata.Origin s.toInitial updated i
  options : stage.options=s.options
  limits : stage.limits=s.limits
  remaining : stage.remaining=s.remaining
  span : stage.span=s.span
  id : stage.id=s.id
  base : stage.base=s.base
  offset : stage.offset=0
  len : stage.len=s.len
  count : stage.count=s.count
  caller : stage.caller=GeneralBorrowPositiveWildcardPartitionAcceptedLenFrame.frame i
  tracker : stage.tracker=GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i
  entry : stage.entry={i.entry with allocation:=i.entry.allocation.setExtra (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.released i)}
  parentTag : stage.parentTag=s.tracker.global.nextPointerTag
  parentIndex : stage.data.input.parent=i.first.parent
  selected : stage.selected=i.selected
  head : stage.head=i.head
  tail : stage.tail=i.tail
  slotPresent : stage.machine.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,{s.slotEntry with allocation:=updated})
  runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before stage.machine
  continuation : stage.caller.returnContinuation=.stop true
  returnPlace : stage.caller.returnPlace.toRuntimePlace=⟨.memory s.place.mplace,s.place.layout⟩
  varargs : stage.caller.vaList=#[]
  frameBorrow : stage.caller.extra.borrowTracker=some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId (GeneralBorrowPositiveWildcardPartitionFunctionState.next s.tracker s.fresh).global.nextPointerTag)
  trackNone : stage.caller.trackCallerArg=none
  relevant : 64<stage.caller.extra.userRelevance
  sourceSlot2 : stage.caller.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.count)))),some RootCompilerFacts.usizeLayout⟩
  unused : ∀ index,15≤index→index≤24→stage.caller.locals[index]?=some ⟨.dead,none⟩

theorem forms (s : GeneralBorrowPositiveWildcardPartitionAcceptedInput.Initial) :
    ∃ (updated : Allocation Provenance BorrowTree) (i : GeneralBorrowExposedScopedLenCallInput.Input)
      (stage : GeneralBorrowExposedScopedAcceptedAfterLen.Initial), ∃ installed,
      Origin s updated i stage ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
        (Storage.withCurrent #[] stage.caller stage.machine) := by
  obtain ⟨updated,i,installed,origin,call,root,post,tree,trace,rootEq,memoryEq,trackedEq,releaseDone,helperData,well,capacity,
    forestRuntime,genericRuntime,lookup,nodeTags,writeContext,writeOwned,coherent,readOwned⟩ :=
    GeneralBorrowPositiveWildcardPartitionNonzeroLenMetadata.invoke s.toInitial
  have sourceChild : GeneralBorrowExposedScopedSharedPathMetadata.child i.input
      (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.held i).global.protectedTags .VisitChildrenOfAccessed=
      GeneralBorrowExposedScopedSharedArgumentCopy.finalTree i.entry.allocation.extra i.tracker i.exprTag i.offset i.len := by
    simp only [GeneralBorrowExposedScopedSharedPathMetadata.child,i.treeEq,i.parentTagEq,i.tagEq,i.offsetEq,i.lenEq,i.protectedEq,
      GeneralBorrowExposedScopedSharedArgumentCopy.finalTree]
    rfl
  have sourceReleased : GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.released i=tree := by
    unfold GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.released
    rw [sourceChild,i.tagEq]
    exact congrArg BorrowTree.ProtectorReleaseResult.tree releaseDone
  have postTracked : post.borrowTracker=some (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i) := by
    rw [trackedEq]
    unfold GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.ended GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.held
    rw [i.tagEq]
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {i.entry with allocation:=i.entry.allocation.setExtra (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.released i)}
  have present : post.memory.live.find? (fun row=>row.1==i.id)=some (i.id,entry) := by
    rw [←sourceReleased] at lookup
    exact lookup
  have postRuntime := genericRuntime origin.frames
  have runtimeS : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span i.beforeMachine post := by
    simpa only [origin.options,origin.remaining,origin.span] using postRuntime
  have originalRuntime := GeneralBorrowPositiveWildcardPartitionNonzeroLenMetadata.runtime_trans s.options s.remaining s.span s.before i.beforeMachine post origin.runtime runtimeS
  obtain ⟨data,parentIndex,atBase,full,slotClean,vacantClean,finalTags,room,reserveFresh⟩ :=
    GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.prepare s updated i origin
  have fresh := GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.fresh s updated i origin
  have nextFresh : (ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i) fresh).global.nextPointerTag.value<18446744073709551615 := by
    exact GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.next_fresh s updated i origin
  have different : (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i).global.nextPointerTag≠
      (ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i) fresh).global.nextPointerTag := by
    have numerical:=GenericFunctionEntryNumerics.successor_value (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i).global.nextPointerTag fresh
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    change (ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i) fresh).global.nextPointerTag.value.toNat=
      (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i).global.nextPointerTag.value.toNat+1 at numerical
    omega
  have rootFrame : root=GeneralBorrowPositiveWildcardPartitionAcceptedLenFrame.frame i := rootEq
  have frameFacts : GeneralBorrowExposedScopedAcceptedControl.FrameFacts root i.input.len s.count := by
    rw [rootFrame,i.lenEq]
    exact GeneralBorrowPositiveWildcardPartitionAcceptedLenFrame.facts s.toInitial updated i origin
  have sourceSlot1 : root.locals[1]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩ := by
    rw [rootFrame,GeneralBorrowPositiveWildcardPartitionAcceptedLenFrame.keep i 1 (by decide)]
    exact origin.sourceSlot1
  have valid1 : (1 : MIR.LocalId)<root.locals.size := by rw [frameFacts.size];decide
  have sourceCell:=Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans sourceSlot1)
  have live1 : root.locals[1].value=.live (.immediate (RetagReferencePlace.sliceValue
      (config i.options (i.remaining+1) i.span).access.runtime.base
      (Pointer.new (.concrete i.id i.first.parentNode.tag) (Size.ofBytes (i.base+i.input.offset))) i.input.len ActualReferenceMetadata.reference).imm) := by
    simpa only [origin.options,origin.remaining,origin.span,origin.id,origin.parentNodeTag,origin.base,i.offsetEq,origin.offset,i.lenEq,origin.len,
      UInt64.add_zero,config,CanonicalConfigFacts.actual_access_runtime] using congrArg LocalState.value sourceCell
  have entryCapacity : entry.allocation.extra.locations.size=entry.allocation.byteSize := by
    change (GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.released i).locations.size=i.entry.allocation.byteSize
    rw [sourceReleased]
    exact capacity.trans i.allocationSize
  obtain ⟨thread,active,top⟩:=postRuntime.active
  have metadata : post.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime := by
    rw [originalRuntime.types]
    exact s.metadata
  have notConstructed : post.user.payload.payload.user.types.entries.any (·.value.ty==4)=false := by
    rw [originalRuntime.types]
    exact s.notConstructed
  let stage : GeneralBorrowExposedScopedAcceptedAfterLen.Initial := {
    options:=i.options,limits:=i.limits,remaining:=i.remaining,span:=i.span,ctx:=i.ctx,
    precise:=by rw [origin.options];exact s.preciseOff,implicitWrites:=by rw [origin.options];exact s.implicitOff,
    debug:=i.debugOff,dynamicFuel:=i.dynamicFuel,dynamic:=i.fuelEq,fuel:=i.validityFuel,validation:=i.validationEq,cmp:=i.cmp,source:=i.source,
    budget:=i.budget,dispatch:=i.dispatchFuel,caller:=root,machine:=post,id:=i.id,entry:=entry,parentTag:=i.first.parentNode.tag,
    base:=i.base,offset:=i.input.offset,len:=i.input.len,positive:=by rw [i.lenEq,origin.len];exact s.positive,
    nonzero:=by rw [i.offsetEq,origin.offset,origin.base,UInt64.add_zero];exact s.nonzero,
    signedFits:=by rw [i.lenEq,origin.len];exact s.signedFits,
    bounds:=by change i.input.offset.toNat+i.input.len.toNat≤i.entry.allocation.byteSize.bytes.toNat;rw [i.offsetEq,origin.offset,i.lenEq,origin.len,origin.bufferSize];simpa using s.bounds,
    capacity:=entryCapacity,cachedAddress:=by rw [originalRuntime.addresses,origin.id,origin.base];exact s.cachedAddress,
    present:=present,tracker:=GeneralBorrowPositiveWildcardPartitionAcceptedDefaultData.tracker i,tracked:=postTracked,mode:=by
      change i.tracker.retagMode=.Default
      exact i.defaultMode,
    fresh:=fresh,selected:=i.selected,head:=i.head,tail:=i.tail,data:=data,atBase:=atBase,full:=full,
    rangePositive:=by rw [data.offsetEq,data.lenEq];exact i.rangePositive,
    vacantClean:=vacantClean,nextFresh:=nextFresh,futureFresh:=reserveFresh,different:=different,room:=room,
    valid1:=valid1,live1:=live1,cached1:=congrArg LocalState.layout sourceCell,count:=s.count,countPositive:=s.countPositive,
    within:=by rw [i.lenEq,origin.len];exact s.within,frameFacts:=frameFacts,
    ghost:=postRuntime.ghost,shallow:=postRuntime.shallow,race:=postRuntime.race,backend:=postRuntime.backend,metadata:=metadata,notConstructed:=notConstructed,
    thread:=thread,active:=active,top:=top,unchecked:=postRuntime.unchecked,noGc:=postRuntime.noGc,fixed:=postRuntime.fixed }
  have sourceSlots (index : Nat) (different : index≠11) : root.locals[index]?=i.caller.locals[index]? := by
    rw [rootFrame]
    exact GeneralBorrowPositiveWildcardPartitionAcceptedLenFrame.keep i index different
  have slotPresent : post.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,{s.slotEntry with allocation:=updated}) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_other i.beforeMachine.memory i.id s.slotId i.entry _ tree
      (by rw [origin.id];exact s.separate) origin.slotPresent
  have continuation : root.returnContinuation=.stop true := by
    rw [rootFrame]
    exact origin.rootContinuation
  have returnPlace : root.returnPlace.toRuntimePlace=⟨.memory s.place.mplace,s.place.layout⟩ := by
    rw [rootFrame]
    exact origin.rootReturn
  have varargs : root.vaList=#[] := by rw [rootFrame];exact origin.rootVa
  have frameBorrow : root.extra.borrowTracker=some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId (GeneralBorrowPositiveWildcardPartitionFunctionState.next s.tracker s.fresh).global.nextPointerTag) := by
    rw [rootFrame]
    exact origin.frameBorrow
  have trackNone : root.trackCallerArg=none := by rw [rootFrame];exact origin.trackNone
  have relevant : 64<root.extra.userRelevance := by rw [rootFrame];exact origin.relevant
  have stageOrigin : Origin s updated i stage :=
    ⟨origin,origin.options,origin.limits,origin.remaining,origin.span,origin.id,origin.base,i.offsetEq.trans origin.offset,i.lenEq.trans origin.len,rfl,
      rootFrame,rfl,rfl,origin.parentNodeTag,parentIndex,rfl,rfl,rfl,slotPresent,originalRuntime,continuation,returnPlace,varargs,frameBorrow,trackNone,relevant,
      (sourceSlots 2 (by decide)).trans origin.countSlot2,fun index low high=>(sourceSlots index (by omega)).trans (origin.unused index low high)⟩
  exact ⟨updated,i,stage,installed,stageOrigin,call,trace⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedAfterLen
