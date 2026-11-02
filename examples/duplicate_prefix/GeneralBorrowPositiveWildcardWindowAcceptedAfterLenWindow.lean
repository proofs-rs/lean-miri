import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedAfterLen
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowNonzeroLenWindow
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedDefaultData
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedLenFrame
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableAcceptedCallInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedAfterLenWindow
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Origin := GeneralBorrowPositiveWildcardWindowAcceptedAfterLen.Origin

theorem forms (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) :
    ∃ (updated : Allocation Provenance BorrowTree) (i : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input)
      (stage : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Initial), ∃ installed,
      Origin s updated i stage ∧ i.first.offset=s.offset ∧ i.first.len=s.len ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
        (Storage.withCurrent #[] stage.caller stage.machine) := by
  obtain ⟨updated,i,installed,sourceOrigin,call,root,post,tree,trace,rootEq,memoryEq,trackedEq,releaseDone,helperData,well,capacity,
    forestRuntime,genericRuntime,lookup,nodeTags,writeContext,writeOwned,coherent,readOwned,targetWritable⟩ :=
    GeneralBorrowPositiveWildcardWindowNonzeroLenWindow.invoke s.toInitial
  let origin := sourceOrigin.toOrigin
  have sourceChild : GeneralBorrowExposedScopedSharedPathMetadata.child i.input
      (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.held i).global.protectedTags .VisitChildrenOfAccessed=
      GeneralBorrowExposedScopedSharedArgumentCopy.finalTree i.entry.allocation.extra i.tracker i.exprTag i.offset i.len := by
    simp only [GeneralBorrowExposedScopedSharedPathMetadata.child,i.treeEq,i.parentTagEq,i.tagEq,i.offsetEq,i.lenEq,i.protectedEq,
      GeneralBorrowExposedScopedSharedArgumentCopy.finalTree]
    rfl
  have sourceReleased : GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.released i=tree := by
    unfold GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.released
    rw [sourceChild,i.tagEq]
    exact congrArg BorrowTree.ProtectorReleaseResult.tree releaseDone
  have postTracked : post.borrowTracker=some (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker i) := by
    rw [trackedEq]
    unfold GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.ended GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.held
    rw [i.tagEq]
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {i.entry with allocation:=i.entry.allocation.setExtra (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.released i)}
  have present : post.memory.live.find? (fun row=>row.1==i.id)=some (i.id,entry) := by
    rw [←sourceReleased] at lookup
    exact lookup
  have postRuntime := genericRuntime origin.frames
  have runtimeS : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span i.beforeMachine post := by
    simpa only [origin.options,origin.remaining,origin.span] using postRuntime
  have originalRuntime := GeneralBorrowPositiveWildcardWindowNonzeroLenMetadata.runtime_trans s.options s.remaining s.span s.before i.beforeMachine post origin.runtime runtimeS
  obtain ⟨data,parentIndex,offsetEq,lenEq,slotClean,vacantClean,finalTags,room,reserveFresh⟩ :=
    GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.prepare s updated i origin
  have fresh := GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.fresh s updated i origin
  have nextFresh : (ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker i) fresh).global.nextPointerTag.value<18446744073709551615 := by
    exact GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.next_fresh s updated i origin
  have different : (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker i).global.nextPointerTag≠
      (ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker i) fresh).global.nextPointerTag := by
    have numerical:=GenericFunctionEntryNumerics.successor_value (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker i).global.nextPointerTag fresh
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    change (ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker i) fresh).global.nextPointerTag.value.toNat=
      (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker i).global.nextPointerTag.value.toNat+1 at numerical
    omega
  have rootFrame : root=GeneralBorrowPositiveWildcardWindowAcceptedLenFrame.frame i := rootEq
  have frameFacts : GeneralBorrowExposedScopedAcceptedControl.FrameFacts root i.input.len s.count := by
    rw [rootFrame,i.lenEq]
    exact GeneralBorrowPositiveWildcardWindowAcceptedLenFrame.facts s.toInitial updated i origin
  have sourceSlot1 : root.locals[1]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩ := by
    rw [rootFrame,GeneralBorrowPositiveWildcardWindowAcceptedLenFrame.keep i 1 (by decide)]
    exact origin.sourceSlot1
  have valid1 : (1 : MIR.LocalId)<root.locals.size := by rw [frameFacts.size];decide
  have sourceCell:=Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans sourceSlot1)
  have live1 : root.locals[1].value=.live (.immediate (RetagReferencePlace.sliceValue
      (config i.options (i.remaining+1) i.span).access.runtime.base
      (Pointer.new (.concrete i.id i.first.parentNode.tag) (Size.ofBytes (i.base+i.input.offset))) i.input.len ActualReferenceMetadata.reference).imm) := by
    simpa only [origin.options,origin.remaining,origin.span,origin.id,origin.parentNodeTag,origin.base,i.offsetEq,origin.offset,i.lenEq,origin.len,
      UInt64.add_zero,config,CanonicalConfigFacts.actual_access_runtime] using congrArg LocalState.value sourceCell
  have entryCapacity : entry.allocation.extra.locations.size=entry.allocation.byteSize := by
    change (GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.released i).locations.size=i.entry.allocation.byteSize
    rw [sourceReleased]
    exact capacity.trans i.allocationSize
  obtain ⟨thread,active,top⟩:=postRuntime.active
  have metadata : post.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime := by
    rw [originalRuntime.types]
    exact s.metadata
  have notConstructed : post.user.payload.payload.user.types.entries.any (·.value.ty==4)=false := by
    rw [originalRuntime.types]
    exact s.notConstructed
  let stage : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Initial := {
    options:=i.options,limits:=i.limits,remaining:=i.remaining,span:=i.span,ctx:=i.ctx,
    precise:=by rw [origin.options];exact s.preciseOff,implicitWrites:=by rw [origin.options];exact s.implicitOff,
    debug:=i.debugOff,dynamicFuel:=i.dynamicFuel,dynamic:=i.fuelEq,fuel:=i.validityFuel,validation:=i.validationEq,cmp:=i.cmp,source:=i.source,
    budget:=i.budget,dispatch:=i.dispatchFuel,caller:=root,machine:=post,id:=i.id,entry:=entry,parentTag:=i.first.parentNode.tag,
    base:=i.base,offset:=i.input.offset,len:=i.input.len,positive:=by rw [i.lenEq,origin.len];exact s.positive,
    nonzero:=by rw [i.offsetEq,origin.offset,origin.base];exact GeneralBorrowPositiveWildcardWindowInputGeometry.nonzero s.toBase,
    signedFits:=by rw [i.lenEq,origin.len];exact s.signedFits,
    bounds:=by change i.input.offset.toNat+i.input.len.toNat≤i.entry.allocation.byteSize.bytes.toNat;rw [i.offsetEq,origin.offset,i.lenEq,origin.len,origin.bufferSize];exact GeneralBorrowPositiveWildcardWindowInputGeometry.byteBounds s.toBase,
    capacity:=entryCapacity,cachedAddress:=by rw [originalRuntime.addresses,origin.id,origin.base];exact s.cachedAddress,
    present:=present,tracker:=GeneralBorrowPositiveWildcardWindowAcceptedDefaultData.tracker i,tracked:=postTracked,mode:=by
      change i.tracker.retagMode=.Default
      exact i.defaultMode,
    fresh:=fresh,selected:=i.selected,head:=i.head,tail:=i.tail,data:=data,
    rangePositive:=by rw [data.offsetEq,data.lenEq];exact i.rangePositive,
    vacantClean:=vacantClean,nextFresh:=nextFresh,futureFresh:=reserveFresh,different:=different,room:=room,
    valid1:=valid1,live1:=live1,cached1:=congrArg LocalState.layout sourceCell,count:=s.count,countPositive:=s.countPositive,
    within:=by rw [i.lenEq,origin.len];exact s.within,frameFacts:=frameFacts,
    ghost:=postRuntime.ghost,shallow:=postRuntime.shallow,race:=postRuntime.race,backend:=postRuntime.backend,metadata:=metadata,notConstructed:=notConstructed,
    thread:=thread,active:=active,top:=top,unchecked:=postRuntime.unchecked,noGc:=postRuntime.noGc,fixed:=postRuntime.fixed }
  have sourceSlots (index : Nat) (different : index≠11) : root.locals[index]?=i.caller.locals[index]? := by
    rw [rootFrame]
    exact GeneralBorrowPositiveWildcardWindowAcceptedLenFrame.keep i index different
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
  have frameBorrow : root.extra.borrowTracker=some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId (GeneralBorrowPositiveWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag) := by
    rw [rootFrame]
    exact origin.frameBorrow
  have trackNone : root.trackCallerArg=none := by rw [rootFrame];exact origin.trackNone
  have relevant : 64<root.extra.userRelevance := by rw [rootFrame];exact origin.relevant
  have stageOrigin : Origin s updated i stage :=
    ⟨origin,origin.options,origin.limits,origin.remaining,origin.span,origin.id,origin.base,i.offsetEq.trans origin.offset,i.lenEq.trans origin.len,rfl,
      rootFrame,rfl,rfl,origin.parentNodeTag,parentIndex,rfl,rfl,rfl,slotPresent,originalRuntime,continuation,returnPlace,varargs,frameBorrow,trackNone,relevant,
      (sourceSlots 2 (by decide)).trans origin.countSlot2,fun index low high=>(sourceSlots index (by omega)).trans (origin.unused index low high)⟩
  exact ⟨updated,i,stage,installed,stageOrigin,sourceOrigin.firstOffset,sourceOrigin.firstLen,call,trace⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedAfterLenWindow
