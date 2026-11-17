import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFnEntryMapping
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFnEntryNode
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowNonzeroSharedStage
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFinalState
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowVacantClean
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableLenHelperResources
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableLenCallInput
import duplicate_prefix.GeneralBorrowForestSharedExpressionRuntime
import duplicate_prefix.LenPushFacts
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowNonzeroMachinePrefixMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency Miri.DataStructures
open CanonicalConfigFacts ActualReferenceContext ReferenceBorrowDriver
open GeneralBorrowPositiveConcreteWindowNonzeroInput GeneralBorrowFreshMetadataChildShared
open LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure Origin {profileMode : ProfileMode} (s : InitialFor profileMode) (updated : Allocation Provenance BorrowTree)
    (input : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode) : Prop where
  options : input.options=s.options
  limits : input.limits=s.limits
  remaining : input.remaining=s.remaining
  span : input.span=s.span
  id : input.id=s.id
  base : input.base=s.base
  offset : input.offset=s.offset
  len : input.len=s.len
  target : input.first.parent=GeneralBorrowFreshMetadataChildMutable.index s.data.input
  sourceTag : input.first.parentTag=s.tracker.global.nextPointerTag
  rootContinuation : input.caller.returnContinuation=.stop true
  rootReturn : input.caller.returnPlace.toRuntimePlace=⟨.memory s.place.mplace,s.place.layout⟩
  rootVa : input.caller.vaList=#[]
  frameBorrow : input.caller.extra.borrowTracker=some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag)
  size : input.caller.locals.size=25
  allImmediate : CopyHelperCleanup.AllImmediate input.caller
  slot0 : input.caller.locals[0]?=some ⟨.live (.immediate .uninit),none⟩
  slot7 : input.caller.locals[7]?=some ⟨.live (.immediate .uninit),none⟩
  slot8 : input.caller.locals[8]?=some ⟨.live (.immediate .uninit),none⟩
  slot9 : input.caller.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.count)))),some RootCompilerFacts.usizeLayout⟩
  slot10 : input.caller.locals[10]?=some ⟨.live (.immediate .uninit),none⟩
  slot13 : input.caller.locals[13]?=some ⟨.live (.immediate .uninit),none⟩
  slotPresent : input.beforeMachine.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,{s.slotEntry with allocation:=updated})
  slotTree : updated.extra=PhysicalMachineWrite.slotTree s.slotRoot (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag 1 true
  slotSize : updated.byteSize=Size.ofBytes 1
  slotLen : updated.len=1
  slotMask : updated.initializationMask=InitMask.new (Size.ofBytes 1) false
  slotProvenance : updated.provenanceMap=ProvenanceMap.new
  slotBytes : AllocationCopy.snapshot updated=AllocationCopy.snapshot s.slotEntry.allocation
  slotMutable : updated.mutability=.Mut
  runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before input.beforeMachine
  frames : input.frames=#[]
  tracker : input.tracker=expressionTracker s.toBase
  firstTree : input.first.tree=GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
  parentNodeTag : input.first.parentNode.tag=s.tracker.global.nextPointerTag
  bufferSize : input.entry.allocation.byteSize=s.entry.allocation.byteSize
  bufferLen : input.entry.allocation.len=s.entry.allocation.len
  bufferMask : input.entry.allocation.initializationMask=s.entry.allocation.initializationMask
  bufferProvenance : input.entry.allocation.provenanceMap=s.entry.allocation.provenanceMap
  bufferMutable : input.entry.allocation.mutability=s.entry.allocation.mutability
  bufferBytes : AllocationCopy.snapshot input.entry.allocation=AllocationCopy.snapshot s.entry.allocation
  sourceSlot1 : input.caller.locals[1]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩
  countSlot2 : input.caller.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.count)))),some RootCompilerFacts.usizeLayout⟩
  unused : ∀ i,15≤i→i≤24→input.caller.locals[i]?=some ⟨.dead,none⟩
  trackNone : input.caller.trackCallerArg=none
  relevant : 64<input.caller.extra.userRelevance
  expressionTag : input.exprTag=(held s.toBase).global.nextPointerTag
  firstNewTag : input.first.newTag=(held s.toBase).global.nextPointerTag
  firstTags : input.firstTags=(held s.toBase).global.protectedTags
  selected : input.selected=s.selected
  head : input.head=s.head
  tail : input.tail=s.extraRoots

  firstOffset : input.first.offset=s.offset
  firstLen : input.first.len=s.len

theorem forms {profileMode : ProfileMode} (s : InitialFor profileMode) :
    ∃ (updated : Allocation Provenance BorrowTree) (input : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode), ∃ installed,
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
        (Storage.withCurrent #[] input.caller input.beforeMachine) ∧ Origin s updated input := by
  obtain ⟨installed,frame,caller,exprMachine,updated,first,call,prefixTrace,frameFacts,shape,ready,⟨valid12,callerEq⟩,
    firstTree,firstParentTag,firstNewTag,firstParent,firstProtected,firstOffset,firstLen,⟨firstRaw,firstSupport⟩,exprMachineEq,
    slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ := GeneralBorrowPositiveConcreteWindowNonzeroSharedStage.enters s
  let tracker := held s.toBase
  let beforeExpr := RootZeroCompleteState.tick s.options s.remaining s.span
    (GenericFunctionEntryState.enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated)
  let buffer := {s.entry with allocation:=s.entry.allocation.setExtra (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len)}
  let exprTree := GeneralBorrowExposedScopedSharedPathMetadata.child first tracker.global.protectedTags .VisitChildrenOfAccessed
  let exprEntry := {buffer with allocation:=buffer.allocation.setExtra exprTree}
  let exprTracker := expressionTracker s.toBase
  let callMachine := PtrMetadataReturn.accountedMachine s.options s.remaining s.span exprMachine
  have initialBounds := GeneralBorrowPositiveConcreteWindowInputGeometry.treeBounds s.toBase
  have finalState := GeneralBorrowPositiveConcreteWindowFinalState.build s.toBase
  have firstState : GeneralBorrowStructuralHistoryState.State first.tree := by rw [firstTree];exact finalState.1
  have firstSize : first.tree.locations.size=s.entry.allocation.extra.locations.size := by rw [firstTree];exact finalState.2.1
  have firstPositive : first.offset.toNat<(first.offset+first.len).toNat := by
    rw [firstOffset,firstLen]
    exact GeneralBorrowPositiveConcreteWindowInputGeometry.positiveEnd s.toBase
  have firstClean : GeneralBorrowGcVacantClean.VacantClean first.tree := by
    rw [firstTree]
    exact GeneralBorrowPositiveConcreteWindowVacantClean.preserves s.toBase s.vacantClean
  have rootHelperDifferent : s.tracker.global.nextPointerTag≠helperTag s.toBase := by
    have one := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
    have two := GenericFunctionEntryNumerics.successor_value (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag s.slotFresh
    have three := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag s.sharedFresh
    change (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+1 at one
    change tracker.global.nextPointerTag.value.toNat=(GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at two
    change (helperTag s.toBase).value.toNat=tracker.global.nextPointerTag.value.toNat+1 at three
    intro same
    have equal:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  have helperFreshAtFirst : GeneralBorrowTagMap.Fresh first.tree.tagMapping (helperTag s.toBase) := by
    rw [firstTree]
    change GeneralBorrowTagMap.Fresh (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len).tagMapping (helperTag s.toBase)
    rw [GeneralBorrowPositiveConcreteWindowFnEntryMapping.source s.toBase]
    exact GeneralBorrowFreshMetadataChildAllocator.fresh_push s.entry.allocation.extra.tagMapping s.tracker.global.nextPointerTag (helperTag s.toBase)
      (GeneralBorrowFreshMetadataChildMutable.index s.data.input) s.entry.allocation.extra.tagMapping.deassigned s.helperMapFresh rootHelperDifferent
  have expressionUnheld : tracker.global.protectedTags.contains first.newTag=false := by
    rw [firstNewTag]
    exact GenericFunctionEntryNumerics.expression_unheld s.tracker s.fresh s.slotFresh s.expressionUnheld
  obtain ⟨helper,helperTree,helperParentTag,helperNewTag,helperParent,helperProtected,helperOffset,helperLen,helperPositive,
    helperClean,helperSize,parentNodeTag,helperExprUnheld,helperRaw,helperNodeTags⟩ :=
    GeneralBorrowExposedScopedInactiveWritableLenHelperResources.build_mode first tracker s.sharedFresh firstNewTag s.selected s.head s.extraRoots firstRaw firstState firstClean firstPositive
      helperFreshAtFirst (by have growth:=finalState.2.2;have room:=s.nodeRoom;rw [firstTree];change (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree _ _ _ _ _).nodes.size+2<65536;omega) expressionUnheld
  have exprTreeEq : exprTree=(GeneralBorrowForestMixedShared.child buffer.allocation.extra tracker.global.protectedTags s.tracker.global.nextPointerTag tracker.global.nextPointerTag false s.offset s.len .VisitChildrenOfAccessed).tree := by
    simp only [exprTree,GeneralBorrowExposedScopedSharedPathMetadata.child,firstTree,firstParentTag,firstNewTag,firstProtected,firstOffset,firstLen,GeneralBorrowForestMixedShared.child,GeneralBorrowForestMixedShared.read]
    rfl
  have machineCanonical : exprMachine=GeneralBorrowForestSharedExpressionRuntime.machine beforeExpr tracker s.sharedFresh s.id buffer exprTree := by
    rw [exprMachineEq,exprTreeEq]
    rfl
  have runtime := GeneralBorrowPositiveConcreteWindowFunctionRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
    s.slotFresh s.slotId s.slotEntry s.slotRoot updated s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed
  have exprRuntime := GeneralBorrowForestSharedExpressionRuntime.facts s.options s.remaining s.span s.before beforeExpr tracker s.sharedFresh s.id buffer exprTree runtime
  rw [←machineCanonical] at exprRuntime
  have callRuntime := exprRuntime.2
  have exprFound : exprMachine.memory.live.find? (fun row=>row.1==s.id)=some (s.id,exprEntry) := by
    rw [machineCanonical]
    exact MemoryCopyBridge.live_lookup_replaced _ s.id _
  have callFound : callMachine.memory.live.find? (fun row=>row.1==s.id)=some (s.id,exprEntry) := exprFound
  have helperTreeEq : helper.tree=exprEntry.allocation.extra := helperTree
  have exprCapacity : exprEntry.allocation.extra.locations.size=exprEntry.allocation.byteSize := by
    change exprTree.locations.size=s.entry.allocation.byteSize
    change (GeneralBorrowExposedScopedSharedPathMetadata.child first tracker.global.protectedTags .VisitChildrenOfAccessed).locations.size=_
    rw [←helperTree,helperSize,firstSize,s.bufferSize]
    exact congrArg Size.ofBytes s.allocationCapacity
  have callerValid : 11<caller.locals.size := by rw [frameFacts.size];decide
  have sourceValid : 12<caller.locals.size := by rw [frameFacts.size];decide
  have callCell := Option.some.inj ((Array.getElem?_eq_getElem callerValid).symm.trans frameFacts.slot11)
  have exprCell := Option.some.inj ((Array.getElem?_eq_getElem sourceValid).symm.trans frameFacts.slot12)
  let helperCaller := cachedCaller caller callerValid
  let destination := (LocalPlaces.localRuntimePlace 0 helperCaller 11 RootCompilerFacts.usizeLayout).stackView
  let state := Storage.withCurrent #[] helperCaller callMachine
  obtain ⟨thread,threadActive,threadCache⟩ := callRuntime.active
  have top : FrameRelevance.top (LenPush.pushed s.options.userRelevantCrates state destination).stack thread.topUserRelevantFrame=some 0 := by
    simp [FrameRelevance.top,threadCache]
  have current : (LenPush.pushed s.options.userRelevantCrates state destination).stack.frames[0]?=some helperCaller := by
    simp [LenPush.pushed,state,Storage.withCurrent]
  have postMetadata : (EvalProjectionMachine.arrays.get (LenPush.completed s.options.userRelevantCrates state destination helperCaller)).metadata=PreparedReflection.actual.runtime := by
    change (LenPushFacts.posted s.options s.remaining s.span #[] helperCaller exprMachine helperCaller).user.payload.payload.user.types.metadata=_
    rw [LenPushFacts.types_eq,exprRuntime.1.types];exact s.metadata
  have postNotConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed s.options.userRelevantCrates state destination helperCaller)).entries.any (·.value.ty==4)=false := by
    change ((LenPushFacts.posted s.options s.remaining s.span #[] helperCaller exprMachine helperCaller).user.payload.payload.user.types.entries.any (·.value.ty==4))=false
    rw [LenPushFacts.types_eq,exprRuntime.1.types];exact s.notConstructed
  have slotFoundBefore : beforeExpr.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,{s.slotEntry with allocation:=updated}) := by
    unfold beforeExpr RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact MemoryCopyBridge.live_lookup_replaced _ s.slotId _
  have slotFound : exprMachine.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,{s.slotEntry with allocation:=updated}) := by
    rw [machineCanonical]
    exact StackPopRelease.lookup_commit_other beforeExpr.memory s.id s.slotId buffer _ exprTree s.separate slotFoundBefore
  have installedMetadata := PositiveRootInstalledFrame.metadata (RawRootInvocation.root s.before s.place s.race)
    (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm s.count {} s.id s.tracker.global.nextPointerTag s.slotId
    (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag
  have continuation : caller.returnContinuation=.stop true := frameFacts.continuation.trans (shape.continuation.trans installedMetadata.2.2.2.1)
  have returnPlace : caller.returnPlace.toRuntimePlace=⟨.memory s.place.mplace,s.place.layout⟩ := by
    rw [frameFacts.returnPlace,shape.returnPlace,installedMetadata.2.2.2.2.1]
    rfl
  have va : caller.vaList=#[] := by rw [frameFacts.varargs,shape.vaList,installedMetadata.2.2.2.2.2.1];rfl
  have borrowed : caller.extra.borrowTracker=some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag) := by
    rw [frameFacts.extra]
    exact ready.borrowed
  have parentNodeTag : first.parentNode.tag=s.tracker.global.nextPointerTag := by
    obtain ⟨node,present,tag,_⟩:=GeneralBorrowPositiveConcreteWindowFnEntryNode.source s.toBase
    have here : first.tree.nodeAt first.parent=some node := by rw [firstTree,firstParent];exact present
    have same := Option.some.inj (first.parentPresent.symm.trans here)
    rw [same]
    exact tag
  have keepExpr (i : Nat) (different : i≠12) : caller.locals[i]?=frame.locals[i]? := by
    rw [callerEq]
    simp [GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different]
  let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
  have originalUnused (i : Nat) (low : 15≤i) (high : i≤24) :
      (PositiveRootInstalledFrame.installed (RawRootInvocation.root s.before s.place s.race) adjusted s.count {} s.id s.tracker.global.nextPointerTag s.slotId
        (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag).locals[i]?=some ⟨.dead,none⟩ := by
    have known := PositiveRootInstalledFrame.slot_option (RawRootInvocation.root s.before s.place s.race)
      (RawRootInvocation.locals s.before s.place s.race) adjusted s.count {} s.id s.tracker.global.nextPointerTag s.slotId
      (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag ⟨i,by omega⟩
    have h14 : 14≠i := by omega
    have h13 : 13≠i := by omega
    have h6 : 6≠i := by omega
    have h0 : 0≠i := by omega
    have h2 : 2≠i := by omega
    have h1 : 1≠i := by omega
    simpa only [adjusted,h14,h13,h6,h0,h2,h1,Fin.val_mk,or_self,ite_false] using known
  have unused (i : Nat) (low : 15≤i) (high : i≤24) : caller.locals[i]?=some ⟨.dead,none⟩ := by
    rw [keepExpr i (by omega),shape.keep i (by omega)]
    exact originalUnused i low high
  have trackNone : caller.trackCallerArg=none := by
    rw [callerEq]
    change frame.trackCallerArg=none
    rw [shape.track,PositiveRootInstalledFrame.track]
    exact (RawRootInvocation.control s.before s.place s.race).2.1
  have relevance : caller.extra.userRelevance=255 := by
    rw [frameFacts.extra,shape.extra,PositiveRootInstalledFrame.relevance,PositiveRootInstalledFrame.raw_relevance]
  let input : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,budget:=s.budget,dispatchFuel:=s.dispatchFuel,span:=s.span,ctx:=s.ctx,
    debugOff:=s.debugOff,cmp:=s.cmp,dynamicFuel:=s.dynamicFuel,validityFuel:=s.validityFuel,fuelEq:=s.fuelEq,validationEq:=s.validationEq,
    id:=s.id,entry:=exprEntry,base:=s.base,offset:=s.offset,len:=s.len,exprTag:=tracker.global.nextPointerTag,positive:=s.positive,
    nonzero:=GeneralBorrowPositiveConcreteWindowInputGeometry.nonzero s.toBase,signedFits:=s.signedFits,bounds:=GeneralBorrowPositiveConcreteWindowInputGeometry.byteBounds s.toBase,frames:=#[],caller:=caller,machine:=callMachine,
    tracker:=exprTracker,enabled:=by unfold callMachine PtrMetadataReturn.accountedMachine SourceControl.accounted;rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators];rw [machineCanonical];rfl,defaultMode:=s.mode,fresh:=s.helperFresh,input:=helper,selected:=_,head:=s.head,tail:=_,
    writable:=GeneralBorrowFreshMixedChild.extend (fun _=>true) (index first).toNat,raw:=helperRaw,treeEq:=helperTreeEq,
    parentTagEq:=helperParentTag.trans firstNewTag,tagEq:=helperNewTag,offsetEq:=helperOffset.trans firstOffset,lenEq:=helperLen.trans firstLen,
    protectedEq:=helperProtected,rangePositive:=helperPositive,clean:=helperClean,allocationSize:=exprCapacity,
    valid:=callerValid,live:=congrArg LocalState.value callCell,uncached:=congrArg LocalState.layout callCell,noClocks:=by rw [frameFacts.extra];exact ready.noClocks,
    ghost:=callRuntime.ghost,shallow:=callRuntime.shallow,cachedAddress:=by rw [callRuntime.addresses];exact s.cachedAddress,present:=callFound,race:=callRuntime.race,
    thread:=thread,index:=0,current:=helperCaller,active:=threadActive,top:=top,presentFrame:=current,metadata:=postMetadata,notConstructed:=postNotConstructed,
    sourceBody:=frameFacts.body,identity:=frameFacts.identity,callee:=frameFacts.callee,located:=frameFacts.location,source:=s.source,sourceValid:=sourceValid,
    sourceLive:=by simpa only [UInt64.add_zero] using congrArg LocalState.value exprCell,sourceCached:=congrArg LocalState.layout exprCell,backend:=callRuntime.backend,
    beforeMachine:=exprMachine,machineEq:=rfl,unchecked:=exprRuntime.1.unchecked,noGc:=exprRuntime.1.noGc,fixed:=exprRuntime.1.fixed,
    first:=first,firstTags:=tracker.global.protectedTags,firstRaw:=firstRaw,firstTreeEq:=helperTree,
    firstParentEq:=helperParent,writableEq:=rfl,initialTags:=firstState.allocator.nodeTags,exprUnheld:=helperExprUnheld }
  refine ⟨updated,input,installed,call,prefixTrace,?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,firstParent,firstParentTag,continuation,returnPlace,va,borrowed,frameFacts.size,frameFacts.all,
    frameFacts.slot0,frameFacts.slot7,frameFacts.slot8,frameFacts.slot9,frameFacts.slot10,frameFacts.slot13,slotFound,
    slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut,exprRuntime.1,
    rfl,rfl,firstTree,parentNodeTag,rfl,rfl,rfl,rfl,rfl,rfl,
    (keepExpr 1 (by decide)).trans ready.source,(keepExpr 2 (by decide)).trans ready.countSlot,unused,trackNone,(by rw [relevance];decide),rfl,firstNewTag,rfl,rfl,rfl,rfl,firstOffset,firstLen⟩
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowNonzeroMachinePrefixMetadata
