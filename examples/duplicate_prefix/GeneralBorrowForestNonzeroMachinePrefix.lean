import duplicate_prefix.GeneralBorrowForestRejectedTreeData
import duplicate_prefix.GeneralBorrowForestPreLenInput
import duplicate_prefix.GeneralBorrowForestFunctionEntryZero
import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame
import duplicate_prefix.GeneralBorrowForestSharedExpressionRuntime
namespace DuplicatePrefix.GeneralBorrowForestNonzeroMachinePrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState LenUncachedFrontend PtrMetadataReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
attribute [local irreducible] GeneralBorrowForestRejectedTreeData.tree
set_option autoImplicit false in
structure Initial extends GeneralBorrowForestFunctionEntryZero.Initial where
  count : UInt64
  countPositive : (0 : UInt64) < count
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  fresh3 : (held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
  fresh4 : (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag.value < 18446744073709551615
  exprUnheld : (held tracker fresh slotFresh).global.protectedTags.contains (held tracker fresh slotFresh).global.nextPointerTag = false
  helperUnheld : (held tracker fresh slotFresh).global.protectedTags.get
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag = none
  rootFreeAfterHelper : ((TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4)
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag).global.endCall
      (({} : FrameState).addProtector id (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag)).protectedTags.contains slotRoot = false
  slotHeldAfterHelper : ((TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4)
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag).global.endCall
      (({} : FrameState).addProtector id (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag)).protectedTags.contains
      (next tracker fresh).global.nextPointerTag = true

def entryTree (s : Initial) := GeneralBorrowForestArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len

def entryTracker (s : Initial) := held s.tracker s.fresh s.slotFresh

def entryFrame (s : Initial) :=
  let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
  PositiveRootInstalledFrame.installed (RawRootInvocation.root s.before s.place s.race) adjusted s.count {} s.id
    s.tracker.global.nextPointerTag s.slotId (next s.tracker s.fresh).global.nextPointerTag

def entryMachine (s : Initial) (updated : Allocation Provenance BorrowTree) :=
  enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
    s.slotFresh s.slotId s.slotEntry s.slotRoot updated

abbrev First (s : Initial) := GeneralBorrowForestEntrySharedInput.First (entryTree s) (entryTracker s).global.protectedTags
  s.tracker.global.nextPointerTag (entryTracker s).global.nextPointerTag
  (ReferenceBorrowDriver.allocatedTracker (entryTracker s) s.fresh3).global.nextPointerTag
  (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras s.offset s.len

abbrev TreeData (s : Initial) (first : First s) := GeneralBorrowForestRejectedTreeData.Data (entryTree s) (entryTracker s) s.fresh3
  s.tracker.global.nextPointerTag (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras s.offset s.len first

def exprTree (s : Initial) := GeneralBorrowForestRejectedTreeData.tree (entryTree s) (entryTracker s) s.tracker.global.nextPointerTag s.offset s.len

def exprTracker (s : Initial) := ReferenceBorrowDriver.allocatedTracker (entryTracker s) s.fresh3

set_option autoImplicit false in
structure Origin (s : Initial) (updated : Allocation Provenance BorrowTree) (input : GeneralBorrowForestPreLenInput.Initial) : Prop where
  id : input.id = s.id
  base : input.base = s.base
  offset : input.offset = s.offset
  len : input.len = s.len
  count : input.inputCount = s.count
  validityFuel : input.validityFuel = s.validityFuel
  entry : input.entry = {s.entry with allocation := s.entry.allocation.setExtra (exprTree s)}
  tracker : input.tracker = exprTracker s
  targetTag : input.targetNode.tag = s.tracker.global.nextPointerTag
  slotId : input.slotId = s.slotId
  slotRoot : input.slotRoot = s.slotRoot
  slotChild : input.slotChild = (next s.tracker s.fresh).global.nextPointerTag
  slotEntry : input.slotEntry = {s.slotEntry with allocation := updated}
  extras : input.beforeMachine.user.payload.payload.user.runtime.extras = s.before.user.payload.payload.user.runtime.extras

-- The machine/frame assembly is kept separate from original-tree formation;
-- the final invocation theorem supplies First and TreeData internally.
theorem prepare (s : Initial) (first : First s) (trees : TreeData s first) :
    ∃ (updated : Allocation Provenance BorrowTree) (input : GeneralBorrowForestPreLenInput.Initial),
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] (entryFrame s) (entryMachine s updated)) ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] (entryFrame s) (entryMachine s updated)) (Storage.withCurrent #[] input.caller input.beforeMachine) ∧ Origin s updated input := by
  have countPositive := s.countPositive
  obtain ⟨updated,frame,call,prefixTrace,shape,ready,slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ :=
    GeneralBorrowForestFunctionEntryToShared.enters_shared_boundary s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel
      s.fuelEq s.validationEq s.id s.parentTag s.tracker s.base s.offset s.len s.count s.nonzero s.entry s.positive s.signedFits s.bounds
      s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh s.data s.capacity s.race s.metadata s.notConstructed
      s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned s.slotCached s.slotTree s.slotSize
      s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree s.mutable s.storage s.maskLength s.provenance
      s.noBackend s.extras s.thread s.active s.noCache s.source s.mode countPositive s.unchecked s.noGc s.fixed
  let beforeExpr := RootZeroCompleteState.tick s.options s.remaining s.span (entryMachine s updated)
  let tracker := entryTracker s
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation := s.entry.allocation.setExtra (entryTree s)}
  let exprTree := GeneralBorrowForestRejectedTreeData.tree (entryTree s) tracker s.tracker.global.nextPointerTag s.offset s.len
  let exprEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {buffer with allocation := buffer.allocation.setExtra exprTree}
  let exprTracker := ReferenceBorrowDriver.allocatedTracker tracker s.fresh3
  let exprMachine := GeneralBorrowForestSharedExpressionRuntime.machine beforeExpr tracker s.fresh3 s.id buffer exprTree
  let callMachine := accountedMachine s.options s.remaining s.span exprMachine
  have runtime := GenericFunctionEntryRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
    s.slotFresh s.slotId s.slotEntry s.slotRoot updated s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed
  change GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before beforeExpr at runtime
  have trackedBefore : beforeExpr.borrowTracker = some tracker := rfl
  have found : beforeExpr.memory.live.find? (fun row => row.1 == s.id) = some (s.id,buffer) :=
    GenericFunctionEntryState.buffer_lookup (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot updated (Ne.symm s.separate)
  have capacity : buffer.allocation.extra.locations.size = buffer.allocation.byteSize :=
    (GeneralBorrowForestEntryMetadata.build s.entry.allocation.extra s.tracker s.parentTag s.offset s.len (UInt64.pos_iff_ne_zero.mp s.positive)
      s.data (by rw [s.capacity];exact s.bounds)).capacity.trans s.capacity
  have valid1 : 1 < frame.locals.size := by rw [ready.size];decide
  have valid12 : 12 < frame.locals.size := by rw [ready.size];decide
  have sourceCell := Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans ready.source)
  have destCell := Option.some.inj ((Array.getElem?_eq_getElem valid12).symm.trans ready.exprSlot)
  have sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config s.options (s.remaining+1) s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm) := by
    have equality : (config s.options (s.remaining+1) s.span).access.runtime.base = (config s.options s.remaining s.span).access.runtime.base := by
      rw [actual_access_runtime s.options () (s.remaining+1) s.span,actual_access_runtime s.options () s.remaining s.span]
    rw [equality]
    exact congrArg LocalState.value sourceCell
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame beforeExpr)).metadata=PreparedReflection.actual.runtime := by
    change beforeExpr.user.payload.payload.user.types.metadata = _
    rw [runtime.types];exact s.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame beforeExpr)).entries.any (·.value.ty == 4)=false := by
    change beforeExpr.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false
    rw [runtime.types];exact s.notConstructed
  have statement := GeneralBorrowForestEntrySharedExpression.positive_statement s.options s.limits s.remaining s.span s.preciseOff s.implicitOff s.debugOff
    s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.base s.offset s.len s.id buffer s.positive s.nonzero s.signedFits #[] frame beforeExpr
    ready.body ready.identity ready.callee ready.location tracker trackedBefore s.mode s.fresh3 s.tracker.global.nextPointerTag
    (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras first.context first.covered first.tagPresent first.fresh first.slot first.fits first.well
    first.bounds (fun _ => true) capacity first.owned valid1 valid12 sourceLive (congrArg LocalState.layout sourceCell)
    (congrArg LocalState.value destCell) (congrArg LocalState.layout destCell) ready.noClocks runtime.ghost runtime.shallow
    (by rw [runtime.addresses];exact s.cachedAddress) found runtime.race metadata notConstructed
  let exprValue := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after frame valid12 exprValue
  have exprStep : ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits ()
      (Storage.withCurrent #[] frame beforeExpr) = (Storage.withCurrent #[] caller exprMachine,.ok true) := by
    simpa only [caller,GeneralBorrowForestSharedPreLenFrame.after,exprMachine,GeneralBorrowForestSharedExpressionRuntime.machine,exprTree,GeneralBorrowForestRejectedTreeData.tree,exprValue,RootReferenceFacts.destination,RootReferenceFacts.location,RootReferenceInfo.layout,buffer,Allocation.setExtra,Allocation.mapExtra,ite_true] using statement
  have frameFacts := GeneralBorrowForestSharedPreLenFrame.build frame _ exprValue s.count _ ready valid12
  have exprRuntime := GeneralBorrowForestSharedExpressionRuntime.facts s.options s.remaining s.span s.before beforeExpr tracker s.fresh3 s.id buffer exprTree runtime
  change GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before exprMachine ∧
    GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before callMachine at exprRuntime
  have callRuntime := exprRuntime.2
  have callerSize : caller.locals.size = 25 := frameFacts.size
  have callerValid : 11 < caller.locals.size := by rw [callerSize];decide
  have callCell := Option.some.inj ((Array.getElem?_eq_getElem callerValid).symm.trans frameFacts.slot11)
  have sourceValid : 12 < caller.locals.size := by rw [callerSize];decide
  have exprCell := Option.some.inj ((Array.getElem?_eq_getElem sourceValid).symm.trans frameFacts.slot12)
  let helperCaller := cachedCaller caller callerValid
  let destination := (LocalPlaces.localRuntimePlace 0 helperCaller 11 RootCompilerFacts.usizeLayout).stackView
  let state := Storage.withCurrent #[] helperCaller callMachine
  obtain ⟨thread,threadActive,threadCache⟩ := callRuntime.active
  have top : FrameRelevance.top (LenPush.pushed s.options.userRelevantCrates state destination).stack thread.topUserRelevantFrame = some 0 := by
    simp [FrameRelevance.top,threadCache]
  have current : (LenPush.pushed s.options.userRelevantCrates state destination).stack.frames[0]? = some helperCaller := by
    simp [LenPush.pushed,state,Storage.withCurrent]
  have postMetadata : (EvalProjectionMachine.arrays.get (LenPush.completed s.options.userRelevantCrates state destination helperCaller)).metadata=PreparedReflection.actual.runtime := by
    change (LenPushFacts.posted s.options s.remaining s.span #[] helperCaller exprMachine helperCaller).user.payload.payload.user.types.metadata = _
    rw [LenPushFacts.types_eq,exprRuntime.1.types];exact s.metadata
  have postNotConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed s.options.userRelevantCrates state destination helperCaller)).entries.any (·.value.ty == 4)=false := by
    change ((LenPushFacts.posted s.options s.remaining s.span #[] helperCaller exprMachine helperCaller).user.payload.payload.user.types.entries.any (·.value.ty == 4))=false
    rw [LenPushFacts.types_eq,exprRuntime.1.types];exact s.notConstructed
  have slotFoundBefore : beforeExpr.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,{s.slotEntry with allocation := updated}) :=
    GenericFunctionEntryNumerics.slot_lookup s.options s.remaining s.span (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag
      s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated
  have slotFound : exprMachine.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,{s.slotEntry with allocation := updated}) :=
    StackPopRelease.lookup_commit_other beforeExpr.memory s.id s.slotId buffer _ exprTree s.separate slotFoundBefore
  have treeCapacity : exprTree.locations.size = (entryTree s).locations.size := by
    exact trees.capacity
  have entryCapacity : (entryTree s).locations.size = s.entry.allocation.byteSize :=
    capacity.trans (AllocationCopy.set_extra_preserves_storage s.entry.allocation (entryTree s)).1
  have exprCapacity : exprEntry.allocation.extra.locations.size=exprEntry.allocation.byteSize := by
    have store := (AllocationCopy.set_extra_preserves_storage buffer.allocation exprTree).1.trans
      (AllocationCopy.set_extra_preserves_storage s.entry.allocation (entryTree s)).1
    exact (treeCapacity.trans entryCapacity).trans store.symm
  have raw := RawRootInvocation.control s.before s.place s.race
  have installedMetadata := PositiveRootInstalledFrame.metadata (RawRootInvocation.root s.before s.place s.race)
    (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm s.count {} s.id
    s.tracker.global.nextPointerTag s.slotId (next s.tracker s.fresh).global.nextPointerTag
  have continuation : caller.returnContinuation=.stop true := frameFacts.continuation.trans (shape.continuation.trans installedMetadata.2.2.2.1)
  have destinationEq : caller.returnPlace.toRuntimePlace = ⟨.memory s.place.mplace,s.place.layout⟩ := by
    rw [frameFacts.returnPlace,shape.returnPlace,installedMetadata.2.2.2.2.1]
    rfl
  have va : caller.vaList = #[] := by rw [frameFacts.varargs,shape.vaList,installedMetadata.2.2.2.2.2.1];rfl
  have frameBorrow : caller.extra.borrowTracker = some ((({} : FrameState).addProtector s.id trees.targetNode.tag).addProtector s.slotId (next s.tracker s.fresh).global.nextPointerTag) := by
    rw [frameFacts.extra,trees.targetTag]
    exact ready.borrowed
  have getCell (i : Nat) (valid : i<caller.locals.size) (cell : LocalState Provenance LocalLayout)
      (known : caller.locals[i]? = some cell) : caller.locals[i]'valid=cell :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)
  have keepExpr (i : Nat) (different : i≠12) : caller.locals[i]? = frame.locals[i]? := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different]
  let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
  have originalUnused (i : Nat) (low : 15≤i) (high : i≤24) : (entryFrame s).locals[i]? = some ⟨.dead,none⟩ := by
    have known := PositiveRootInstalledFrame.slot_option (RawRootInvocation.root s.before s.place s.race)
      (RawRootInvocation.locals s.before s.place s.race) adjusted s.count {} s.id s.tracker.global.nextPointerTag s.slotId
      (next s.tracker s.fresh).global.nextPointerTag ⟨i,by omega⟩
    have h14 : 14≠i := by omega
    have h13 : 13≠i := by omega
    have h6 : 6≠i := by omega
    have h0 : 0≠i := by omega
    have h2 : 2≠i := by omega
    have h1 : 1≠i := by omega
    simpa only [entryFrame,adjusted,h14,h13,h6,h0,h2,h1,Fin.val_mk,or_self,ite_false] using known
  have unusedFrame (i : Nat) (low : 15≤i) (high : i≤24) : caller.locals[i]? = some ⟨.dead,none⟩ := by
    rw [keepExpr i (by omega),shape.keep i (by omega)]
    exact originalUnused i low high
  have cell15 := getCell 15 (by omega) _ (unusedFrame 15 (by decide) (by decide))
  have cell16 := getCell 16 (by omega) _ (unusedFrame 16 (by decide) (by decide))
  have caller1 : 1<caller.locals.size := by rw [callerSize];decide
  have cell1 := getCell 1 caller1 _ ((keepExpr 1 (by decide)).trans ready.source)
  have value1 : caller.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config s.options (s.remaining+1) s.span).access.runtime.base
      (Pointer.new (.concrete s.id trees.targetNode.tag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm) := by
    rw [trees.targetTag]
    have same : (config s.options (s.remaining+1) s.span).access.runtime.base = (config s.options s.remaining s.span).access.runtime.base := by
      rw [actual_access_runtime s.options () (s.remaining+1) s.span,actual_access_runtime s.options () s.remaining s.span]
    rw [same]
    exact congrArg LocalState.value cell1
  have trackNone : caller.trackCallerArg = none := by
    change frame.trackCallerArg = none
    rw [shape.track,PositiveRootInstalledFrame.track]
    exact (RawRootInvocation.control s.before s.place s.race).2.1
  have relevance : caller.extra.userRelevance = 255 := by
    rw [frameFacts.extra,shape.extra,PositiveRootInstalledFrame.relevance,PositiveRootInstalledFrame.raw_relevance]
  let input : GeneralBorrowForestPreLenInput.Initial := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,budget:=s.budget,dispatchFuel:=s.dispatchFuel,span:=s.span,ctx:=s.ctx,
    debugOff:=s.debugOff,cmp:=s.cmp,dynamicFuel:=s.dynamicFuel,validityFuel:=s.validityFuel,fuelEq:=s.fuelEq,validationEq:=s.validationEq,
    id:=s.id,entry:=exprEntry,base:=s.base,offset:=s.offset,len:=s.len,exprTag:=tracker.global.nextPointerTag,
    positive:=s.positive,nonzero:=s.nonzero,signedFits:=s.signedFits,bounds:=s.bounds,caller:=caller,machine:=callMachine,tracker:=exprTracker,
    enabled:=rfl,defaultMode:=s.mode,fresh:=s.fresh4,parent:=GeneralBorrowFreshMetadataChildSlot.index first.slot,
    primary:=s.data.primary,extras:=s.data.extras,context:=trees.next.context,covered:=trees.next.covered,tagPresent:=trees.next.tag,
    tagFresh:=trees.next.nextFresh,nodeTags:=trees.next.allocator.nodeTags,unheld:=s.helperUnheld,slot:=trees.next.slot,
    fits:=trees.next.nodeFits,well:=trees.next.well,clean:=trees.next.clean,rangePositive:=GenericFunctionEntryNumerics.range_positive s.offset s.len s.entry.allocation.byteSize.bytes s.positive s.bounds,
    owned:=trees.next.owned,allocationSize:=exprCapacity,valid:=callerValid,live:=congrArg LocalState.value callCell,
    uncached:=congrArg LocalState.layout callCell,noClocks:=by rw [frameFacts.extra];exact ready.noClocks,
    ghost:=callRuntime.ghost,shallow:=callRuntime.shallow,cachedAddress:=by rw [callRuntime.addresses];exact s.cachedAddress,
    present:=StackPopRelease.lookup_commit_same beforeExpr.memory s.id buffer exprTree,race:=callRuntime.race,
    thread:=thread,index:=0,current:=helperCaller,active:=threadActive,top:=top,presentFrame:=current,metadata:=postMetadata,notConstructed:=postNotConstructed,
    sourceBody:=frameFacts.body,identity:=frameFacts.identity,callee:=frameFacts.callee,located:=frameFacts.location,source:=s.source,sourceValid:=sourceValid,
    sourceLive:=congrArg LocalState.value exprCell,sourceCached:=congrArg LocalState.layout exprCell,backend:=callRuntime.backend,
    beforeMachine:=exprMachine,machineEq:=rfl,unchecked:=exprRuntime.1.unchecked,noGc:=exprRuntime.1.noGc,fixed:=exprRuntime.1.fixed,
    target:=GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot,targetNode:=trees.targetNode,targetPresent:=trees.targetPresent,
    exprFree:=trees.exprFree,prefixPath:=trees.prefixPath,exprOutside:=trees.exprOutside,rootPath:=trees.rootPath,targetActive:=trees.targetActive,
    inputCount:=s.count,frameSize:=callerSize,allImmediate:=frameFacts.all,
    live0:=congrArg LocalState.value (getCell 0 (by omega) _ frameFacts.slot0),cache0:=congrArg LocalState.layout (getCell 0 (by omega) _ frameFacts.slot0),
    live7:=congrArg LocalState.value (getCell 7 (by omega) _ frameFacts.slot7),live8:=congrArg LocalState.value (getCell 8 (by omega) _ frameFacts.slot8),
    cache8:=congrArg LocalState.layout (getCell 8 (by omega) _ frameFacts.slot8),live9:=congrArg LocalState.value (getCell 9 (by omega) _ frameFacts.slot9),
    cache9:=congrArg LocalState.layout (getCell 9 (by omega) _ frameFacts.slot9),live10:=congrArg LocalState.value (getCell 10 (by omega) _ frameFacts.slot10),
    cache10:=congrArg LocalState.layout (getCell 10 (by omega) _ frameFacts.slot10),live13:=congrArg LocalState.value (getCell 13 (by omega) _ frameFacts.slot13),
    cache13:=congrArg LocalState.layout (getCell 13 (by omega) _ frameFacts.slot13),continuation:=continuation,varargs:=va,
    slotId:=s.slotId,slotEntry:={s.slotEntry with allocation:=updated},slotRoot:=s.slotRoot,slotChild:=(next s.tracker s.fresh).global.nextPointerTag,
    slotBase:=s.slotBase,separate:=s.separate,slotPresent:=slotFound,slotTree:=slotTree,slotSize:=slotSize,slotStorage:=slotLen,
    slotMask:=slotMask,slotProvenance:=slotProv,slotMutable:=slotMut,slotRootFree:=s.rootFreeAfterHelper,slotChildHeld:=s.slotHeldAfterHelper,
    slotDistinct:=s.slotDistinct,frameTracked:=frameBorrow,place:=s.place,layout:=s.layout,slotPointer:=s.slotPointer,aligned:=s.aligned,slotFits:=s.slotFits,
    slotCached:=by rw [exprRuntime.1.addresses];exact s.slotCached,slotExtras:=by rw [exprRuntime.1.extras];exact s.extras,destination:=destinationEq,
    writeContext:=s.writeContext,validationContext:=s.validationContext,accessEq:=s.accessEq,validationWidth:=s.validationWidth,
    validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    cache7:=congrArg LocalState.layout (getCell 7 (by omega) _ frameFacts.slot7),dead15:=congrArg LocalState.value cell15,cache15:=congrArg LocalState.layout cell15,
    dead16:=congrArg LocalState.value cell16,cache16:=congrArg LocalState.layout cell16,valid1:=caller1,value1:=value1,cached1:=congrArg LocalState.layout cell1,
    slot2:=(keepExpr 2 (by decide)).trans ready.countSlot,unused:=fun i low high => unusedFrame i (by omega) high,
    trackNone:=trackNone,relevant:=by rw [relevance];decide,
    rootMetadata:=by rw [exprRuntime.1.types];exact s.metadata,
    rootNotConstructed:=by rw [exprRuntime.1.types];exact s.notConstructed }
  refine ⟨updated,input,rfl,rfl,rfl,rfl,call,SuccessfulTrace.append prefixTrace (.next exprStep (.refl _)),?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,trees.targetTag,rfl,rfl,rfl,rfl,exprRuntime.1.extras⟩
end
end DuplicatePrefix.GeneralBorrowForestNonzeroMachinePrefix
