import duplicate_prefix.GeneralBorrowForestNonzeroMachinePrefix
import duplicate_prefix.GeneralBorrowForestRejectedTreeBuild
import duplicate_prefix.GeneralBorrowForestAcceptedAfterLenHelper
import duplicate_prefix.GeneralBorrowForestEntryFreshMap
namespace DuplicatePrefix.GeneralBorrowForestAcceptedFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open ActualReferenceContext GenericFunctionEntryState
open GeneralBorrowForestNonzeroMachinePrefix
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
attribute [local irreducible] GeneralBorrowForestEntrySharedInput.build GeneralBorrowForestRejectedTreeBuild.build GeneralBorrowForestRejectedTreeData.tree
set_option autoImplicit false in
structure Initial extends toPrefix : GeneralBorrowForestNonzeroMachinePrefix.Initial where
  within : count ≤ len/2
  statementFuel : limits.validation = validityFuel+1
  allocator : GeneralBorrowGcAllocator.Invariant entry.allocation.extra
  room : entry.allocation.extra.nodes.size+8 ≤ 4294967295
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  exprFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (held tracker fresh slotFresh).global.nextPointerTag
  helperFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag
  rootExprDifferent : tracker.global.nextPointerTag ≠ (held tracker fresh slotFresh).global.nextPointerTag
  rootHelperDifferent : tracker.global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag
  storageBuffer : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  maskValidBuffer : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLengthBuffer : entry.allocation.initializationMask.len = entry.allocation.byteSize
  initializedBuffer : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  provenanceBuffer : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  storageFitsBuffer : entry.allocation.len+64 < 18446744073709551616
  mutableBuffer : entry.allocation.mutability = .Mut
  bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes
  fresh5 : (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag.value < 18446744073709551615
  fresh6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag.value < 18446744073709551615
  map5 : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag
  map6 : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag
  unheld5 : (entryTracker toPrefix).global.protectedTags.get (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag = none
  unheld6 : (entryTracker toPrefix).global.protectedTags.get
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag = none
  rootDifferent5 : (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag ≠ tracker.global.nextPointerTag
  rootDifferent6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag ≠ tracker.global.nextPointerTag
  exprDifferent5 : (entryTracker toPrefix).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag
  exprDifferent6 : (entryTracker toPrefix).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag
  helperDifferent5 : (exprTracker toPrefix).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag
  helperDifferent6 : (exprTracker toPrefix).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag
  different56 : (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag
  slotRootDifferent5 : (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag ≠ slotRoot
  slotRootDifferent6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag ≠ slotRoot
  slotChildDifferent5 : (next tracker fresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4).global.nextPointerTag
  slotChildDifferent6 : (next tracker fresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (exprTracker toPrefix) fresh4) fresh5).global.nextPointerTag

def firstInput (s : Initial) : GeneralBorrowForestNonzeroMachinePrefix.First s.toPrefix := by
  let input := s.toPrefix
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.capacity];exact s.bounds
  exact GeneralBorrowForestEntrySharedInput.build s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
    (UInt64.pos_iff_ne_zero.mp s.positive) s.data bounds s.clean s.fresh s.slotFresh s.successorFresh s.successorDifferent
    s.allocator (by have room:=s.room;omega) s.vacantClean (entryTracker input).global.nextPointerTag
    (ReferenceBorrowDriver.allocatedTracker (entryTracker input) s.fresh3).global.nextPointerTag
    s.exprFresh s.rootExprDifferent s.helperFresh s.rootHelperDifferent

def treeInput (s : Initial) : GeneralBorrowForestNonzeroMachinePrefix.TreeData s.toPrefix (firstInput s) :=
  GeneralBorrowForestRejectedTreeBuild.build (entryTree s.toPrefix) (entryTracker s.toPrefix) s.fresh3 s.tracker.global.nextPointerTag
    (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras s.offset s.len (firstInput s)
    (UInt64.pos_iff_ne_zero.mp s.positive) s.exprUnheld

attribute [local irreducible] firstInput treeInput

theorem future (s : Initial) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.entry.allocation.extra.tagMapping tag)
    (rootDifferent : s.tracker.global.nextPointerTag ≠ tag)
    (exprDifferent : (entryTracker s.toPrefix).global.nextPointerTag ≠ tag) :
    GeneralBorrowTagMap.Fresh (exprTree s.toPrefix).tagMapping tag := by
  let input := s.toPrefix
  let first := firstInput s
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.capacity];exact s.bounds
  have entryFresh := GeneralBorrowForestEntryFreshMap.future s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
    (UInt64.pos_iff_ne_zero.mp s.positive) s.data bounds tag fresh rootDifferent
  have foreign : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestForeignAccess.LocationData (entryTree input) location (entryTracker input).global.protectedTags
        (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras .Read)) s.offset (s.offset+s.len) (entryTree input).locations := by
    intro position valid positive start stop
    obtain ⟨data⟩ := first.owned position valid positive start stop
    exact ⟨data.base⟩
  have result := GeneralBorrowForestForeignSharedFresh.preserves (entryTree input) (entryTracker input).global.protectedTags s.tracker.global.nextPointerTag
    (entryTracker input).global.nextPointerTag false (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras s.offset s.len
    .VisitChildrenOfAccessed first.context first.covered first.tagPresent first.fresh first.slot first.fits (UInt64.pos_iff_ne_zero.mp s.positive)
    first.well first.bounds foreign tag entryFresh exprDifferent
  simpa only [exprTree,GeneralBorrowForestRejectedTreeData.tree,GeneralBorrowForestForeignShared.child,GeneralBorrowForestForeignShared.read,GeneralBorrowForestMixedShared.child,GeneralBorrowForestMixedShared.read,input] using result

theorem resources (s : Initial) : GeneralBorrowGcVacantClean.VacantClean (exprTree s.toPrefix) ∧
    (exprTree s.toPrefix).nodes.size+6 ≤ 4294967295 := by
  let input := s.toPrefix
  let first := firstInput s
  have foreign : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestForeignAccess.LocationData (entryTree input) location (entryTracker input).global.protectedTags
        (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras .Read)) s.offset (s.offset+s.len) (entryTree input).locations := by
    intro position valid positive start stop
    obtain ⟨data⟩ := first.owned position valid positive start stop
    exact ⟨data.base⟩
  have vacancy := GeneralBorrowForestMixedSharedVacantClean.preserves (entryTree input) (entryTracker input).global.protectedTags s.tracker.global.nextPointerTag
    (entryTracker input).global.nextPointerTag false (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras s.offset s.len
    .VisitChildrenOfAccessed first.context first.covered first.tagPresent first.fresh first.slot first.fits (UInt64.pos_iff_ne_zero.mp s.positive)
    first.well first.bounds (fun _ => true) first.allocator first.owned first.vacantClean
  have shared := GeneralBorrowForestForeignSharedResources.preserves (entryTree input) (entryTracker input).global.protectedTags s.tracker.global.nextPointerTag
    (entryTracker input).global.nextPointerTag false (GeneralBorrowFreshMetadataChildMutableSlot.index s.data.slot) s.data.primary s.data.extras s.offset s.len
    .VisitChildrenOfAccessed first.context first.covered first.tagPresent first.fresh first.slot first.fits (UInt64.pos_iff_ne_zero.mp s.positive)
    first.well first.bounds first.allocator foreign
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.capacity];exact s.bounds
  have entryGrowth := GeneralBorrowForestEntryResources.growth s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
    (UInt64.pos_iff_ne_zero.mp s.positive) s.data bounds s.allocator
  have size : (exprTree input).nodes.size ≤ s.entry.allocation.extra.nodes.size+2 := by
    have sharedGrowth : (exprTree input).nodes.size ≤ (entryTree input).nodes.size+1 := by
      simpa only [exprTree,GeneralBorrowForestRejectedTreeData.tree,GeneralBorrowForestForeignShared.child,GeneralBorrowForestForeignShared.read,GeneralBorrowForestMixedShared.child,GeneralBorrowForestMixedShared.read] using shared.2.2.2.1
    change (entryTree input).nodes.size ≤ s.entry.allocation.extra.nodes.size+1 at entryGrowth
    omega
  have vacant : GeneralBorrowGcVacantClean.VacantClean (exprTree input) := by
    simpa only [exprTree,GeneralBorrowForestRejectedTreeData.tree] using vacancy
  refine ⟨vacant,?_⟩
  change (exprTree input).nodes.size+6 ≤ 4294967295
  have room:=s.room
  omega
theorem prepare (s : Initial) :
    ∃ (updated : Allocation Provenance BorrowTree) (input : GeneralBorrowForestAcceptedAfterLenHelper.Initial),
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] (entryFrame s.toPrefix) (entryMachine s.toPrefix updated)) ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] (entryFrame s.toPrefix) (entryMachine s.toPrefix updated)) (Storage.withCurrent #[] input.caller input.beforeMachine) := by
  obtain ⟨updated,x,options,limits,remaining,span,call,prefixTrace,origin⟩ :=
    GeneralBorrowForestNonzeroMachinePrefix.prepare s.toPrefix (firstInput s) (treeInput s)
  have map5 := future s _ s.map5 (Ne.symm s.rootDifferent5) s.exprDifferent5
  have map6 := future s _ s.map6 (Ne.symm s.rootDifferent6) s.exprDifferent6
  have data := resources s
  let input : GeneralBorrowForestAcceptedAfterLenHelper.Initial := {
    options:=x.options,
    limits:=x.limits,
    remaining:=x.remaining,
    budget:=x.budget,
    dispatchFuel:=x.dispatchFuel,
    span:=x.span,
    ctx:=x.ctx,
    debugOff:=x.debugOff,
    cmp:=x.cmp,
    dynamicFuel:=x.dynamicFuel,
    validityFuel:=x.validityFuel,
    fuelEq:=x.fuelEq,
    validationEq:=x.validationEq,
    id:=x.id,
    entry:=x.entry,
    base:=x.base,
    offset:=x.offset,
    len:=x.len,
    exprTag:=x.exprTag,
    positive:=x.positive,
    nonzero:=x.nonzero,
    signedFits:=x.signedFits,
    bounds:=x.bounds,
    caller:=x.caller,
    machine:=x.machine,
    tracker:=x.tracker,
    enabled:=x.enabled,
    defaultMode:=x.defaultMode,
    fresh:=x.fresh,
    parent:=x.parent,
    primary:=x.primary,
    extras:=x.extras,
    context:=x.context,
    covered:=x.covered,
    tagPresent:=x.tagPresent,
    tagFresh:=x.tagFresh,
    nodeTags:=x.nodeTags,
    unheld:=x.unheld,
    slot:=x.slot,
    fits:=x.fits,
    well:=x.well,
    clean:=x.clean,
    rangePositive:=x.rangePositive,
    owned:=x.owned,
    allocationSize:=x.allocationSize,
    valid:=x.valid,
    live:=x.live,
    uncached:=x.uncached,
    noClocks:=x.noClocks,
    ghost:=x.ghost,
    shallow:=x.shallow,
    cachedAddress:=x.cachedAddress,
    present:=x.present,
    race:=x.race,
    thread:=x.thread,
    index:=x.index,
    current:=x.current,
    active:=x.active,
    top:=x.top,
    presentFrame:=x.presentFrame,
    metadata:=x.metadata,
    notConstructed:=x.notConstructed,
    sourceBody:=x.sourceBody,
    identity:=x.identity,
    callee:=x.callee,
    located:=x.located,
    source:=x.source,
    sourceValid:=x.sourceValid,
    sourceLive:=x.sourceLive,
    sourceCached:=x.sourceCached,
    backend:=x.backend,
    beforeMachine:=x.beforeMachine,
    machineEq:=x.machineEq,
    unchecked:=x.unchecked,
    noGc:=x.noGc,
    fixed:=x.fixed,
    target:=x.target,
    targetNode:=x.targetNode,
    targetPresent:=x.targetPresent,
    exprFree:=x.exprFree,
    prefixPath:=x.prefixPath,
    exprOutside:=x.exprOutside,
    rootPath:=x.rootPath,
    targetActive:=x.targetActive,
    frameSize:=x.frameSize,
    allImmediate:=x.allImmediate,
    live0:=x.live0,
    cache0:=x.cache0,
    live7:=x.live7,
    live8:=x.live8,
    cache8:=x.cache8,
    live9:=x.live9,
    cache9:=x.cache9,
    live10:=x.live10,
    cache10:=x.cache10,
    live13:=x.live13,
    cache13:=x.cache13,
    continuation:=x.continuation,
    varargs:=x.varargs,
    slotId:=x.slotId,
    slotEntry:=x.slotEntry,
    slotRoot:=x.slotRoot,
    slotChild:=x.slotChild,
    slotBase:=x.slotBase,
    separate:=x.separate,
    slotPresent:=x.slotPresent,
    slotTree:=x.slotTree,
    slotSize:=x.slotSize,
    slotStorage:=x.slotStorage,
    slotMask:=x.slotMask,
    slotProvenance:=x.slotProvenance,
    slotMutable:=x.slotMutable,
    slotRootFree:=x.slotRootFree,
    slotChildHeld:=x.slotChildHeld,
    slotDistinct:=x.slotDistinct,
    frameTracked:=x.frameTracked,
    place:=x.place,
    layout:=x.layout,
    slotPointer:=x.slotPointer,
    aligned:=x.aligned,
    slotFits:=x.slotFits,
    slotCached:=x.slotCached,
    slotExtras:=x.slotExtras,
    destination:=x.destination,
    writeContext:=x.writeContext,
    validationContext:=x.validationContext,
    accessEq:=x.accessEq,
    validationWidth:=x.validationWidth,
    validationRuntimeSize:=x.validationRuntimeSize,
    sameRuntime:=x.sameRuntime,
    width:=x.width,
    runtimeWidth:=x.runtimeWidth,
    runtimeSize:=x.runtimeSize,
    outerAccessEq:=x.outerAccessEq,
    cache7:=x.cache7,
    dead15:=x.dead15,
    cache15:=x.cache15,
    dead16:=x.dead16,
    cache16:=x.cache16,
    valid1:=x.valid1,
    value1:=x.value1,
    cached1:=x.cached1,
    slot2:=x.slot2,
    unused:=x.unused,
    trackNone:=x.trackNone,
    relevant:=x.relevant,
    rootMetadata:=x.rootMetadata,
    rootNotConstructed:=x.rootNotConstructed,
    count:=x.inputCount,countPositive:=by rw [origin.count];exact s.countPositive,
    within:=by rw [origin.count,origin.len];exact s.within,
    statementFuel:=by rw [limits,origin.validityFuel];exact s.statementFuel,
    preciseOff:=by rw [options];exact s.preciseOff,implicitOff:=by rw [options];exact s.implicitOff,
    storage:=by rw [origin.entry];exact s.storageBuffer,
    maskValid:=by rw [origin.entry];exact s.maskValidBuffer,
    maskLength:=by rw [origin.entry];exact s.maskLengthBuffer,
    initialized:=by rw [origin.entry,origin.offset,origin.count];exact s.initializedBuffer,
    provenance:=by rw [origin.entry];exact s.provenanceBuffer,
    storageFits:=by rw [origin.entry];exact s.storageFitsBuffer,
    mutable:=by rw [origin.entry];exact s.mutableBuffer,
    bufferExtras:=by rw [origin.extras,origin.id];exact s.bufferExtras,
    bounded:=by rw [origin.count,options,remaining,span];exact s.bounded,
    allocator:=by rw [origin.entry];exact (treeInput s).next.allocator,
    vacantClean:=by rw [origin.entry];exact data.1,
    room:=by rw [origin.entry];exact data.2,
    fresh3:=by simpa only [origin.tracker] using s.fresh5,
    fresh4:=by simpa only [origin.tracker] using s.fresh6,
    map3:=by simpa only [origin.entry,origin.tracker,Allocation.setExtra,Allocation.mapExtra] using map5,
    map4:=by simpa only [origin.entry,origin.tracker,Allocation.setExtra,Allocation.mapExtra] using map6,
    unheld3:=by simpa only [origin.tracker,exprTracker,ReferenceBorrowDriver.allocatedTracker] using s.unheld5,
    unheld4:=by simpa only [origin.tracker,exprTracker,ReferenceBorrowDriver.allocatedTracker] using s.unheld6,
    different23:=by simpa only [origin.tracker] using s.helperDifferent5,
    different24:=by simpa only [origin.tracker] using s.helperDifferent6,
    different34:=by simpa only [origin.tracker] using s.different56,
    targetDifferent3:=by simpa only [origin.tracker,origin.targetTag] using s.rootDifferent5,
    targetDifferent4:=by simpa only [origin.tracker,origin.targetTag] using s.rootDifferent6,
    slotRootDifferent3:=by simpa only [origin.tracker,origin.slotRoot] using s.slotRootDifferent5,
    slotRootDifferent4:=by simpa only [origin.tracker,origin.slotRoot] using s.slotRootDifferent6,
    slotChildDifferent3:=by simpa only [origin.tracker,origin.slotChild] using s.slotChildDifferent5,
    slotChildDifferent4:=by simpa only [origin.tracker,origin.slotChild] using s.slotChildDifferent6 }
  exact ⟨updated,input,options,limits,remaining,span,call,prefixTrace⟩

def Result (s : Initial) : Prop :=
  let cfg := config s.options (s.remaining+1) s.span
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,s.limits,fun _ _ => True⟩
  ∃ (slot : Allocation Provenance BorrowTree) (ready : GeneralBorrowForestAsMutPhysicalReturn.Input) (done : MachineHooks.State MiriMemoryKind Machine.RootUser),
    let initial := Storage.withCurrent #[] (entryFrame s.toPrefix) (entryMachine s.toPrefix slot)
    Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ = .ok () initial ∧
    GeneralBorrowForestAsMutPhysicalReturn.Result ready ∧
    SuccessfulTrace.Trace cfg s.limits initial done ∧
    ExecutionMachine.step cfg s.limits () done = (done,.ok false) ∧ done.stack.frames = #[] ∧
    CallSafety.NoUBBeforeReturn safety 1 initial ∧
    (∀ before, SuccessfulTrace.Trace cfg s.limits initial before →
      ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing))

/-- Original protected ROOT call, positive accepted-count body, actual len and
mutable helper lifetimes, physical adjacent copy, bool true return, terminal
execution and scoped NoUB for all reachable permitted finite Unit prefixes.
Only original caller/configuration/physical-storage resources are supplied. -/
theorem invoke (s : Initial) : Result s := by
  obtain ⟨slot,boundary,options,limits,remaining,span,call,leadingTrace⟩ := prepare s
  obtain ⟨ready,done,physical,suffixTrace,terminal,empty,_,_⟩ := GeneralBorrowForestAcceptedAfterLenHelper.invoke boundary
  rw [options,limits,remaining,span] at suffixTrace terminal
  have trace := SuccessfulTrace.append leadingTrace suffixTrace
  let initial := Storage.withCurrent #[] (entryFrame s.toPrefix) (entryMachine s.toPrefix slot)
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩
  have safe := SuccessfulTrace.no_ub safety 1 initial done ⟨by decide,rfl⟩ trace
    (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change 0<1;decide)
  exact ⟨slot,ready,done,call,physical,trace,terminal,empty,safe,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
end
end DuplicatePrefix.GeneralBorrowForestAcceptedFunctionSafety
