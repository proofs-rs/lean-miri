import duplicate_prefix.GeneralBorrowPositiveWildcardFamilyPhysical
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardFamilyInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveWildcardFamilyPhysical
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {capacity : UInt64} {global : GlobalState} {tree : BorrowTree} {location : LocationTree} {roots : List UniIndex}

theorem future_fresh (p : Caller capacity global tree)
    (family : GeneralBorrowExposedUniqueRootFamilySeed.Family capacity global tree location roots)
    (tag : BorTag) (above : p.tracker.global.nextPointerTag.value≤tag.value) :
    GeneralBorrowTagMap.Fresh p.entry.allocation.extra.tagMapping tag := by
  rw [p.entryTree]
  exact GeneralBorrowExposedUniqueRootFamilyRows.fresh_above capacity global tree location roots family tag
    (by simpa only [p.trackerGlobal] using above)

/-- Source-generated rows and pure numeric reserves form the raw original
caller graph contract. Every physical premise stays on Caller. -/
def base (p : Caller capacity global tree)
    (family : GeneralBorrowExposedUniqueRootFamilySeed.Family capacity global tree location roots) :
    @GeneralBorrowPositiveWildcardOriginalInput.Base (scope roots) := by
  letI : GeneralBorrowExposedKnownRootState.Scope:=scope roots
  let t:=tags p
  let rows:=Classical.choice (GeneralBorrowExposedUniqueRootFamilyRows.rows capacity global tree location roots family
    (TypedBorrowSteps.registeredGlobal p.tracker p.tracker.global.nextPointerTag).protectedTags)
  exact {
    options:=p.options,
    limits:=p.limits,
    remaining:=p.remaining,
    span:=p.span,
    ctx:=p.ctx,
    debugOff:=p.debugOff,
    cmp:=p.cmp,
    dynamicFuel:=p.dynamicFuel,
    validityFuel:=p.validityFuel,
    fuelEq:=p.fuelEq,
    validationEq:=p.validationEq,
    id:=p.id,
    tracker:=p.tracker,
    base:=p.base,
    len:=capacity,
    count:=p.count,
    nonzero:=p.nonzero,
    entry:=p.entry,
    positive:=UInt64.pos_iff_ne_zero.mpr family.nonzero,
    signedFits:=p.signedFits,
    bounds:=by rw [p.bufferSize];exact Nat.le_refl _,
    before:=p.before,
    ghost:=p.ghost,
    shallow:=p.shallow,
    cachedAddress:=p.cachedAddress,
    present:=p.present,
    enabled:=p.enabled,
    fresh:=t.fresh,
    position:=p.position,
    positionValid:=p.positionValid,
    ordered:=p.ordered,
    addressRow:=p.addressRow,
    addressMode:=p.addressMode,
    exposedAlloc:=p.exposedAlloc,
    location:=location,
    head:=rows.head,
    headNode:=rows.headNode,
    extraRoots:=rows.extraRoots,
    nodes:=rows.nodes,
    states:=fun _=>GeneralBorrowWildcardLeaf.unique,
    locations:=by simpa only [p.entryTree] using rows.locations,
    roots:=by simpa only [p.entryTree] using rows.rootsEq,
    headPresent:=by simpa only [p.entryTree] using rows.headPresent,
    headLeaf:=rows.headLeaf,
    headExposed:=rows.headExposed,
    headStored:=rows.headStored,
    coherent:=by simpa only [p.entryTree] using rows.coherent,
    short:=by rw [p.entryTree];have room:=p.nodeRoom;omega,
    data:=by simpa only [p.entryTree] using rows.data,
    tagFresh:=by simpa only [p.entryTree,p.trackerGlobal] using rows.tagFresh,
    noFree:=by simpa only [p.entryTree] using rows.noFree,
    fits:=by rw [p.entryTree,family.aligned];change tree.nodes.size≤4294967295;have room:=p.nodeRoom;omega,
    race:=p.race,
    metadata:=p.metadata,
    notConstructed:=p.notConstructed,
    retagCtx:=p.retagCtx,
    place:=p.place,
    layout:=p.layout,
    slotId:=p.slotId,
    slotEntry:=p.slotEntry,
    slotBase:=p.slotBase,
    slotRoot:=p.slotRoot,
    slotPointer:=p.slotPointer,
    aligned:=p.aligned,
    slotCached:=p.slotCached,
    slotTree:=p.slotTree,
    slotSize:=p.slotSize,
    slotPresent:=p.slotPresent,
    separate:=p.separate,
    slotFresh:=t.slotFresh,
    slotDistinct:=by intro same;have e:=congrArg (fun tag : BorTag=>tag.value.toNat) same;exact p.slotNotSuccessor (e.trans (GenericFunctionEntryNumerics.successor_value _ t.fresh)),
    slotParentDistinct:=p.slotParentDistinct,
    slotFree:=by rw [p.trackerGlobal,family.emptyProtections];rfl,
    mutable:=p.mutable,
    storage:=p.storage,
    maskLength:=p.maskLength,
    provenance:=p.provenance,
    noBackend:=p.noBackend,
    extras:=p.extras,
    thread:=p.thread,
    active:=p.active,
    noCache:=p.noCache,
    source:=p.source,
    mode:=p.mode,
    unchecked:=p.unchecked,
    noGc:=p.noGc,
    fixed:=p.fixed,
    initialState:=by simpa only [p.entryTree] using rows.structural,
    bufferSize:=p.bufferSize,
    mapAligned:=by simpa only [p.entryTree] using rows.mapAligned,
    nodeRoom:=by simpa only [p.entryTree] using p.nodeRoom,
    scope:=by intro index;change index∈roots↔index∈rows.head::rows.extraRoots;rw [←rows.split],
    allLeaves:=by simpa only [p.entryTree,p.trackerGlobal] using rows.allLeaves,
    slotTagFresh:=future_fresh p family _ (UInt64.le_iff_toNat_le.mpr (by have n:=t.slotValue;omega)),
    sharedTagFresh:=future_fresh p family _ (UInt64.le_iff_toNat_le.mpr (by have n:=t.sharedValue;omega)),
    slotTagDifferent:=by intro same;have e:=congrArg (fun tag : BorTag=>tag.value.toNat) same;have n:=t.slotValue;omega,
    sharedTagDifferent:=by intro same;have e:=congrArg (fun tag : BorTag=>tag.value.toNat) same;have n:=t.sharedValue;omega,
    sharedFresh:=t.sharedFresh,
    preciseOff:=p.preciseOff,
    implicitOff:=p.implicitOff,
    writeContext:=p.writeContext,
    validationContext:=p.validationContext,
    accessEq:=p.accessEq,
    validationWidth:=p.validationWidth,
    validationRuntimeSize:=p.validationRuntimeSize,
    sameRuntime:=p.sameRuntime,
    width:=p.width,
    runtimeWidth:=p.runtimeWidth,
    runtimeSize:=p.runtimeSize,
    outerAccessEq:=p.outerAccessEq,
    slotFits:=p.slotFits }
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardFamilyInput
