import duplicate_prefix.GeneralBorrowPositiveWildcardWindowPhysical
import duplicate_prefix.GeneralBorrowSparseExposedRootFormation
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAllCountInput
import duplicate_prefix.GeneralBorrowProtectorCacheMap
import duplicate_prefix.ProtectorInsertion
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowFamilyInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open GeneralBorrowPositiveWildcardWindowPhysical
open GeneralBorrowSparseExposedRootFormation (State)
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {capacity : UInt64}

theorem node_tag_below (state : State capacity) (index : UniIndex) (node : TreeNode)
    (present : state.tree.nodeAt index=some node) : node.tag.value<state.global.nextPointerTag.value := by
  have tagged:=state.structural.allocator.nodeTags index node present
  unfold UniKeyMap.get at tagged
  cases looked : state.tree.tagMapping.mapping.find? (fun row=>row.1==node.tag) with
  | none => simp [looked] at tagged
  | some row =>
    have key : row.1=node.tag := by simpa only [beq_iff_eq] using Array.find?_some looked
    have bound:=state.below row (Array.mem_of_find?_eq_some looked)
    rw [key] at bound
    exact UInt64.lt_iff_toNat_lt.mpr bound

theorem all_leaves (state : State capacity) :
    ∀ root∈state.primary::state.extras,∃node,state.tree.nodeAt root=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
      node.tag.value≤state.global.nextPointerTag.value := by
  intro root member
  obtain ⟨node,present⟩:=state.geometry.present root member
  have shape:=state.geometry.nodes root node present
  exact ⟨node,present,shape.2.1,shape.2.2,UInt64.le_of_lt (node_tag_below state root node present)⟩

theorem registered_raw (state : State capacity) :
    GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw state.tree location
      (state.global.protectedTags.insert state.global.nextPointerTag .StrongProtector)) state.tree.locations := by
  have fresh : ∀ index node,state.tree.nodeAt index=some node→node.tag≠state.global.nextPointerTag := by
    intro index node present same
    have smaller:=node_tag_below state index node present
    rw [same] at smaller
    exact UInt64.lt_irrefl _ smaller
  intro position valid
  have raw:=state.raw position valid
  refine ⟨?_,?_⟩
  · apply GeneralBorrowProtectorCacheMap.register state.tree _ state.global.protectedTags state.global.nextPointerTag .StrongProtector raw.1
    intro index node present same
    exact False.elim (fresh index node present same)
  · intro index node present
    rw [ProtectorInsertion.contains_other state.global.protectedTags state.global.nextPointerTag node.tag .StrongProtector (fresh index node present)]
    exact raw.2 index node present

theorem future_fresh (state : State capacity) (p : Caller capacity state.global state.tree)
    (tag : BorTag) (above : p.tracker.global.nextPointerTag.value≤tag.value) :
    GeneralBorrowTagMap.Fresh p.entry.allocation.extra.tagMapping tag := by
  rw [p.entryTree]
  apply GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ state.below tag
  simpa only [p.trackerGlobal] using UInt64.le_iff_toNat_le.mp above

/-- Source-generated mixed/sparse rows provide all borrow-side data for the actual interior window. Caller
contains only the reusable physical/compiler/storage and numeric reserve data. -/
def base (state : State capacity) (p : Caller capacity state.global state.tree)
    (nonzero : capacity≠0) (empty : state.global.protectedTags={}) :
    @GeneralBorrowPositiveWildcardWindowOriginalInput.Base (scope (state.primary::state.extras)) := by
  letI : GeneralBorrowExposedKnownRootState.Scope:=scope (state.primary::state.extras)
  let t:=tags p
  have slotValue : (GeneralBorrowPositiveWildcardSparseFunctionState.next p.tracker t.fresh).global.nextPointerTag.value.toNat=
      p.tracker.global.nextPointerTag.value.toNat+1 := t.slotValue
  have sharedValue : (GeneralBorrowPositiveWildcardSparseFunctionState.held p.tracker t.fresh t.slotFresh).global.nextPointerTag.value.toNat=
      p.tracker.global.nextPointerTag.value.toNat+2 := t.sharedValue
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
    capacity:=capacity,
    offset:=p.offset,
    len:=p.len,
    count:=p.count,
    nonzero:=p.nonzero,
    entry:=p.entry,
    positive:=p.positive,
    signedFits:=p.signedFits,
    bounds:=p.bounds,
    addressFits:=p.addressFits,
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
    beforeNext:=p.beforeNext,
    addressMode:=p.addressMode,
    exposedAlloc:=p.exposedAlloc,
    head:=state.primary,
    extraRoots:=state.extras,
    roots:=by simpa only [p.entryTree] using state.geometry.roots,
    short:=by rw [p.entryTree];have room:=p.nodeRoom;omega,
    tagFresh:=by simpa only [p.entryTree,p.trackerGlobal] using GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ state.below state.global.nextPointerTag (Nat.le_refl _),
    noFree:=by simpa only [p.entryTree] using state.noFree,
    fits:=by rw [p.entryTree,state.aligned];change state.tree.nodes.size≤4294967295;have room:=p.nodeRoom;omega,
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
    slotFree:=by rw [p.trackerGlobal,empty];rfl,
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
    initialState:=by simpa only [p.entryTree] using state.structural,
    bufferSize:=p.bufferSize,
    mapAligned:=by simpa only [p.entryTree] using state.aligned,
    nodeRoom:=by simpa only [p.entryTree] using p.nodeRoom,
    scope:=fun _=>Iff.rfl,
    allLeaves:=by simpa only [p.entryTree,p.trackerGlobal] using all_leaves state,
    slotTagFresh:=future_fresh state p _ (UInt64.le_iff_toNat_le.mpr (by have n:=slotValue;omega)),
    sharedTagFresh:=future_fresh state p _ (UInt64.le_iff_toNat_le.mpr (by have n:=sharedValue;omega)),
    slotTagDifferent:=by intro same;have e:=congrArg (fun tag : BorTag=>tag.value.toNat) same;have n:=slotValue;omega,
    sharedTagDifferent:=by intro same;have e:=congrArg (fun tag : BorTag=>tag.value.toNat) same;have n:=sharedValue;omega,
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
    slotFits:=p.slotFits,
    allocationCapacity:=by rw [p.entryTree,state.capacityEq];rfl,
    leafGeometry:=by simpa only [p.entryTree] using state.geometry,
    sourceRaw:=by simpa only [p.entryTree,p.trackerGlobal,TypedBorrowSteps.registeredGlobal] using registered_raw state }

/-- Source cleanliness, highwater bounds and the common numeric plan supply
all all-count reserves without exact stored rows or post-operation premises. -/
def initial (state : State capacity) (p : Caller capacity state.global state.tree)
    (nonzero : capacity≠0) (empty : state.global.protectedTags={}) :
    @GeneralBorrowPositiveWildcardWindowAllCountInput.Initial (scope (state.primary::state.extras)) := by
  letI : GeneralBorrowExposedKnownRootState.Scope:=scope (state.primary::state.extras)
  let b:=base state p nonzero empty
  let t:=tags p
  have unheld (tag : BorTag) : p.tracker.global.protectedTags.contains tag=false := by
    rw [p.trackerGlobal,empty]
    rfl
  exact {
    toBase:=b,statementFuel:=p.statementFuel,budget:=p.budget,dispatchFuel:=p.dispatchFuel,
    vacantClean:=by change GeneralBorrowGcVacantClean.VacantClean p.entry.allocation.extra;simpa only [p.entryTree] using state.clean,
    helperMapFresh:=future_fresh state p _
      (UInt64.le_iff_toNat_le.mpr (by change p.tracker.global.nextPointerTag.value.toNat≤(GeneralBorrowPositiveWildcardFamilyTags.expression p.tracker t.fresh t.slotFresh t.sharedFresh).global.nextPointerTag.value.toNat;have n:=t.helperValue;omega)),
    helperFresh:=t.helperFresh,expressionUnheld:=unheld _,helperUnheld:=unheld _,
    mutableFresh:=t.mutableFresh,mutableHelperFresh:=t.mutableHelperFresh,
    mutableMapFresh:=future_fresh state p _
      (UInt64.le_iff_toNat_le.mpr (by change p.tracker.global.nextPointerTag.value.toNat≤(GeneralBorrowPositiveWildcardFamilyTags.ended p.tracker t.fresh t.slotFresh t.sharedFresh t.helperFresh p.id).global.nextPointerTag.value.toNat;have n:=t.mutableValue;omega)),
    mutableHelperMapFresh:=future_fresh state p _
      (UInt64.le_iff_toNat_le.mpr (by change p.tracker.global.nextPointerTag.value.toNat≤(ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardFamilyTags.ended p.tracker t.fresh t.slotFresh t.sharedFresh t.helperFresh p.id) t.mutableFresh).global.nextPointerTag.value.toNat;have n:=t.mutableHelperValue;omega)),
    mutableUnheld:=unheld _,mutableHelperUnheld:=unheld _,
    bufferStorage:=p.bufferStorage,bufferMaskValid:=p.bufferMaskValid,bufferMaskLength:=p.bufferMaskLength,
    bufferInitialized:=p.bufferInitialized,bufferProvenance:=p.bufferProvenance,bufferStorageFits:=p.bufferStorageFits,
    bufferMutable:=p.bufferMutable,bufferExtras:=p.bufferExtras }

end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowFamilyInput
