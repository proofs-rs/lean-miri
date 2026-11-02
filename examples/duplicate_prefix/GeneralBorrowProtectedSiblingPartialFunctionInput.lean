import duplicate_prefix.GeneralBorrowProtectedSiblingForestEntry
import duplicate_prefix.GeneralBorrowProtectedSiblingPartialFunctionHistory
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialFunctionInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext GenericFunctionEntryState GeneralRangeMapState
open GeneralBorrowProtectedSiblingFunctionCaller GeneralBorrowProtectedSiblingFunctionNumerics GeneralBorrowProtectedSiblingPartialFunctionHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def assemble {bytes : UInt64} {windows : List (GeneralBorrowProtectedSiblingPartial.Window bytes)} (nonzero : bytes ≠ 0) (room : windows.length+10 ≤ 4294967295)
    (history : History bytes windows) (s : Caller history.output.tree history.output.ended bytes) :
    GeneralBorrowForestAllCountInput.Initial := by
  have empty : s.tracker.global.protectedTags = {} := by rw [s.globalEq,history.empty]
  have free : s.tracker.global.protectedTags.contains s.slotRoot = false := by rw [empty];rfl
  have roomTree : history.output.tree.nodes.size+8 ≤ 4294967295 := by rw [history.nodes];omega
  let data : GeneralBorrowForestEntryValidity.Data s.entry.allocation.extra s.tracker.global.protectedTags s.parentTag
      s.tracker.global.nextPointerTag s.offset s.len := by
    rw [s.treeEq,s.globalEq,s.parentEq,s.offsetEq,s.lenEq]
    exact GeneralBorrowProtectedSiblingForestEntry.build history.output.tree history.output.ended.protectedTags
      GeneralBorrowFullSharedSeed.root history.rootNode BorTag.one history.output.ended.nextPointerTag bytes history.rootPresent history.rootTag
      history.depth history.children history.covered history.roots history.hidden history.allocator roomTree history.well
      (by simpa only [tag,s.globalEq] using tag_fresh s history.below 0) (by rw [history.empty];rfl) history.owned
  have clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) = none)
      s.entry.allocation.extra.locations :=
    GeneralBorrowProtectedSiblingForestEntry.clean _ _ _ _ _ _ data (by rw [s.treeEq];exact history.vacant)
  refine {
    options := s.options,
    limits := s.limits,
    remaining := s.remaining,
    span := s.span,
    ctx := s.ctx,
    debugOff := s.debugOff,
    cmp := s.cmp,
    dynamicFuel := s.dynamicFuel,
    validityFuel := s.validityFuel,
    fuelEq := s.fuelEq,
    validationEq := s.validationEq,
    id := s.id,
    parentTag := s.parentTag,
    tracker := s.tracker,
    base := s.base,
    offset := s.offset,
    len := s.len,
    nonzero := s.nonzero,
    entry := s.entry,
    signedFits := s.signedFits,
    before := s.before,
    ghost := s.ghost,
    shallow := s.shallow,
    cachedAddress := s.cachedAddress,
    present := s.present,
    enabled := s.enabled,
    fresh := s.fresh,
    race := s.race,
    metadata := s.metadata,
    notConstructed := s.notConstructed,
    retagCtx := s.retagCtx,
    place := s.place,
    layout := s.layout,
    slotId := s.slotId,
    slotEntry := s.slotEntry,
    slotBase := s.slotBase,
    slotRoot := s.slotRoot,
    slotPointer := s.slotPointer,
    aligned := s.aligned,
    slotCached := s.slotCached,
    slotTree := s.slotTree,
    slotSize := s.slotSize,
    slotPresent := s.slotPresent,
    separate := s.separate,
    slotFresh := s.slotFresh,
    slotDistinct := s.slotDistinct,
    slotParentDistinct := s.slotParentDistinct,
    mutable := s.mutable,
    storage := s.storage,
    maskLength := s.maskLength,
    provenance := s.provenance,
    noBackend := s.noBackend,
    extras := s.extras,
    thread := s.thread,
    active := s.active,
    noCache := s.noCache,
    source := s.source,
    mode := s.mode,
    unchecked := s.unchecked,
    noGc := s.noGc,
    fixed := s.fixed,
    successorDifferent := s.successorDifferent,
    writeContext := s.writeContext,
    validationContext := s.validationContext,
    accessEq := s.accessEq,
    validationWidth := s.validationWidth,
    validationRuntimeSize := s.validationRuntimeSize,
    sameRuntime := s.sameRuntime,
    width := s.width,
    runtimeWidth := s.runtimeWidth,
    runtimeSize := s.runtimeSize,
    outerAccessEq := s.outerAccessEq,
    slotFits := s.slotFits,
    count := s.count,
    preciseOff := s.preciseOff,
    implicitOff := s.implicitOff,
    budget := s.budget,
    dispatchFuel := s.dispatchFuel,
    fresh3 := s.fresh3,
    fresh4 := s.fresh4,
    statementFuel := s.statementFuel,
    rootExprDifferent := s.rootExprDifferent,
    rootHelperDifferent := s.rootHelperDifferent,
    storageBuffer := s.storageBuffer,
    maskValidBuffer := s.maskValidBuffer,
    maskLengthBuffer := s.maskLengthBuffer,
    initializedBuffer := s.initializedBuffer,
    provenanceBuffer := s.provenanceBuffer,
    storageFitsBuffer := s.storageFitsBuffer,
    mutableBuffer := s.mutableBuffer,
    bufferExtras := s.bufferExtras,
    bounded := s.bounded,
    fresh5 := s.fresh5,
    fresh6 := s.fresh6,
    rootDifferent5 := s.rootDifferent5,
    rootDifferent6 := s.rootDifferent6,
    exprDifferent5 := s.exprDifferent5,
    exprDifferent6 := s.exprDifferent6,
    helperDifferent5 := s.helperDifferent5,
    helperDifferent6 := s.helperDifferent6,
    different56 := s.different56,
    slotRootDifferent5 := s.slotRootDifferent5,
    slotRootDifferent6 := s.slotRootDifferent6,
    slotChildDifferent5 := s.slotChildDifferent5,
    slotChildDifferent6 := s.slotChildDifferent6,
    data := data,clean := clean,
    positive := (by rw [s.lenEq];exact UInt64.pos_iff_ne_zero.mpr nonzero),
    bounds := (by rw [s.offsetEq,s.lenEq,s.byteSizeEq];change 0+bytes.toNat ≤ bytes.toNat;omega),
    capacity := (by rw [s.treeEq,s.byteSizeEq];exact history.capacity),slotFree := free,
    successorFresh := GeneralBorrowFullSharedResources.protector_fresh _
      (by rw [s.treeEq];exact history.allocator.nodeTags) _
      (by rw [s.treeEq];exact tag_fresh s history.below 1),
    allocator := (by rw [s.treeEq];exact history.allocator),
    room := (by rw [s.treeEq];exact roomTree),vacantClean := (by rw [s.treeEq];exact history.vacant),
    exprFresh := (by rw [s.treeEq];exact tag_fresh s history.below 2),
    helperFresh := (by rw [s.treeEq];exact tag_fresh s history.below 3),
    map5 := (by rw [s.treeEq];exact tag_fresh s history.below 4),
    map6 := (by rw [s.treeEq];exact tag_fresh s history.below 5),
    exprUnheld := congrArg Option.isSome (unheld s history.empty 2 (by decide)),
    helperUnheld := unheld s history.empty 3 (by decide),
    unheld5 := unheld s history.empty 4 (by decide),unheld6 := unheld s history.empty 5 (by decide),
    rootFreeAfterHelper := (by
      exact (congrArg (fun protections : ProtectedTags => protections.contains s.slotRoot) (helper_table s history.empty)).trans
        (GenericFunctionEntryState.buffer_root_free s.tracker s.fresh s.slotFresh s.slotRoot s.slotParentDistinct s.slotDistinct free)),
    slotHeldAfterHelper := (by
      apply (congrArg (fun protections : ProtectedTags => protections.contains (tag s 1)) (helper_table s history.empty)).trans
      change ((s.tracker.global.protectedTags.insert (tag s 0) .StrongProtector).insert (tag s 1) .StrongProtector).contains (tag s 1) = true
      simp [ProtectedTags.contains]) }
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialFunctionInput
