import duplicate_prefix.GenericAsMutDefaultRuntime
import duplicate_prefix.GeneralRootDefaultBoundary
namespace DuplicatePrefix.GenericAsMutDefaultToCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section

set_option autoImplicit false in
/-- Initial PC6:7 data for the append-only expression/FnEntry sequence. The
future slot and tag contracts are initial allocator and metadata facts. -/
structure DataInput where
  base : GenericAsMutDefaultCore.Input
  target : base.data.target = base.data.start.data.parent
  fresh : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag.value < 18446744073709551615
  mapFresh : GeneralBorrowTagMap.Fresh base.data.start.entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag
  nodeFresh : GeneralBorrowProtector.Fresh base.data.start.entry.allocation.extra
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag
  different : base.data.start.tracker.global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag
  expressionUnheld : base.data.start.tracker.global.protectedTags.contains base.data.start.tracker.global.nextPointerTag = false
  targetDifferent : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag ≠ base.data.targetTag
  rootDifferent : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag ≠ base.data.slotRoot
  childDifferent : base.data.slotChild ≠ (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag

set_option autoImplicit false in
structure Input where
  base : GenericAsMutDefaultCore.Input
  target : base.data.target = base.data.start.data.parent
  noFree : base.data.start.entry.allocation.extra.tagMapping.deassigned.back? = none
  room : base.data.start.entry.allocation.extra.tagMapping.mapping.size+1 ≤ 4294967295
  fresh : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag.value < 18446744073709551615
  mapFresh : GeneralBorrowTagMap.Fresh base.data.start.entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag
  nodeFresh : GeneralBorrowProtector.Fresh base.data.start.entry.allocation.extra
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag
  different : base.data.start.tracker.global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag
  futureClean : GeneralBorrowFreshFutureClean.Clean base.data.start.entry.allocation.extra
    ⟨UInt32.ofNat (base.data.start.entry.allocation.extra.tagMapping.mapping.size+1)⟩
  expressionUnheld : base.data.start.tracker.global.protectedTags.contains base.data.start.tracker.global.nextPointerTag = false
  targetDifferent : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag ≠ base.data.targetTag
  rootDifferent : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag ≠ base.data.slotRoot
  childDifferent : base.data.slotChild ≠ (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag

/-- Build the entire following call's input from the pre-expression tree and
actual statement result; no post-expression graph/ownership is assumed. -/
def prepare_data (input : DataInput)
    (next : GenericAsMutPtrEntryValidity.Data
      (GenericAsMutDefaultRuntime.entry input.base.data.start).allocation.extra
      input.base.data.start.tracker.global.protectedTags input.base.data.start.tracker.global.nextPointerTag
      (ReferenceBorrowDriver.allocatedTracker input.base.data.start.tracker input.base.data.start.fresh).global.nextPointerTag
      input.base.data.start.offset input.base.data.start.len)
    (nextParent : next.parent = GeneralBorrowFreshDefaultSequence.index (GenericAsMutDefaultCore.first input.base.data.start))
    (nextClean : GeneralBorrowFreshFutureClean.Clean
      (GenericAsMutDefaultRuntime.entry input.base.data.start).allocation.extra
      (GeneralBorrowFreshMutableStages.slot_index next.slot))
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin
      (GenericAsMutDefaultRuntime.entry input.base.data.start).allocation.extra input.base.data.start.data.parent .Write
      input.base.data.start.offset (input.base.data.start.offset+input.base.data.start.len)) :
    let s := input.base.data.start
    Σ' call : GenericAsMutCallToReturn.Input,
      call.caller = GenericAsMutDefaultCore.frame input.base ∧
      call.data.start.machine = GenericAsMutDefaultCore.machine s ∧
      PreparedContracts.actualConfig call.data.start.options () (call.data.start.remaining+1) call.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧
      call.data.start.limits = s.limits := by
  let s := input.base.data.start
  let first := GenericAsMutDefaultCore.first s
  let metadata := GeneralRootDefaultMetadata.build s.entry.allocation.extra s.tracker.global.nextPointerTag s.data.parent
    s.tracker.global.protectedTags s.offset s.len first.nonzero first first.bounds s.data.owned
  have paths := GeneralRootDefaultPathFacts.build s.entry.allocation.extra s.tracker.global.nextPointerTag s.data.parent
    s.tracker.global.protectedTags s.offset s.len first.nonzero first first.bounds s.data.owned input.expressionUnheld
  let targetNode := Classical.choose paths.2.1
  have targetFacts := Classical.choose_spec paths.2.1
  have targetPresent := targetFacts.1
  have targetTag := targetFacts.2.1
  have targetExposure := targetFacts.2.2
  have oldPresent : s.entry.allocation.extra.nodeAt s.data.parent = some input.base.data.targetNode := by
    rw [←input.target]
    exact input.base.data.targetPresent
  have oldNode : s.data.node = input.base.data.targetNode := Option.some.inj (s.data.parentPresent.symm.trans oldPresent)
  let core := GenericAsMutDefaultRuntime.core s input.fresh next nextClean metadata.capacity
  have rows := GenericAsMutDefaultRuntime.locals s
  let data : GenericAsMutInvocation.Input := by
    refine {input.base.data with
      start := core, targetNode := targetNode, targetPresent := ?_, targetNotExposed := ?_
      targetNotHelper := input.targetDifferent, targetTagPresent := ?_, targetWithin := ?_, subset := ?_, escaping := ?_
      zero := ?_, slotPresent := ?_, slotRootNotHelper := input.rootDifferent, slotChildNotHelper := input.childDifferent }
    · change (GenericAsMutDefaultRuntime.entry s).allocation.extra.nodeAt input.base.data.target = some targetNode
      rw [input.target]
      exact targetPresent
    · rw [targetExposure]
      change s.data.node.isExposed = false
      rw [oldNode]
      exact input.base.data.targetNotExposed
    · exact (paths.1 input.base.data.targetTag input.base.data.targetNotHelper).trans input.base.data.targetTagPresent
    · change GeneralBorrowFreshActiveWithin.ActiveWithin _ input.base.data.target .Write s.offset (s.offset+s.len)
      rw [input.target]
      exact targetActive
    · intro location position member
      have parent : core.data.parent = GeneralBorrowFreshDefaultSequence.index first := nextParent
      rw [parent]
      rw [input.target] at member
      exact paths.2.2.1 location position member
    · intro location index node present localChild foreignTarget
      have parent : core.data.parent = GeneralBorrowFreshDefaultSequence.index first := nextParent
      rw [parent] at localChild
      rw [input.target] at foreignTarget
      exact paths.2.2.2 location index node present localChild foreignTarget
    · change (GenericAsMutDefaultRuntime.caller s).locals[0]? = _
      rw [rows]
      simpa only [Array.getElem?_set,show ¬ ((16 : Nat) = 0) from by decide,ite_false] using input.base.data.zero
    · exact StackPopRelease.lookup_commit_other s.machine.memory s.id input.base.data.slotId s.entry input.base.data.slot _
        input.base.data.separate input.base.data.slotPresent
  have frameShape := GenericRootDefaultBorrow.frame_shape input.base.caller (RootReferenceInfo.layout false) input.base.valid16 (GenericAsMutDefaultCore.value s)
  have rawSize : (GenericAsMutDefaultCore.frame input.base).locals.size = input.base.caller.locals.size := frameShape.1
  have valid15 : (15 : MIR.LocalId) < (GenericAsMutDefaultCore.frame input.base).locals.size := by rw [rawSize];exact input.base.valid15
  have valid16 : (16 : MIR.LocalId) < (GenericAsMutDefaultCore.frame input.base).locals.size := by rw [rawSize];exact input.base.valid16
  have cached : s.caller = AsMutUncachedCall.cachedCaller input.base.caller input.base.valid15 := input.base.cached
  have coreCaller : core.caller = GenericAsMutDefaultRuntime.caller s := rfl
  have cacheEq : core.caller = AsMutUncachedCall.cachedCaller (GenericAsMutDefaultCore.frame input.base) valid15 := by
    have commute := GenericAsMutDefaultFrame.cache_write input.base.caller 15 16 (by decide) input.base.valid15 input.base.valid16
      CopyCompilerFacts.destPointerLayout (RootReferenceInfo.layout false) (GenericAsMutDefaultCore.value s) ⟨6,7⟩
    rw [coreCaller]
    simpa only [GenericAsMutDefaultCore.frame,GenericAsMutDefaultRuntime.caller,cached,AsMutUncachedCall.cachedCaller] using commute.symm
  let call : GenericAsMutCallToReturn.Input := by
    refine {
      data := data, caller := GenericAsMutDefaultCore.frame input.base, valid15 := valid15, cached := cacheEq
      live15 := ?_, uncached15 := ?_, location := frameShape.2.1, valid16 := valid16, value16 := ?_, cached16 := ?_ }
    · have row := frameShape.2.2.2.2 15 (by decide)
      have old : input.base.caller.locals[15]? = some input.base.caller.locals[15] := Array.getElem?_eq_getElem input.base.valid15
      rw [old] at row
      have got : (GenericAsMutDefaultCore.frame input.base).locals[15] = input.base.caller.locals[15] :=
        Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans row)
      rw [got]
      exact input.base.live15
    · have row := frameShape.2.2.2.2 15 (by decide)
      rw [Array.getElem?_eq_getElem input.base.valid15] at row
      have got := Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans row)
      rw [got]
      exact input.base.uncached15
    · have row := frameShape.2.2.1
      change (GenericAsMutDefaultCore.frame input.base).locals[16]?.map (fun slot => slot.value) = some (.live (.immediate (GenericAsMutDefaultCore.value s))) at row
      rw [Array.getElem?_eq_getElem valid16] at row
      exact Option.some.inj row
    · have row := frameShape.2.2.2.1
      change (GenericAsMutDefaultCore.frame input.base).locals[16]?.map (fun slot => slot.layout) = some (some ActualReferenceMetadata.reference) at row
      rw [Array.getElem?_eq_getElem valid16] at row
      exact Option.some.inj row
  exact ⟨call,rfl,rfl,rfl,rfl⟩
/-- Preserve the append-only public API by constructing its structural data and
passing them to the shared runtime/frame adapter. -/
def prepare (input : Input) :
    let s := input.base.data.start
    Σ' call : GenericAsMutCallToReturn.Input,
      call.caller = GenericAsMutDefaultCore.frame input.base ∧
      call.data.start.machine = GenericAsMutDefaultCore.machine s ∧
      PreparedContracts.actualConfig call.data.start.options () (call.data.start.remaining+1) call.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧
      call.data.start.limits = s.limits := by
  let s := input.base.data.start
  let first := GenericAsMutDefaultCore.first s
  have active : GeneralBorrowFreshActiveWithin.ActiveWithin s.entry.allocation.extra s.data.parent .Write s.offset (s.offset+s.len) := by
    rw [←input.target]
    exact input.base.data.targetWithin
  let supplied := GeneralRootDefaultNext.build s.entry.allocation.extra s.tracker.global.nextPointerTag
    (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh).global.nextPointerTag s.data.parent s.tracker.global.protectedTags
    s.offset s.len first.nonzero first first.bounds s.data.owned active input.noFree input.room input.mapFresh input.nodeFresh
    input.different input.futureClean
  let common : DataInput := ⟨input.base,input.target,input.fresh,input.mapFresh,input.nodeFresh,input.different,
    input.expressionUnheld,input.targetDifferent,input.rootDifferent,input.childDifferent⟩
  exact prepare_data common supplied.1 rfl supplied.2.1 supplied.2.2

end
end DuplicatePrefix.GenericAsMutDefaultToCall
