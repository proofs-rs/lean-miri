import duplicate_prefix.GeneralBorrowForestAsMutDefaultRuntime
import duplicate_prefix.GeneralBorrowForestAsMutDefaultPathFacts
import duplicate_prefix.GeneralBorrowForestAsMutDefaultTargetPath
import duplicate_prefix.GeneralBorrowForestDefaultStageNext
import duplicate_prefix.GeneralBorrowForestDefaultStageTargetActivity
namespace DuplicatePrefix.GeneralBorrowForestAsMutDefaultToCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure Input where
  base : GeneralBorrowForestAsMutDefaultCore.Input
  target : base.data.target = base.data.start.data.parent
  fresh : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag.value < 18446744073709551615
  allocator : GeneralBorrowGcAllocator.Invariant base.data.start.entry.allocation.extra
  vacantClean : GeneralBorrowGcVacantClean.VacantClean base.data.start.entry.allocation.extra
  room : base.data.start.entry.allocation.extra.nodes.size+5 ≤ 4294967295
  mapFresh : GeneralBorrowTagMap.Fresh base.data.start.entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag
  different : base.data.start.tracker.global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag
  unheld : base.data.start.tracker.global.protectedTags.get
    (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag = none
  expressionUnheld : base.data.start.tracker.global.protectedTags.contains base.data.start.tracker.global.nextPointerTag = false
  targetDifferent : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag ≠ base.data.targetTag
  rootDifferent : (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag ≠ base.data.slotRoot
  childDifferent : base.data.slotChild ≠ (ReferenceBorrowDriver.allocatedTracker base.data.start.tracker base.data.start.fresh).global.nextPointerTag

def prepare_data (input : Input)
    (next : GeneralBorrowForestEntryValidity.Data
      (GeneralBorrowForestAsMutDefaultRuntime.entry input.base.data.start).allocation.extra
      input.base.data.start.tracker.global.protectedTags input.base.data.start.tracker.global.nextPointerTag
      (ReferenceBorrowDriver.allocatedTracker input.base.data.start.tracker input.base.data.start.fresh).global.nextPointerTag
      input.base.data.start.offset input.base.data.start.len)
    (nextParent : next.parent = GeneralBorrowForestAsMutDefaultSequence.index (GeneralBorrowForestAsMutDefaultCore.first input.base.data.start))
    (nextPrimary : next.primary = input.base.data.start.data.primary)
    (nextClean : GeneralBorrowFreshFutureClean.Clean
      (GeneralBorrowForestAsMutDefaultRuntime.entry input.base.data.start).allocation.extra
      (GeneralBorrowFreshMutableStages.slot_index next.slot))
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin
      (GeneralBorrowForestAsMutDefaultRuntime.entry input.base.data.start).allocation.extra input.base.data.start.data.parent .Write
      input.base.data.start.offset (input.base.data.start.offset+input.base.data.start.len)) :
    let s := input.base.data.start
    Σ' call : GeneralBorrowForestAsMutCallToReturn.Input,
      call.caller = GeneralBorrowForestAsMutDefaultCore.frame input.base ∧
      call.data.start.machine = GeneralBorrowForestAsMutDefaultCore.machine s ∧
      PreparedContracts.actualConfig call.data.start.options () (call.data.start.remaining+1) call.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧
      call.data.start.limits = s.limits := by
  let s := input.base.data.start
  let first := GeneralBorrowForestAsMutDefaultCore.first s
  have constructed := GeneralBorrowForestDefault.run s.entry.allocation.extra s.tracker.global.protectedTags first.parentTag s.tracker.global.nextPointerTag
    s.data.parent first.primary first.extras s.offset s.len .VisitChildrenOfAccessed first.context first.covered first.parentTagPresent first.tagFresh first.slot first.nodeFits first.nonzero first.well first.bounds s.data.owned
  have capacity : (GeneralBorrowForestAsMutDefaultSequence.child first s.tracker.global.protectedTags).tree.locations.size = s.entry.allocation.extra.locations.size := constructed.2.2.2.2.2.2.1
  have paths := GeneralBorrowForestAsMutDefaultPathFacts.build s.entry.allocation.extra s.tracker.global.nextPointerTag s.data.parent
    s.tracker.global.protectedTags s.offset s.len first.nonzero first first.bounds s.data.owned input.expressionUnheld
  let targetNode := Classical.choose paths.2.1
  have targetFacts := Classical.choose_spec paths.2.1
  have targetPresent := targetFacts.1
  have targetTag := targetFacts.2.1
  have targetExposure := targetFacts.2.2
  have oldPresent : s.entry.allocation.extra.nodeAt s.data.parent = some input.base.data.targetNode := by
    rw [←input.target]
    exact input.base.data.targetPresent
  have oldNode : s.data.context.anchorNode = input.base.data.targetNode := Option.some.inj (s.data.context.anchorPresent.symm.trans oldPresent)
  let core := GeneralBorrowForestAsMutDefaultRuntime.core s input.fresh next nextClean capacity
  have rows := GeneralBorrowForestAsMutDefaultRuntime.locals s
  let data : GeneralBorrowForestAsMutInvocation.Input := by
    refine {input.base.data with
      start := core, targetNode := targetNode, targetPresent := ?_, targetNotExposed := ?_
      targetNotHelper := input.targetDifferent, targetTagPresent := ?_, targetRootPath := ?_, targetWithin := ?_, subset := ?_, escaping := ?_
      zero := ?_, slotPresent := ?_, slotRootNotHelper := input.rootDifferent, slotChildNotHelper := input.childDifferent }
    · change (GeneralBorrowForestAsMutDefaultRuntime.entry s).allocation.extra.nodeAt input.base.data.target = some targetNode
      rw [input.target]
      exact targetPresent
    · rw [targetExposure]
      change s.data.context.anchorNode.isExposed = false
      rw [oldNode]
      exact input.base.data.targetNotExposed
    · exact (paths.1 input.base.data.targetTag input.base.data.targetNotHelper).trans input.base.data.targetTagPresent
    · intro location
      change ((source_normal_projection (GeneralBorrowForestAsMutDefaultSequence.child first s.tracker.global.protectedTags).tree
        location s.tracker.global.protectedTags).topology.ancestorPath input.base.data.target.toNat).getLast! = next.primary.toNat
      rw [nextPrimary,input.target]
      have path := GeneralBorrowForestAsMutDefaultTargetPath.parent_path s.entry.allocation.extra s.tracker.global.nextPointerTag s.data.parent
        s.tracker.global.protectedTags s.offset s.len first.nonzero first first.bounds s.data.owned input.expressionUnheld location
      rw [path]
      rw [←input.target]
      exact input.base.data.targetRootPath location
    · change GeneralBorrowFreshActiveWithin.ActiveWithin _ input.base.data.target .Write s.offset (s.offset+s.len)
      rw [input.target]
      exact targetActive
    · intro location position member
      have parent : core.data.parent = GeneralBorrowForestAsMutDefaultSequence.index first := nextParent
      rw [parent]
      rw [input.target] at member
      exact paths.2.2.1 location position member
    · intro location index node present localChild foreignTarget
      have parent : core.data.parent = GeneralBorrowForestAsMutDefaultSequence.index first := nextParent
      rw [parent] at localChild
      rw [input.target] at foreignTarget
      exact paths.2.2.2 location index node present localChild foreignTarget
    · change (GeneralBorrowForestAsMutDefaultRuntime.caller s).locals[0]? = _
      rw [rows]
      simpa only [Array.getElem?_set,show ¬ ((16 : Nat) = 0) from by decide,ite_false] using input.base.data.zero
    · exact StackPopRelease.lookup_commit_other s.machine.memory s.id input.base.data.slotId s.entry input.base.data.slot _
        input.base.data.separate input.base.data.slotPresent
  have frameShape := GeneralBorrowForestAsMutDefaultBorrow.frame_shape input.base.caller (RootReferenceInfo.layout false) input.base.valid16 (GeneralBorrowForestAsMutDefaultCore.value s)
  have rawSize : (GeneralBorrowForestAsMutDefaultCore.frame input.base).locals.size = input.base.caller.locals.size := frameShape.1
  have valid15 : (15 : MIR.LocalId) < (GeneralBorrowForestAsMutDefaultCore.frame input.base).locals.size := by rw [rawSize];exact input.base.valid15
  have valid16 : (16 : MIR.LocalId) < (GeneralBorrowForestAsMutDefaultCore.frame input.base).locals.size := by rw [rawSize];exact input.base.valid16
  have cached : s.caller = AsMutUncachedCall.cachedCaller input.base.caller input.base.valid15 := input.base.cached
  have coreCaller : core.caller = GeneralBorrowForestAsMutDefaultRuntime.caller s := rfl
  have cacheEq : core.caller = AsMutUncachedCall.cachedCaller (GeneralBorrowForestAsMutDefaultCore.frame input.base) valid15 := by
    have commute := GeneralBorrowForestAsMutDefaultFrame.cache_write input.base.caller 15 16 (by decide) input.base.valid15 input.base.valid16
      CopyCompilerFacts.destPointerLayout (RootReferenceInfo.layout false) (GeneralBorrowForestAsMutDefaultCore.value s) ⟨6,7⟩
    rw [coreCaller]
    simpa only [GeneralBorrowForestAsMutDefaultCore.frame,GeneralBorrowForestAsMutDefaultRuntime.caller,cached,AsMutUncachedCall.cachedCaller] using commute.symm
  let call : GeneralBorrowForestAsMutCallToReturn.Input := by
    refine {
      data := data, caller := GeneralBorrowForestAsMutDefaultCore.frame input.base, valid15 := valid15, cached := cacheEq
      live15 := ?_, uncached15 := ?_, location := frameShape.2.1, valid16 := valid16, value16 := ?_, cached16 := ?_ }
    · have row := frameShape.2.2.2.2 15 (by decide)
      have old : input.base.caller.locals[15]? = some input.base.caller.locals[15] := Array.getElem?_eq_getElem input.base.valid15
      rw [old] at row
      have got : (GeneralBorrowForestAsMutDefaultCore.frame input.base).locals[15] = input.base.caller.locals[15] :=
        Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans row)
      rw [got]
      exact input.base.live15
    · have row := frameShape.2.2.2.2 15 (by decide)
      rw [Array.getElem?_eq_getElem input.base.valid15] at row
      have got := Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans row)
      rw [got]
      exact input.base.uncached15
    · have row := frameShape.2.2.1
      change (GeneralBorrowForestAsMutDefaultCore.frame input.base).locals[16]?.map (fun slot => slot.value) = some (.live (.immediate (GeneralBorrowForestAsMutDefaultCore.value s))) at row
      rw [Array.getElem?_eq_getElem valid16] at row
      exact Option.some.inj row
    · have row := frameShape.2.2.2.1
      change (GeneralBorrowForestAsMutDefaultCore.frame input.base).locals[16]?.map (fun slot => slot.layout) = some (some ActualReferenceMetadata.reference) at row
      rw [Array.getElem?_eq_getElem valid16] at row
      exact Option.some.inj row
  exact ⟨call,rfl,rfl,rfl,rfl⟩
def prepare (input : Input) :
    let s := input.base.data.start
    Σ' call : GeneralBorrowForestAsMutCallToReturn.Input,
      call.caller = GeneralBorrowForestAsMutDefaultCore.frame input.base ∧
      call.data.start.machine = GeneralBorrowForestAsMutDefaultCore.machine s ∧
      PreparedContracts.actualConfig call.data.start.options () (call.data.start.remaining+1) call.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧
      call.data.start.limits = s.limits := by
  let s := input.base.data.start
  let first := GeneralBorrowForestAsMutDefaultCore.first s
  let supplied := GeneralBorrowForestDefaultStageNext.build s.entry.allocation.extra s.tracker.global.protectedTags
    s.tracker.global.nextPointerTag (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh).global.nextPointerTag s.data.parent s.offset s.len first
    s.data.owned input.allocator input.vacantClean input.mapFresh input.different input.unheld input.room
  have targetActive := GeneralBorrowForestDefaultStageTargetActivity.preserves_target s.entry.allocation.extra s.tracker.global.protectedTags
    s.parentTag s.tracker.global.nextPointerTag s.offset s.len s.data.parent first rfl s.data.owned first.nonzero first.bounds
    s.data.parent s.offset (s.offset+s.len) (Nat.le_refl _) (Nat.le_refl _) (by rw [←input.target];exact input.base.data.targetWithin)
  have clean : GeneralBorrowFreshFutureClean.Clean (GeneralBorrowForestAsMutDefaultRuntime.entry s).allocation.extra
      (GeneralBorrowFreshMutableStages.slot_index supplied.data.slot) := by
    have eqn : GeneralBorrowFreshMetadataChildMutableSlot.index supplied.data.slot = GeneralBorrowFreshMutableStages.slot_index supplied.data.slot := by cases supplied.data.slot <;> rfl
    rw [←eqn]
    exact supplied.clean
  exact prepare_data input supplied.data rfl rfl clean targetActive
end
end DuplicatePrefix.GeneralBorrowForestAsMutDefaultToCall
