import duplicate_prefix.GenericSharedAcceptedStages
import duplicate_prefix.GenericSharedLenAccepted
import duplicate_prefix.GeneralBorrowFreshSharedReleasedMetadata
import duplicate_prefix.GeneralBorrowFreshSharedPoolReleasedMetadata
import duplicate_prefix.GenericAsMutDefaultPoolToCall
import duplicate_prefix.GenericFunctionEntryNumerics
namespace DuplicatePrefix.GenericSharedAcceptedForm
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralRangeMapState GenericSharedAcceptedStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

set_option autoImplicit false in
/-- Data projected from the actual shared/len execution. This is a runtime
transport interface, not an assumption of the final safety theorem. -/
structure Boundary (s : GenericSharedAcceptedInput.Base) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tree : BorrowTree) : Prop where
  location : frame.location = .mir ⟨6,7⟩
  tracked : machine.borrowTracker = some (ended_base s)
  present : machine.memory.live.find? (fun row => row.1 == s.id) = some (s.id,GeneralBorrowFreshSharedPop.withTree s.entry tree)
  body : frame.body = s.frame.body
  identity : frame.bodyIdentity = s.frame.bodyIdentity
  callee : frame.functionInstance = s.frame.functionInstance
  extra : frame.extra = s.frame.extra
  size : frame.locals.size = 25
  slot1 : frame.locals[1]? = s.frame.locals[1]?
  slot2 : frame.locals[2]? = s.frame.locals[2]?
  slot15 : frame.locals[15]? = some ⟨.live (.immediate .uninit),none⟩
  slot16 : frame.locals[16]? = some ⟨.live (.immediate .uninit),none⟩
  immediate : CopyHelperCleanup.AllImmediate frame
  owned : OwnedOn (GeneralBorrowRange.LocationOwned tree (ended_base s).global.protectedTags s.target .Write) s.offset (s.offset+s.len) tree.locations
  runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.machine machine
  track : frame.trackCallerArg = s.frame.trackCallerArg
  active : GeneralBorrowFreshActiveWithin.ActiveWithin tree s.target .Write s.offset (s.offset+s.len)
  well : tree.locations.WellFormed
  capacity : tree.locations.size = s.entry.allocation.extra.locations.size
  facts : GenericSharedLenAccepted.EndpointFrameFacts s.frame frame
  memory : machine.memory = RetagEntry.updatedMemory s.machine.memory s.id s.entry tree

/-- Shared physical/runtime formation, independent of the allocator policy.
The supplied structural Data and cleanliness are derived by the thin append or
pool factory; they are not premises of the final initial-state safety API. -/
def form_data (s : GenericSharedAcceptedInput.Base) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tree : BorrowTree)
    (b : Boundary s frame machine tree)
    (data : GenericAsMutPtrEntryValidity.Data tree (ended_base s).global.protectedTags
      s.first.parentTag (ended_base s).global.nextPointerTag s.offset s.len)
    (parent : data.parent = s.target) (notExposed : data.node.isExposed = false)
    (dataClean : GeneralBorrowFreshFutureClean.Clean tree (GeneralBorrowFreshMutableStages.slot_index data.slot))
    (map4 : GeneralBorrowTagMap.Fresh tree.tagMapping (three_base s).global.nextPointerTag)
    (node4 : GeneralBorrowProtector.Fresh tree (three_base s).global.nextPointerTag) :
    Σ' ready : GenericAsMutDefaultToCall.DataInput,
      ready.base.caller = frame ∧ ready.base.data.start.machine = machine ∧
      PreparedContracts.actualConfig ready.base.data.start.options () (ready.base.data.start.remaining+1) ready.base.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.base.data.start.limits = s.limits ∧
      ready.base.data.start.entry.allocation.extra = tree := by
  have valid15 : (15 : MIR.LocalId) < frame.locals.size := by rw [b.size];decide
  let cached := AsMutUncachedCall.cachedCaller frame valid15
  have cachedSize : cached.locals.size = frame.locals.size := by simp only [cached,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  have same (index : MIR.LocalId) (different : index ≠ 15) : cached.locals[index]? = frame.locals[index]? := by
    simp only [cached,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different,ite_false]
  have row15 : cached.locals[15]? = some ⟨.live (.immediate .uninit),some CopyCompilerFacts.destPointerLayout⟩ := by
    have old := Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans b.slot15)
    simp only [cached,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set_self,old]
  have valid15c : (15 : MIR.LocalId) < cached.locals.size := by rw [cachedSize];exact valid15
  have cell15 : (cached.locals[15]'valid15c) = ⟨.live (.immediate .uninit),some CopyCompilerFacts.destPointerLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid15c).symm.trans row15)
  have immediate : CopyHelperCleanup.AllImmediate cached := by
    apply CopyHelperCleanup.all_immediate_set frame 15 {frame.locals[15] with layout := some CopyCompilerFacts.destPointerLayout} valid15 b.immediate
    intro memory
    exact b.immediate frame.locals[15] (Array.getElem_mem valid15) memory
  let thread := Classical.choose b.runtime.active
  have threadFacts := Classical.choose_spec b.runtime.active
  let localEntry := GeneralBorrowFreshSharedPop.withTree s.entry tree
  let core : GenericAsMutInvocationCore.Input := by
    refine {
      options := s.options, limits := s.limits, remaining := s.remaining, span := s.span, debug := s.debug
      fuel := s.validityFuel, validation := s.validationEq, dynamicFuel := s.dynamicFuel, dynamic := s.dynamicEq
      cmp := s.cmp, source := s.source, budget := s.budget, dispatch := s.dispatchFuel
      caller := cached, machine := machine, id := s.id, entry := localEntry, base := s.base, offset := s.offset, len := s.len
      positive := s.positive, nonzero := s.nonnull, signedFits := s.signedFits, bounds := ?_, cachedAddress := ?_, present := b.present
      parentTag := s.first.parentTag, tracker := ended_base s, tracked := b.tracked, mode := (ended_fields_base s).2.trans s.defaultMode
      ghost := b.runtime.ghost, shallow := b.runtime.shallow, race := b.runtime.race, backend := b.runtime.backend
      valid15 := valid15c, live15 := congrArg LocalState.value cell15, cached15 := congrArg LocalState.layout cell15
      clocks := by change frame.extra.dataRace = none; rw [b.extra]; exact s.frameRace, metadata := ?_, notConstructed := ?_, thread := thread, active := threadFacts.1, top := threadFacts.2
      unchecked := b.runtime.unchecked, noGc := b.runtime.noGc, fixed := b.runtime.fixed
      size := cachedSize.trans b.size, body := b.body.trans s.body, identity := b.identity.trans s.identity, callee := b.callee.trans s.callee
      track := b.track.trans s.trackNone, relevant := ?_, immediate := immediate, temp16 := .uninit
      live16 := ?_, count := s.count, countPositive := s.countPositive, within := s.within, slot2 := ?_, slot13 := ?_, unused := ?_
      capacity := b.capacity.trans s.capacity, runtimeContext := s.runtimeContext, fresh := s.fresh3, data := data, clean := dataClean }
    · change s.offset.toNat+s.len.toNat ≤ s.entry.allocation.byteSize.bytes.toNat
      rw [←s.capacity]
      exact s.first.bounds
    · rw [b.runtime.addresses]
      exact s.cached
    · change machine.user.payload.payload.user.types.metadata = _
      rw [b.runtime.types]
      exact s.metadata
    · change machine.user.payload.payload.user.types.entries.any _ = _
      rw [b.runtime.types]
      exact s.notConstructed
    · change frame.extra.userRelevance > 0
      rw [b.extra]
      exact s.relevant
    · rw [same 16 (by decide),b.slot16]
      rfl
    · exact (same 2 (by decide)).trans (b.slot2.trans s.slot2)
    · exact (same 13 (by decide)).trans b.facts.slot13
    · intro index lower upper
      have different : index ≠ 15 := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : 15 < 17) lower))
      exact (same index different).trans ((b.facts.high index lower).trans (s.unused index lower upper))
  let physical : GenericAsMutInvocation.Input := by
    refine {
      start := core, statementFuel := s.statementFuel, target := data.parent, targetNode := data.node, targetPresent := data.parentPresent
      targetNotExposed := notExposed, targetTag := s.first.parentTag, targetNotHelper := s.targetDifferent3
      targetTagPresent := data.tagPresent, targetWithin := by rw [parent];exact b.active, subset := ?_, escaping := ?_
      storage := s.storage, maskValid := s.maskValid, maskLength := s.maskLength, initialized := s.initialized
      provenance := s.provenance, storageFits := s.storageFits, mutable := s.mutable, bufferExtras := ?_, bounded := s.bounded
      zero := (same 0 (by decide)).trans b.facts.zero, continuation := b.facts.continuation.trans s.continuation
      varargs := b.facts.varargs.trans s.varargs, context := s.context, validationContext := s.validationContext
      accessEq := s.accessEq, validationWidth := s.validationWidth, validationRuntimeSize := s.validationRuntimeSize
      sameRuntime := s.sameRuntime, width := s.width, runtimeWidth := s.runtimeWidth, runtimeSize := s.runtimeSize, outerAccessEq := s.outerAccessEq
      slotId := s.slotId, separate := s.separate, slot := s.slot, slotPresent := ?_, slotRoot := s.slotRoot, slotChild := s.slotChild
      slotTree := s.slotTree, slotRootNotHelper := s.slotRootDifferent3, slotRootFree := ?_, slotChildHeld := ?_
      slotDistinct := s.slotDistinct, slotChildNotHelper := s.slotChildDifferent3, frameTracked := ?_
      slotSize := s.slotSize, slotStorage := s.slotStorage, slotMask := s.slotMask, slotProvenance := s.slotProvenance, slotMutable := s.slotMutable
      place := s.place, layout := s.layout, slotBase := s.slotBase, slotPointer := s.slotPointer, aligned := s.aligned, fits := s.fits
      cached := ?_, extras := ?_, destination := (congrArg (fun place => place.toRuntimePlace) b.facts.destination).trans s.destination }
    · intro _ _ member
      exact member
    · intro _ _ _ _ localMember foreignMember
      exact False.elim (foreignMember localMember)
    · change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _
      rw [b.runtime.extras]
      exact s.bufferExtras
    · rw [b.memory]
      exact StackPopRelease.lookup_commit_other s.machine.memory s.id s.slotId s.entry s.slot tree s.separate s.slotPresent
    · change (ended_base s).global.protectedTags.contains s.slotRoot = false
      rw [contains_base s s.slotRoot (Ne.symm s.slotRootDifferent2)]
      exact s.slotRootFree
    · change (ended_base s).global.protectedTags.contains s.slotChild = true
      rw [contains_base s s.slotChild s.slotChildDifferent2]
      exact s.slotChildHeld
    · change frame.extra.borrowTracker = _
      rw [b.extra]
      exact s.frameTracked
    · rw [b.runtime.addresses]
      exact s.slotCached
    · change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _
      rw [b.runtime.extras]
      exact s.extras
  have valid1 : (1 : MIR.LocalId) < frame.locals.size := by rw [b.size];decide
  have valid16 : (16 : MIR.LocalId) < frame.locals.size := by rw [b.size];decide
  have source1 : (frame.locals[1]'valid1) = (s.frame.locals[1]'s.v1) :=
    Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans (b.slot1.trans (Array.getElem?_eq_getElem s.v1)))
  have cell15raw : frame.locals[15] = ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans b.slot15)
  have cell16raw : frame.locals[16] = ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid16).symm.trans b.slot16)
  let ready : GenericAsMutDefaultToCall.DataInput := by
    refine {
      base := {
        data := physical, caller := frame, valid15 := valid15, cached := rfl
        live15 := congrArg LocalState.value cell15raw, uncached15 := congrArg LocalState.layout cell15raw
        preciseOff := s.precise, implicitOff := s.implicitWrites, location := b.location, valid1 := valid1
        value1 := ?_, cached1 := ?_, valid16 := valid16, live16 := congrArg LocalState.value cell16raw, uncached16 := congrArg LocalState.layout cell16raw }
      target := rfl
      fresh := s.fresh4, mapFresh := map4, nodeFresh := node4, different := s.different34
      expressionUnheld := ?_, targetDifferent := s.targetDifferent4, rootDifferent := s.slotRootDifferent4, childDifferent := s.slotChildDifferent4 }
    · rw [source1]
      exact s.sourceLive
    · rw [source1]
      exact s.sourceCached
    · change (ended_base s).global.protectedTags.contains (two_base s).global.nextPointerTag = false
      rw [contains_base s (two_base s).global.nextPointerTag (Ne.symm s.different23)]
      exact s.unheld3
  exact ⟨ready,rfl,rfl,rfl,rfl,rfl⟩
/-- The original append-only factory, delegating all common formation to
form_data and adding only the original append allocator fields. -/
def form (s : GenericSharedAcceptedInput.Input) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tree : BorrowTree)
    (b : Boundary s.toBase frame machine tree)
    (metadata : GeneralBorrowFreshSharedReleasedMetadata.Output s.entry.allocation.extra tree s.target s.first.parentNode s.first.parentTag)
    (map3 : GeneralBorrowTagMap.Fresh tree.tagMapping (two s).global.nextPointerTag)
    (node3 : GeneralBorrowProtector.Fresh tree (two s).global.nextPointerTag)
    (clean3 : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (s.entry.allocation.extra.tagMapping.mapping.size+2)⟩)
    (map4 : GeneralBorrowTagMap.Fresh tree.tagMapping (three s).global.nextPointerTag)
    (node4 : GeneralBorrowProtector.Fresh tree (three s).global.nextPointerTag)
    (clean4 : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (s.entry.allocation.extra.tagMapping.mapping.size+3)⟩) :
    Σ' ready : GenericAsMutDefaultToCall.Input,
      ready.base.caller = frame ∧ ready.base.data.start.machine = machine ∧
      PreparedContracts.actualConfig ready.base.data.start.options () (ready.base.data.start.remaining+1) ready.base.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.base.data.start.limits = s.limits := by
  let slot := GeneralBorrowFreshSharedReleasedMetadata.next_slot metadata s.roomFour
  let node := Classical.choose metadata.node
  have nodeFacts := Classical.choose_spec metadata.node
  let data : GenericAsMutPtrEntryValidity.Data tree (ended_base s.toBase).global.protectedTags
      s.first.parentTag (ended_base s.toBase).global.nextPointerTag s.offset s.len := {
    parent := s.target, root := s.first.root, node := node
    depth := metadata.certificates.depth, children := metadata.certificates.children, parentPresent := nodeFacts.1
    roots := metadata.roots.trans s.first.roots, covered := metadata.certificates.covered
    tagPresent := metadata.tagPresent, tagFresh := map3, protectorFresh := node3, nodeFits := metadata.nodeFits
    slot := slot, well := b.well, owned := b.owned }
  have dataClean : GeneralBorrowFreshFutureClean.Clean tree (GeneralBorrowFreshMutableStages.slot_index data.slot) := by
    change GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    rw [metadata.mappingSize]
    exact clean3
  obtain ⟨common,callerEq,machineEq,configEq,limitsEq,treeEq⟩ := form_data s.toBase frame machine tree b data rfl
    (nodeFacts.2.2.trans s.targetNotExposed) dataClean map4 node4
  let ready : GenericAsMutDefaultToCall.Input := {
    base := common.base, target := common.target
    noFree := by rw [treeEq];exact metadata.noFree
    room := by rw [treeEq];exact GeneralBorrowFreshSharedReleasedMetadata.room metadata s.roomFour
    fresh := common.fresh, mapFresh := common.mapFresh, nodeFresh := common.nodeFresh, different := common.different
    futureClean := by rw [treeEq];rw [metadata.mappingSize,Nat.add_assoc];exact clean4
    expressionUnheld := common.expressionUnheld, targetDifferent := common.targetDifferent
    rootDifferent := common.rootDifferent, childDifferent := common.childDifferent }
  exact ⟨ready,callerEq,machineEq,configEq,limitsEq⟩

private theorem fresh_different (tree : BorrowTree) (newTag oldTag : BorTag) (parent : UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (present : tree.indexOfTag oldTag = some parent) :
    newTag ≠ oldTag := by
  intro same
  have absent := GeneralBorrowTagMap.fresh_find tree.tagMapping newTag fresh
  change tree.tagMapping.get oldTag = some parent at present
  rw [←same] at present
  simp only [UniKeyMap.get,absent,Option.map_none] at present
  cases present

/-- Form the exact arbitrary-pool mutable suffix input from released pure
metadata derived by the runtime. No append index formula is used. -/
def pool_form (s : GenericSharedAcceptedInput.PoolInput) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tree : BorrowTree)
    (b : Boundary s.toBase frame machine tree)
    (metadata : GeneralBorrowFreshSharedPoolReleasedMetadata.Output s.entry.allocation.extra tree
      s.tracker.global.nextPointerTag (one_base s.toBase).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.index s.first) (GeneralBorrowFreshSharedSequence.index (second_pool s))) :
    Σ' ready : GenericAsMutDefaultPoolToCall.Input,
      ready.common.base.caller = frame ∧ ready.common.base.data.start.machine = machine ∧
      PreparedContracts.actualConfig ready.common.base.data.start.options () (ready.common.base.data.start.remaining+1) ready.common.base.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.common.base.data.start.limits = s.limits := by
  let old := metadata.oldNode s.target s.first.parentNode s.first.parentPresent
  let node := Classical.choose old
  have nodeFacts := Classical.choose_spec old
  have differentFirst := fresh_different s.entry.allocation.extra s.tracker.global.nextPointerTag s.first.parentTag s.target
    s.first.tagFresh s.first.parentTagPresent
  have differentSecond := fresh_different s.entry.allocation.extra (one_base s.toBase).global.nextPointerTag s.first.parentTag s.target
    s.tagFresh s.first.parentTagPresent
  have tags := GenericFunctionEntryNumerics.four_tags_distinct s.tracker s.fresh s.fresh2 s.fresh3
  let slot := GeneralBorrowFreshSharedPoolReleasedMetadata.next_slot metadata s.target s.first.parentNode s.first.parentPresent
    (by have room := s.nodeRoom;omega)
  let data : GenericAsMutPtrEntryValidity.Data tree (ended_base s.toBase).global.protectedTags
      s.first.parentTag (ended_base s.toBase).global.nextPointerTag s.offset s.len := {
    parent := s.target, root := s.first.root, node := node
    depth := GeneralBorrowTightAncestry.tight tree.nodes metadata.certificates.depth
    children := metadata.certificates.children, parentPresent := nodeFacts.1
    roots := metadata.roots.trans s.first.roots, covered := metadata.certificates.covered
    tagPresent := (metadata.oldLookup s.first.parentTag differentFirst differentSecond).trans s.first.parentTagPresent
    tagFresh := metadata.freshTag _ s.mapFresh3 tags.2.1 s.different23
    protectorFresh := metadata.freshProtector _ s.nodeFresh3 tags.2.1 s.different23
    nodeFits := metadata.nodeFits, slot := slot, well := b.well, owned := b.owned }
  have dataClean : GeneralBorrowFreshFutureClean.Clean tree (GeneralBorrowFreshMutableStages.slot_index data.slot) :=
    GeneralBorrowFreshSharedPoolReleasedMetadata.clean_all metadata s.cleanVacant _
      (GeneralBorrowFreshMutableStages.slot_vacant tree data.depth data.parent data.slot)
  have map4 : GeneralBorrowTagMap.Fresh tree.tagMapping (three_base s.toBase).global.nextPointerTag :=
    metadata.freshTag _ s.mapFresh4 tags.2.2.1 s.different24
  have node4 : GeneralBorrowProtector.Fresh tree (three_base s.toBase).global.nextPointerTag :=
    metadata.freshProtector _ s.nodeFresh4 tags.2.2.1 s.different24
  obtain ⟨common,callerEq,machineEq,configEq,limitsEq,treeEq⟩ := form_data s.toBase frame machine tree b data rfl
    (nodeFacts.2.2.trans s.targetNotExposed) dataClean map4 node4
  let ready : GenericAsMutDefaultPoolToCall.Input := {
    common := common
    pool := by rw [treeEq];exact metadata.pool
    accounting := by rw [treeEq];exact metadata.accounting
    room := by rw [treeEq];have size := metadata.size;have room := s.nodeRoom;omega
    cleanVacant := by
      intro query vacant
      rw [treeEq] at vacant ⊢
      exact GeneralBorrowFreshSharedPoolReleasedMetadata.clean_all metadata s.cleanVacant query vacant }
  exact ⟨ready,callerEq,machineEq,configEq,limitsEq⟩
end
end DuplicatePrefix.GenericSharedAcceptedForm
