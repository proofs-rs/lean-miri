import duplicate_prefix.CurrentCallOrdinaryConversionEnsure
import duplicate_prefix.CurrentCallConversionSourceCopy
import duplicate_prefix.CurrentCallConversionSourceCheckpoint
import duplicate_prefix.CurrentCallConversionSourceLeaf
import duplicate_prefix.CurrentCallPreparedResources
import duplicate_prefix.CurrentCallSpatialEntryControl

/-! The positive CURRENT source argument executes its original registered
conversion and typed copy. The actual converter state is retained for the Bool
phase, including its remaining selected protocol. -/
namespace DuplicatePrefix.CurrentCallOrdinaryCurrentSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private theorem fresh {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    input.tracker.global.nextPointerTag.value < 18446744073709551615 := by
  have room := input.resources.tagRoom
  simpa [UInt64.lt_iff_toNat_lt] using (show input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615 by omega)
private theorem cached_below {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (id : AllocId) (root : BorTag) (cached : input.tracker.global.rootTag? id = some root) :
    root.value.toNat < input.tracker.global.nextPointerTag.value.toNat := by
  cases found : input.tracker.global.rootPointerTags.find? (fun row => row.1 == id) with
  | none => simp only [GlobalState.rootTag?, found, Option.map_none] at cached; cases cached
  | some row =>
    have same : row.2 = root := Option.some.inj (by simpa only [GlobalState.rootTag?, found, Option.map_some] using cached)
    have below := input.resources.cachedRootsBelow row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
    rw [same] at below
    exact below
private theorem successor_nat (tag : BorTag) (room : tag.value < 18446744073709551615) :
    (TypedRetagEmpty.successorTag tag room).value.toNat = tag.value.toNat + 1 := by
  have bound : tag.value.toNat < 18446744073709551615 := by simpa [UInt64.lt_iff_toNat_lt] using room
  change (tag.value + 1).toNat = _
  rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]

private theorem storage_room {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (id : AllocId) (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before id source)
    (storage : source.len = source.byteSize.bytes.toNat) : source.len + 64 < 2^64 := by
  cases current with
  | memory descriptor =>
    rw [storage]
    exact input.resources.globalRoom _ (CurrentCallConversionTargetAdequacy.global_member descriptor)
  | internalStatic definition descriptor initializer =>
    exact input.resources.initializerRoom (definition, source)
      (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some initializer))

def rawPost (options : EvalConfigurationCore.Options) (after : Before) (id : AllocId)
    (root tag : BorTag) (converted : Allocation Provenance Unit) (held : ProtectedTags) (offset len : UInt64) : Before :=
  let raw := CurrentCallConversionSourceCopy.childMachine options after id root tag converted held offset len
  {raw with user := {raw.user with payload := {raw.user.payload with ghost := false}}}

theorem copy {options limits remaining span before place len argument}
    (id : AllocId) (rootTag : BorTag) (base offset : UInt64)
    (input : OrdinaryInput options limits remaining span before argument len place)
    (encoding : argument = .pointer (Pointer.new (.concrete id rootTag) (Size.ofBytes (base + offset))))
    (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : before.memory.hasFunctionPointer id = false) (noVaList : before.memory.hasVaListId id = false)
    (registry : InitialRegistryVacant before id)
    (cachedRoot : input.tracker.global.rootTag? id = some rootTag)
    (cachedBase : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (nonnull : base + offset ≠ 0) (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ source.byteSize.bytes.toNat)
    (physicalSource : Physical source offset len true)
    (baseRoom : base.toNat + source.byteSize.bytes.toNat < 2^64) :
    let root := CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let frame := (firstLive root).frame
    let machine := CurrentCallPush.preparedMachine before #[]
    let ptr := Pointer.new (.concrete id rootTag) (Size.ofBytes (base + offset))
    let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span frame 1 (by simpa only [i1] using (firstLive root).valid i1) ptr len
    let active := CurrentCallReferenceEntry.view machine input.tracker .FnEntry true
    let phase := registeredState #[] copied {} (allocatedMachine active ⟨input.tracker.global, .FnEntry⟩ (fresh input))
      (allocatedTracker ⟨input.tracker.global, .FnEntry⟩ (fresh input)) id input.tracker.global.nextPointerTag
    ∃ rest : List (Allocation CtfeProvenance Unit), ∃ externStatic finalAddresses finalTape,
    ∃ result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic phase.machine
      (registeredTracker (allocatedTracker ⟨input.tracker.global, .FnEntry⟩ (fresh input)) input.tracker.global.nextPointerTag)
      (rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) 15 finalAddresses finalTape,
    ∃ doneFrame,
      (CurrentCallConversionActualEnsure.hooks options).rootPointer =
        PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic ∧
      CurrentCallConversionPlan.selectedPayloads before argument len place = source :: rest ∧
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span ptr len).imm, reference⟩
        (LocalPlaces.localRuntimePlace 0 frame 1 reference).stackView
        (Storage.withCurrent #[] frame (ScopedFrame.entered machine input.tracker .FnEntry)) =
        .ok () (Storage.withCurrent #[] doneFrame
          (rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len)) ∧
      MachineHooks.withRetagMode .FnEntry
        ((ExecutionMachine.callHooks (config options (remaining + 1) span) limits).copyAllowTransmute ()
          ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span ptr len).imm, reference⟩
          (LocalPlaces.localRuntimePlace 0 frame 1 reference).stackView)
        (Storage.withCurrent #[] frame machine) = .ok () (Storage.withCurrent #[] doneFrame
          {rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len with
            borrowTracker := some ⟨result.global, input.tracker.retagMode⟩}) ∧
      doneFrame.extra.borrowTracker = some (({} : FrameState).addProtector id input.tracker.global.nextPointerTag) ∧
      doneFrame.locals.size = frame.locals.size ∧
      doneFrame = CurrentCallTypedSourceCopy.writtenFrame options remaining span copied {} 1
        (by simpa only [copied, CurrentCallTypedSourceCopy.copiedFrame, Array.size_set, frame, i1] using (firstLive root).valid i1)
        ptr len id input.tracker.global.nextPointerTag ∧
      ∃ stage : CurrentCallLazySourceResources.Stage input.tracker.global {} id rootTag source.byteSize.bytes offset len (fresh input),
      ∃ currentSource : CurrentCallPostEntryCheckpoint.Source
          {rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len with
            borrowTracker := some ⟨result.global, input.tracker.retagMode⟩}
          ⟨result.global, input.tracker.retagMode⟩ offset.toNat len,
        CurrentCallPostEntryCheckpoint.CopyReady currentSource ∧ currentSource.role.backing.id = id ∧
        currentSource.role.family.value = Pointer.new (.concrete id input.tracker.global.nextPointerTag) (Size.ofBytes (base + offset)) ∧
        currentSource.role.backing.allocation = result.converted.mapExtra (fun _ => stage.output.child.tree) ∧
        currentSource.grant = stage.child ∧ currentSource.tag = input.tracker.global.nextPointerTag ∧
        currentSource.node.children = #[] ∧ currentSource.role.backing.allocation.extra.nodes.size + 7 < 65536 ∧
        DuplicatePrefixCallModel.Model options remaining span ({rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len with
            borrowTracker := some ⟨result.global, input.tracker.retagMode⟩}) ∧
        DuplicatePrefixTypeCacheOrigins.Origins (rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len).user.payload.payload.user.types ∧
        (rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len).threads =
          (CurrentCallPush.preparedMachine before #[]).threads ∧
        (rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len).memory =
          {before.memory with live := ((before.memory.live.filter (fun row => row.1 != id)).push
            (id, ⟨.machine .global, result.converted.mapExtra (fun _ => stage.output.child.tree)⟩))} ∧
        (rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len).borrowTracker =
          some ⟨result.global, .FnEntry⟩ ∧
        (rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len).user.payload.validation = .Shallow := by
  dsimp only
  let root := CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let frame := (firstLive root).frame
  let machine := CurrentCallPush.preparedMachine before #[]
  let ptr := Pointer.new (Provenance.concrete id rootTag) (Size.ofBytes (base + offset))
  let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span frame 1 (by simpa only [i1] using (firstLive root).valid i1) ptr len
  let active := CurrentCallReferenceEntry.view machine input.tracker .FnEntry true
  let phase := registeredState #[] copied {} (allocatedMachine active ⟨input.tracker.global, .FnEntry⟩ (fresh input))
    (allocatedTracker ⟨input.tracker.global, .FnEntry⟩ (fresh input)) id input.tracker.global.nextPointerTag
  let tracker := registeredTracker (allocatedTracker ⟨input.tracker.global, .FnEntry⟩ (fresh input)) input.tracker.global.nextPointerTag
  have payload := CurrentCallConversionPlanAdequacy.payload_of_current before id source absent noFunction noVaList current
  have query : CurrentCallConversionPlan.sourceQuery before argument len = .ok (some id) := by
    rw [encoding]
    exact CurrentCallConversionPlanAdequacy.query_concrete before ptr len id rootTag base rfl cachedBase
  obtain ⟨rest, head, _⟩ := CurrentCallOrdinaryConversionSelected.source_first before argument len place id source query payload
  have currentPhase : CurrentPayload phase.machine id source := by
    cases current with
    | memory descriptor => exact .memory descriptor
    | internalStatic definition descriptor initializer => exact .internalStatic definition descriptor initializer
  obtain ⟨externStatic, wiring, finalAddresses, finalTape, result, _⟩ := CurrentCallOrdinaryConversionEnsure.first input phase tracker
    (by intro query; rfl) rfl rfl rfl (by intro query; rfl) 1 15 (by decide) (by decide)
    (by change (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag (fresh input)).value.toNat ≤ _; rw [successor_nat]; exact Nat.le_refl _)
    rfl (fun target member => CurrentCallOrdinaryConversionSelected.targets_metadata input target member)
    id rootTag source rest head currentPhase absent cachedRoot registry input.model.noDataRace
  obtain ⟨ctx, actualPointers⟩ := GlobalEmptyReferenceContext.exists_context options remaining span input.model.preciseOff input.model.implicitOff
  have frameBorrow : frame.extra.borrowTracker = some ({} : FrameState) := by
    change root.frame.extra.borrowTracker = some ({} : FrameState)
    exact RootEntryFrame.raw_borrow _ _ _ input.tracker input.runtime.enabled
  have live : (frame.locals[1]'(by simpa only [i1] using (firstLive root).valid i1)).value = .live (.immediate .uninit) := by
    simp only [frame, firstLive, RootFrameData.live, RootFrameData.write, Array.getElem_set_self, i1]
  have cached : (frame.locals[1]'(by simpa only [i1] using (firstLive root).valid i1)).layout = some reference := by
    simp only [frame, firstLive, RootFrameData.live, RootFrameData.write, Array.getElem_set_self, firstCache,
      RootFrameData.cache, LocalOperands.cachedLayoutFrame, atSpan, i1]
  have currentMachine : CurrentPayload machine id source := by
    cases current with
    | memory descriptor => exact .memory descriptor
    | internalStatic definition descriptor initializer => exact .internalStatic definition descriptor initializer
  have dynamicPositive : 0 < options.place.dynamicFuel := by
    have room := input.resources.dynamicFuel; unfold DuplicatePrefixCallSpecification.work at room; omega
  have validationPositive : 0 < options.limits.validation := by
    have room := input.resources.configuredFuel.2.2.2; unfold DuplicatePrefixCallSpecification.work at room; omega
  have completed : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer phase.machine = .ok result.converted result.machine := by
    rw [wiring]
    exact result.completed
  have enabled : result.machine.borrowTracker = some {tracker with global := result.global} := by
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
  have output := CurrentCallConversionSourceCopy.invoke options limits remaining span ctx actualPointers machine input.tracker
    input.runtime.enabled #[] frame {} frameBorrow id rootTag source base offset len currentMachine absent noFunction noVaList cachedBase
    positive signedFits bounds nonnull (cached_below input id rootTag cachedRoot) input.protectorsBelow (fresh input)
    input.model.nullComparator (options.place.dynamicFuel - 1) (options.limits.validation - 1) (by omega) (by omega)
    input.model.metadata input.cacheOrigins input.model.debugOff input.model.ghostOff input.model.shallow
    1 (by simpa only [i1] using (firstLive root).valid i1) .uninit live cached (firstLive root).noClocks result.converted result.attributes
    result.machine {tracker with global := result.global} completed enabled (result.roots id rootTag cachedRoot)
    (by rw [result.frame, CurrentCallConversionFiniteFold.state_eq]; exact input.model.noDataRace)
    (by rw [result.frame, CurrentCallConversionFiniteFold.state_eq]; exact registry)
    (by rw [result.frame, CurrentCallConversionFiniteFold.state_eq]; rfl) result.flags
  let post : Before := {rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len with
    borrowTracker := some ⟨result.global, input.tracker.retagMode⟩}
  let next : MachineHooks.BorrowState := ⟨result.global, input.tracker.retagMode⟩
  obtain ⟨stage⟩ := CurrentCallLazySourceResources.construct input.tracker.global {} id rootTag source.byteSize.bytes offset len (fresh input)
    positive bounds (cached_below input id rootTag cachedRoot) input.protectorsBelow
  have flags : next.global.protectedTags = stage.output.global.protectedTags := by rw [stage.globalEq]; exact result.flags
  have counter : stage.output.global.nextPointerTag.value.toNat ≤ next.global.nextPointerTag.value.toNat := by
    rw [stage.globalEq]; exact result.counter
  have tree : stage.output.child.tree = PositiveGlobalTypedReborrow.finalTree rootTag input.tracker.global.nextPointerTag
      result.converted.byteSize result.global.protectedTags offset len := by
    rw [stage.treeEq, result.attributes.size, flags]
    rfl
  have sourceLive : post.memory.live.find? (fun row => row.1 == id) =
      some (id, ⟨.machine .global, result.converted.mapExtra (fun _ => stage.output.child.tree)⟩) := by
    rw [tree]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have sourceCached : post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩ := by
    change result.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact result.bases id ⟨id, base⟩ cachedBase
  have extras : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id, ⟨none, #[]⟩) := by
    change (((result.machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != id)).push
      (id, ⟨none, #[]⟩)).find? (fun row => row.1 == id)) = _
    have noMatch : (fun row : AllocId × MemoryExtras.AllocationExtra Unit =>
        decide ((row.1 != id) = true ∧ (row.1 == id) = true)) = (fun _ => false) := by
      funext row
      by_cases equal : row.1 = id <;> simp [equal]
    have emptyFind : result.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun _ => false) = none := by
      simp [Array.find?_eq_none]
    simp [Array.find?_push, Array.find?_filter, noMatch, emptyFind]
  let data : CandidateCurrentJointCall.Identities := ⟨⟨#[], #[], #[], fun _ _ => none⟩, #[], #[]⟩
  obtain ⟨S, ready, sourceId, sourcePointer, sourceAllocation, sourceGrant, sourceTag⟩ :=
    CurrentCallConversionSourceCheckpoint.at_post input.tracker.global {} id rootTag source result.converted result.attributes offset len physicalSource
      result.wellFormed (storage_room input id source current physicalSource.1.1) cachedRoot (fresh input) stage positive signedFits base baseRoom nonnull
      post next (result.roots id rootTag cachedRoot) flags counter sourceLive sourceCached extras data
  have nodeEq : S.node = stage.node := by
    have present := S.nodeAt
    rw [sourceAllocation, sourceGrant] at present
    exact Option.some.inj (present.symm.trans stage.nodeAt)
  have leaf : S.node.children = #[] := by
    rw [nodeEq]
    exact CurrentCallConversionSourceLeaf.stage_leaf input.tracker.global {} id rootTag source.byteSize.bytes offset len (fresh input)
      stage positive bounds (cached_below input id rootTag cachedRoot) input.protectorsBelow
  have nodes : S.role.backing.allocation.extra.nodes.size + 7 < 65536 := by
    rw [sourceAllocation]
    have growth := stage.growth
    change stage.output.child.tree.nodes.size + 7 < 65536
    omega
  have defaultMode : input.tracker.retagMode = .Default := by
    obtain ⟨old, tracked, mode⟩ := input.model.defaultTracker
    have equal : input.tracker = old := Option.some.inj (input.runtime.enabled.symm.trans tracked)
    exact equal ▸ mode
  have controlEq : (config options (remaining + 1) span).terminators.getControl post.user =
      (config options (remaining + 1) span).terminators.getControl before.user := by
    dsimp only [post]
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    rw [(CanonicalConfigFacts.actual_fields options () (remaining + 1) span).terminators]
    rfl
  have sourceModel : DuplicatePrefixCallModel.Model options remaining span post := by
    refine ⟨input.model.debugOff, input.model.preciseOff, input.model.implicitOff, rfl, ?_,
      ⟨next, rfl, defaultMode⟩, ?_, ?_, ?_, ?_, ?_, ?_, input.model.nullComparator, input.model.sourceMatches⟩
    · dsimp only [post]
      rw [result.frame, CurrentCallConversionFiniteFold.state_eq]; exact input.model.shallow
    · dsimp only [post]
      rw [result.frame, CurrentCallConversionFiniteFold.state_eq]; exact input.model.noDataRace
    · dsimp only [post]
      rw [result.frame, CurrentCallConversionFiniteFold.state_eq]; exact input.model.noBackend
    · dsimp only [post]
      rw [result.frame, CurrentCallConversionFiniteFold.state_eq]; exact input.model.metadata
    · dsimp only [post]
      rw [result.frame, CurrentCallConversionFiniteFold.state_eq]; exact input.model.fixedScheduler
    · change ((config options (remaining + 1) span).terminators.getControl post.user).checkedArithmetic = false
      rw [controlEq]; exact input.model.unchecked
    · change ((config options (remaining + 1) span).terminators.getControl post.user).gcInterval = 0
      rw [controlEq]; exact input.model.noGc
  have sourceOrigins : DuplicatePrefixTypeCacheOrigins.Origins post.user.payload.payload.user.types := by
    dsimp only [post]
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact input.cacheOrigins
  have threads : post.threads = machine.threads := by
    dsimp only [post]
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    rfl
  have heap : post.memory = {before.memory with live := ((before.memory.live.filter (fun row => row.1 != id)).push
      (id, ⟨.machine .global, result.converted.mapExtra (fun _ => stage.output.child.tree)⟩))} := by
    rw [tree]
    simp only [post, rawPost, CurrentCallConversionSourceCopy.childMachine, CurrentCallConversionSourceCopy.rootMachine,
      RetagEntry.updatedMemory, CurrentCallConversionMaterialize.installed, MemoryExtras.putAllocation,
      Array.filter_push, beq_self_eq_true, bne_self_eq_false, Bool.false_eq_true, ite_false, Array.filter_filter, Bool.and_self]
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    rfl
  have rawTracked : (rawPost options result.machine id rootTag input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len).borrowTracker =
      some ⟨result.global, .FnEntry⟩ := by
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    rfl
  exact ⟨rest, externStatic, finalAddresses, finalTape, result, _, wiring, head, output.1, output.2.1, output.2.2.1, output.2.2.2, rfl,
    stage, S, ready, sourceId, sourcePointer, sourceAllocation, sourceGrant, sourceTag, leaf, nodes, sourceModel, sourceOrigins, threads, heap,
    rawTracked, sourceModel.shallow⟩

end
end DuplicatePrefix.CurrentCallOrdinaryCurrentSource
