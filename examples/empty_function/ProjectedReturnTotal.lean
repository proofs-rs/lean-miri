import empty_function.ProjectedOldValue
import empty_function.ProjectedWriteContext
import empty_function.ProjectedImmediateCopy
import empty_function.ProjectedAllocationTotal
import empty_function.ProjectedForceTotal
import empty_function.ProjectedUninitCopy
import empty_function.ProjectedReady
namespace EmptyFunction.ProjectedReturnTotal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false

theorem copy (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacityEq : s.capacity = remaining+2) (validation : 0 < s.options.limits.validation)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (offset : Size)
    (projected : destination.offset = some offset) (value : Immediate Provenance)
    (old : destination.oldOperand = .immediate value)
    (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size)
    (callee previous : LocalUnit.F) (index : Nat) :
    let before := LocalUnit.current older (ProjectedModel.caller s p input.tracker destination bound)
      (ProjectedReady.popped s p input.tracker destination older bound callee previous index)
    let operation := (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (.frameLocal older.size destination.localId (some offset) s.abi.ret.layout destination.caller.localsIdentity)
    (∃ error failed, operation before = (failed,.error error) ∧ RunLoop.reportsUB error = false) ∨
    (∃ caller machine, operation before = (LocalUnit.current older caller machine,.ok ())) := by
  have capacity : 0 < s.capacity := by omega
  dsimp only
  let frame := ProjectedModel.caller s p input.tracker destination bound
  let machine := ProjectedReady.popped s p input.tracker destination older bound callee previous index
  let before := LocalUnit.current older frame machine
  have needed := ProjectedForce.needed s p input.tracker destination offset projected value old
  have prior := ProjectedReady.resources s metadata capacity p runtime input destination older bound callee previous index
  rcases prior with ⟨memory,addressBefore,tracked,noRace,backend,extras,choices,noGhost,shallow⟩
  rcases ProjectedAllocationTotal.allocate s metadata capacity p input destination needed before memory addressBefore tracked backend noRace extras with failed | succeeded
  · obtain ⟨error,failed,allocationError,safe⟩ := failed
    have atSlot := LocalImmediate.cached_at destination.caller destination.localId destination.slot destination.baseLayout bound
    have live : ({destination.slot with layout := some destination.baseLayout}).value = .live (.immediate value) := by
      change destination.slot.value = _; rw [destination.live,old]
    have dictionaries := MetadataBinding.fields s metadata capacity
    have forced := ProjectedForceTotal.allocation_error s.cfg.access s.cfg.allocation s.cfg.compiler () older frame machine
      destination.localId {destination.slot with layout := some destination.baseLayout} destination.baseLayout s.abi.ret.layout value
      atSlot live rfl destination.baseSized (dictionaries.debug.trans profile.debug) error failed allocationError (some offset) frame.localsIdentity
    have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
      (Configuration.leaves s.prepared s.options.place.debugAssertions) (remaining+1) metadata.construction s.cfg
      (by simpa only [Configuration.rootConfig,capacityEq,Nat.add_assoc] using s.built)
    rw [←fields.projection] at forced
    exact Or.inl ⟨error,failed,ProjectedForceTotal.copy_error_from_force s metadata profile remaining capacityEq
      before failed older.size destination.localId offset frame.localsIdentity error forced,safe⟩
  obtain ⟨allocated⟩ := succeeded
  let reserved := allocated.reserved
  let id := allocated.id
  let global := allocated.global
  let tag := allocated.tag
  let bytes := allocated.bytes
  let base := allocated.base
  let tape := allocated.tape
  let addresses := allocated.addresses
  have created := allocated.storage
  have sizeEq := allocated.size
  have mutable := allocated.mutable
  have allocatedEq := allocated.allocated
  rw [allocated.afterEq] at allocatedEq
  have cached := allocated.cached
  have baseFits := allocated.extent
  have missing := allocated.fresh
  let registered := ProjectedCreate.registered s before reserved input.tracker global id bytes tag destination.baseLayout.layout.size
  let post := ProjectedAddress.assigned (ChoiceProjection.tapeAccess.put registered tape) addresses
  let parent : MPlaceTy Provenance := ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,destination.baseLayout⟩
  have ctx := ProjectedWriteContext.registered s before reserved input.tracker global id bytes tag destination.baseLayout.layout.size
    tape addresses backend noRace noGhost shallow
  obtain ⟨allocation,sizeUpdated,writeCases⟩ : ∃ allocation : Allocation Provenance BorrowTree,
      allocation.byteSize = destination.baseLayout.layout.size ∧
      ((value = .uninit ∧ allocation = bytes.withExtra (BorrowTree.new tag destination.baseLayout.layout.size)) ∨
       (value ≠ .uninit ∧ (ValidityMachine.placeHooks s.cfg.access s.cfg.allocation s.cfg.compiler).writeMemoryNoValidate () value parent post =
         .ok () {post with machine := {post.machine with memory := {post.machine.memory with live := reserved.live.push (id,⟨.stack,allocation⟩)}}})) := by
    by_cases initialized : value = .uninit
    · exact ⟨bytes.withExtra (BorrowTree.new tag destination.baseLayout.layout.size),sizeEq,Or.inl ⟨initialized,rfl⟩⟩
    · obtain ⟨allocation,written,sizeUpdated,rest⟩ :=
        ProjectedOldValue.write s metadata capacity post id tag base destination.baseLayout bytes value initialized reserved.live
          (destination.oldEncoding value old) created sizeEq mutable destination.baseSized destination.baseSigned ctx.2.2.2.2.1 missing
          cached ctx.1 ctx.2.1 ctx.2.2.2.2.2.1 ctx.2.2.1 ctx.2.2.2.1
      exact ⟨allocation,sizeUpdated,Or.inr ⟨initialized,written⟩⟩
  let writtenMachine : MachineHooks.MachineState MiriMemoryKind RootUser := {post.machine with memory := {post.machine.memory with live := reserved.live.push (id,⟨.stack,allocation⟩)}}
  have allocationEq : PlaceMachine.allocateStack s.cfg.allocation destination.baseLayout before =
      .ok parent (LocalUnit.current older frame post.machine) := allocatedEq
  have sameCaller : destination.caller = input.caller := Option.some.inj (destination.current.symm.trans input.current)
  have noClocks : frame.extra.dataRace = none := by
    change destination.caller.extra.dataRace = none
    rw [sameCaller]
    exact input.callerNoClocks
  have normalized : CompilerFrameContext.normalizedLocalType s.prepared.compiler frame destination.localId = .ok destination.metadata.normalizedTy := by
    rw [CompilerFrameContext.normalizedLocalType_congr s.prepared.compiler frame destination.caller
      destination.localId rfl rfl rfl rfl]
    exact destination.metadata.normalization
  have liveId : writtenMachine.memory.live.any (fun row => row.1 == id) = true := by
    change (reserved.live.push _).any (fun row => row.1 == id) = true
    simp [Array.any_push]
  obtain ⟨span,moved⟩ := ProjectedForce.after_move s metadata capacity older frame writtenMachine destination.localId
    destination.metadata.normalizedTy normalized parent id tag rfl liveId noClocks
  let movedMachine : MachineHooks.MachineState MiriMemoryKind RootUser := {writtenMachine with allocationSpans := (writtenMachine.allocationSpans.filter (fun row => row.1 != id)).push (id,span,none)}
  have footprint : InputDraft.IndirectFootprint (LocalUnit.current older frame movedMachine) parent.mplace.ptr destination.baseLayout.layout.size := by
    refine {id := id,entry := ⟨.stack,allocation⟩,live := ?_,base := base,relative := 0,cached := cached,address := ?_,addressFits := ?_,extent := ?_,attribution := rfl}
    · change (reserved.live.push _).find? _ = _
      have absent : reserved.live.find? (fun row => row.1 == id) = none := allocated.fresh
      simp [Array.find?_push,absent]
    · simp [parent,Pointer.new,Size.ofBytes]
    · rw [sizeUpdated]
      exact baseFits
    · change 0 + destination.baseLayout.layout.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat
      rw [sizeUpdated]
      omega
  let slot := {destination.slot with layout := some destination.baseLayout}
  have boundCurrent : destination.localId < frame.locals.size := by simpa [frame,ProjectedModel.caller,LocalImmediate.cached] using bound
  have atSlot : frame.locals[destination.localId]? = some slot :=
    LocalImmediate.cached_at destination.caller destination.localId destination.slot destination.baseLayout bound
  have live : slot.value = .live (.immediate value) := by change destination.slot.value = _;rw [destination.live,old]
  have within : offset.bytes.toNat ≤ destination.baseLayout.layout.size.bytes.toNat := by cases destination;cases projected;assumption
  have ghostMoved : movedMachine.user.payload.ghost = false := noGhost
  have shallowMoved : movedMachine.user.payload.validation = .Shallow := shallow
  let updated : LocalUnit.F := {frame with locals := frame.locals.set destination.localId {slot with value := .live (.indirect parent.mplace)} boundCurrent}
  have copied : (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (.frameLocal older.size destination.localId (some offset) s.abi.ret.layout frame.localsIdentity) before =
      (LocalUnit.current older updated movedMachine,.ok ()) := by
    rcases writeCases with ⟨uninit,allocationUninit⟩ | ⟨initialized,written⟩
    · have machineEq : writtenMachine = post.machine := by
        change {post.machine with memory := {post.machine.memory with live := reserved.live.push (id,⟨.stack,allocation⟩)}} = _
        rw [allocationUninit,←ctx.2.2.2.2.1]
      have createdEq := allocationEq
      rw [←machineEq] at createdEq
      exact ProjectedUninitCopy.from_allocation s metadata profile remaining capacityEq validation older frame machine writtenMachine movedMachine
        destination.localId slot destination.baseLayout boundCurrent atSlot (uninit ▸ live) rfl destination.baseSized
        id tag base offset createdEq moved footprint within destination.baseSigned noClocks ghostMoved shallowMoved
    · have writtenEq : (ValidityMachine.placeHooks s.cfg.access s.cfg.allocation s.cfg.compiler).writeMemoryNoValidate () value parent
          (LocalUnit.current older frame post.machine) = .ok () (LocalUnit.current older frame writtenMachine) := written
      exact ProjectedImmediateCopy.from_write s metadata profile remaining capacityEq validation older frame machine post.machine
        writtenMachine movedMachine destination.localId slot destination.baseLayout value initialized boundCurrent atSlot live rfl
        destination.baseSized id tag base offset allocationEq writtenEq moved footprint within destination.baseSigned noClocks ghostMoved shallowMoved
  exact Or.inr ⟨_,_,copied⟩
end EmptyFunction.ProjectedReturnTotal
