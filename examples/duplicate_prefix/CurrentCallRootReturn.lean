import duplicate_prefix.CurrentCallBoolScalarWrite
import duplicate_prefix.S04FinalReturnRuleCopy
import duplicate_prefix.CandidateCurrentWindowPointerChecks
import duplicate_prefix.ActualPopPlan
/-! Physical original-Bool return and the actual root terminal step. Logical
release and Write certificates are internal leaves supplied by the endpoint;
current WindowBinding supplies concrete/wildcard interior geometry. -/
namespace DuplicatePrefix.CurrentCallRootReturn
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
theorem validated_write {options : EvalConfigurationCore.Options}
    {remaining : Nat} (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : CurrentCallBoolScalarWrite.Window state.machine place)
    (binding : CandidateCallBindings.WindowBinding state.machine input.pointer input.id input.offset.toNat 1)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (race : state.machine.dataRace = none) (backend : state.machine.user.payload.payload.user.backend = .none)
    (ghost : state.machine.user.payload.ghost = false) (shallow : state.machine.user.payload.validation = .Shallow)
    (ready : CurrentCallBoolProtection.WindowReady state.machine input.id input.offset.toNat 1)
    (completed : (input.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (resolvedBefore : (PreparedContracts.actualConfig options () (remaining+1) span).access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine)
    (value : Bool) (fuel : Nat) :
    let outer := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let tree := (input.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree
    ∃ updated, (do
      PlaceMachine.writeMemory outer.access outer.compiler.willValidateMemory (.scalar (Scalar.fromBool value)) place
      ValidityMachine.validateRuntime inner.validity () (fuel+1) ⟨.memory place.mplace,place.layout⟩ true) state =
      .ok () (CanonicalCopy.replaceAllocation state input.id input.entry.kind updated) ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.validationContext
  obtain ⟨stored,write,writeTree,writeSize,writeLen,writeMut,read,pointerBounds⟩ :=
    CurrentCallBoolScalarWrite.configured options remaining span state place input tracker enabled race backend ready completed resolvedBefore value
  let after := CanonicalCopy.replaceAllocation state input.id input.entry.kind stored
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨input.entry.kind,stored⟩
  have present : after.machine.memory.live.find? (fun row => row.1 == input.id) = some (input.id,entry) :=
    CanonicalCopy.replace_lookup state input.id input.entry.kind stored
  have size : stored.byteSize = Size.ofBytes input.capacity := writeSize.trans input.size
  have storage : stored.len = input.capacity.toNat := writeLen.trans input.bytes
  obtain ⟨updated,mutation,clearLen,clearSize,clearMut,clearExtra,clearMask,clearRead⟩ :=
    S04ReturnAllocationClear.clear_exists stored input.capacity input.offset storage size input.bounds pointerBounds
  obtain ⟨original,base,live,cached,physicalLen,addressRoom,physicalBounds,addressEq,nonnull,provenanceBinding⟩ := binding
  have entryEq : original = input.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans input.live))).2
  subst original
  have baseEq : base = input.base := by
    have eq := Option.some.inj (cached.symm.trans input.cachedBase)
    exact congrArg (fun row => row.address) eq
  subst base
  let active := S04ReturnBoolValidation.ghostState after
  let provenance := S04ReturnBorrowBridge.extra input.pointer.provenance
  have cached : active.machine.user.addresses.baseAddr.find? (fun row => row.allocId == input.id) =
      some ⟨input.id,input.base⟩ := input.cachedBase
  have activePresent : active.machine.memory.live.find? (fun row => row.1 == input.id) = some (input.id,entry) := present
  have off : input.pointer.offset = Size.ofBytes (input.base+input.offset) := by
    cases h : input.pointer.offset
    simpa [h,Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
  have pointer : place.mplace.ptr = Pointer.new (some input.pointer.provenance) (Size.ofBytes (input.base+input.offset)) := by
    rw [input.physicalPointer]
    simp only [Pointer.withOptionalProvenance,Pointer.new,off]
  have resolved : context.access.resolvePointer active.machine.memory
      (Pointer.new (some input.pointer.provenance) (Size.ofBytes (input.base+input.offset)))
      (Int.ofNat (1 : UInt64).toNat) active.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,provenance⟩) active.machine := by
    rw [show context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers from rfl]
    cases prov : input.pointer.provenance with
    | concrete id tag =>
      have same : id = input.id := by simpa only [prov] using provenanceBinding
      subst id
      have res := MemoryCopyBridge.typed_resolve_cached context.pointers active.machine.memory active.machine
        input.id tag input.base input.offset (Int.ofNat (1 : UInt64).toNat) contexts.validationWidth
        (by decide) (by decide) cached
      simpa only [prov,provenance,S04ReturnBorrowBridge.extra] using res
    | wildcard =>
      obtain ⟨mode,exposed,geometry⟩ := (show state.machine.user.addresses.provenanceMode ≠ .strict ∧
        state.machine.user.addresses.exposed.contains input.id = true ∧
        WildcardGeneralHitReborrow.Geometry state.machine.user.addresses.intToPtrMap input.pointer.offset.bytes input.base input.id
          input.entry.allocation.byteSize from by simpa only [prov] using provenanceBinding)
      have geometry' : WildcardGeneralHitReborrow.Geometry active.machine.user.addresses.intToPtrMap
          (input.base+input.offset) input.base input.id stored.byteSize := by
        rw [writeSize,←input.pointerAddress]
        exact geometry
      have res := GeneralBorrowPositiveWildcardWindowPointerChecks.resolve context.pointers active input.base input.offset 1 input.id entry
        geometry' contexts.validationWidth mode exposed cached activePresent (by decide)
      simpa only [prov,provenance,S04ReturnBorrowBridge.extra,Pointer.withOptionalProvenance,Pointer.new] using res
  have read' : Allocation.readScalar stored context.access.runtime.base
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value) := by
    rw [contexts.sameRuntime]
    rw [←contexts.outerAccessEq]
    exact read
  have addressBound : place.mplace.ptr.offset.bytes.toNat+1<2^64 := by
    rw [input.physicalPointer]
    change input.pointer.offset.bytes.toNat+1<2^64
    have length := input.bytes
    omega
  have endpoint := DuplicatePrefix.source_end place.mplace.ptr.offset 1
    (by simpa using addressBound)
  have validation := S04ReturnActualBoolValidity.validate_actual context options remaining span contexts.accessEq
    after place.mplace input.id input.pointer.provenance provenance input.base input.offset input.capacity entry updated value fuel
    contexts.validationWidth input.cachedBase present size input.bounds writeMut read' mutation pointer input.aligned
    contexts.validationRuntimeSize resolved ghost shallow _ endpoint
  have memoryEq : CanonicalCopy.replaceAllocation after input.id entry.kind updated =
      CanonicalCopy.replaceAllocation state input.id input.entry.kind updated := by
    unfold after CanonicalCopy.replaceAllocation
    simp [entry,Array.filter_filter]
  rw [memoryEq] at validation
  refine ⟨updated,?_,clearExtra.trans writeTree,clearSize.trans writeSize,clearLen.trans writeLen,clearMut.trans writeMut⟩
  rw [input.layout]
  simp only [Bind.bind,EStateM.bind]
  erw [write]
  exact validation
/-- The actual configured return copy, including real Bool validation. -/
theorem copy_return {options : EvalConfigurationCore.Options} (limits : ExecutionMachine.Limits)
    {remaining : Nat} (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : CurrentCallBoolScalarWrite.Window state.machine place)
    (binding : CandidateCallBindings.WindowBinding state.machine input.pointer input.id input.offset.toNat 1)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (race : state.machine.dataRace = none) (backend : state.machine.user.payload.payload.user.backend = .none)
    (ghost : state.machine.user.payload.ghost = false) (shallow : state.machine.user.payload.validation = .Shallow)
    (ready : CurrentCallBoolProtection.WindowReady state.machine input.id input.offset.toNat 1)
    (completed : (input.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (resolvedBefore : (PreparedContracts.actualConfig options () (remaining+1) span).access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine)
    (value : Bool) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩) :
    ∃ updated, (GenericCallReturn.sourceControl
      (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyReturn ()
      ⟨.immediate (.scalar (Scalar.fromBool value)),RootCompilerFacts.boolLayout⟩ view state =
      (CanonicalCopy.replaceAllocation state input.id input.entry.kind updated,.ok ()) ∧
      updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let inner := PreparedContracts.actualConfig options () remaining span
  let bound := ExecutionMachine.withValidation config limits
  let hooks := (ExecutionMachine.projectionHooks bound).place
  let dest : RuntimePlace Provenance := ⟨.memory place.mplace,place.layout⟩
  let scalar : Immediate Provenance := .scalar (Scalar.fromBool value)
  obtain ⟨updated,combined,tree,size,length,mutable⟩ := validated_write span state place input binding tracker enabled
    race backend ghost shallow ready completed resolvedBefore value fuel
  obtain ⟨stored,write,_,_,_,_,_,_⟩ := CurrentCallBoolScalarWrite.configured options remaining span state place input tracker enabled
    race backend ready completed resolvedBefore value
  let afterStore := CanonicalCopy.replaceAllocation state input.id input.entry.kind stored
  let after := CanonicalCopy.replaceAllocation state input.id input.entry.kind updated
  have physical : PlaceMachine.writeMemory config.access (fun _ => true) scalar place state = .ok () afterStore := by
    rw [S04FinalReturnRuleScalar.scalar_policy config.access place (Scalar.fromBool value)
      (fun _ => true) config.compiler.willValidateMemory]
    exact write
  have validated : ValidityMachine.validateRuntime inner.validity () (fuel+1) dest true afterStore = .ok () after := by
    simp only [Bind.bind,EStateM.bind] at combined
    rw [write] at combined
    exact combined
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have noValidate : writePlaceImmediateNoValidate hooks () scalar dest state = .ok () afterStore := by
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    have sized : place.layout.layout.isSized = true := by rw [input.layout]; decide +kernel
    simp only [dest,sized,bind,pure]
    change config.projection.place.writeMemoryNoValidate () scalar place state = _
    rw [fields.projectionWriteMemory]
    have accessGhost : config.access.ghostMode = false := by
      rw [(DuplicatePrefixPhysicalContexts.canonical options remaining span).outerAccessEq]
      rfl
    have scope := S04ProtectUninitWrite.scopedAccess_of_not_ghost config.access state accessGhost ghost
    dsimp only [config] at scope
    have enforce : ValidityMachine.enforceValidity state = .ok true state := by
      simp [ValidityMachine.enforceValidity,shallow,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
    simp only [bind,EStateM.bind,scope,enforce]
    exact physical
  have enforced : hooks.enforceValidity () place.layout afterStore = .ok true afterStore := by
    change config.projection.place.enforceValidity () place.layout afterStore = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity,afterStore,CanonicalCopy.replaceAllocation,shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have checked : hooks.validate () dest afterStore = .ok () after := by
    change config.projection.place.validate () dest afterStore = _
    rw [fields.projectionValidate,CanonicalConfigFacts.actual_validate_successor,validationFuel]
    exact validated
  have actualWrite : (ExecutionMachine.rvalueHooks config limits).writeImmediate () scalar dest state = .ok () after := by
    change writePlaceImmediate hooks () scalar dest state = _
    unfold writePlaceImmediate
    simp only [bind,EStateM.bind,noValidate]
    erw [enforced]
    exact checked
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible,debugOff]
  have destLayout : dest.layout = RootCompilerFacts.boolLayout := input.layout
  have flag := GenericCallReturn.same_layout_transmute_flag hooks bound.copy PreparedReflection.actual.compiler ()
    RootCompilerFacts.boolLayout scalar dest destLayout compatible
  have exactCopy : copyRuntimePlace hooks bound.copy () ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ dest := by
    rw [flag]
    rfl
  obtain ⟨primitive,range,repr⟩ := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.boolLayout
    RootGenericBoolWrite.bool_initialized
  have copy := ActualScalarCopy.actual_copy_scalar options limits (remaining+1) span debugOff
    RootCompilerFacts.boolLayout scalar dest destLayout _ repr RootGenericBoolWrite.bool_sized
  refine ⟨updated,?_,size,length,mutable⟩
  change MachineHooks.run (copyRuntimePlace hooks bound.copy ()
    ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ view.toRuntimePlace true) state = _
  rw [destination,exactCopy,copy]
  unfold MachineHooks.run Call.run
  rw [actualWrite]

/-- Real root release/pop, scalar return copy and detached immediate cleanup. -/
theorem return_of_plan (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (beforeTracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (beforeTracked : beforeMachine.borrowTracker = some beforeTracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan beforeTracker.global.protectedTags borrowFrame.protectedTags.toList beforeMachine.memory releasedMemory)
    (thread : Miri.Concurrency.ThreadRecord) (active : beforeMachine.threads.activeThread? = some thread)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (stateEq : state = ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] frame
      (ActualPopPlan.released beforeMachine releasedMemory beforeTracker borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩)
    (sourceBody : frame.body = RootBody.reflected.body.body) (location : frame.location = .mir ⟨10,0⟩)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size) (noLocalClocks : frame.extra.dataRace = none)
    (beforeGhost : beforeMachine.user.payload.ghost = false) (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory)) (varargs : frame.vaList = #[])
    (place : MPlaceTy Provenance)
    (input : CurrentCallBoolScalarWrite.Window state.machine place)
    (binding : CandidateCallBindings.WindowBinding state.machine input.pointer input.id input.offset.toNat 1)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (race : state.machine.dataRace = none) (backend : state.machine.user.payload.payload.user.backend = .none)
    (ghost : state.machine.user.payload.ghost = false) (shallow : state.machine.user.payload.validation = .Shallow)
    (ready : CurrentCallBoolProtection.WindowReady state.machine input.id input.offset.toNat 1)
    (completed : (input.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (resolvedBefore : (PreparedContracts.actualConfig options () (remaining+1) span).access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine)
    (value : Bool) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool value))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (destination : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩) :
    ∃ updated, ControlFlow.returnFromCurrentFrame
      (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining+1) span) limits) () false
      (Storage.withCurrent #[] frame beforeMachine) = (CanonicalCopy.replaceAllocation state input.id input.entry.kind updated,.ok ()) ∧
      updated.byteSize = input.entry.allocation.byteSize ∧ updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let control := GenericCallReturn.sourceControl cfg limits
  let before := Storage.withCurrent #[] frame beforeMachine
  let result : OpTy Provenance := ⟨.immediate (.scalar (.fromBool value)),RootCompilerFacts.boolLayout⟩
  have read : control.returnOperand () before = (before,.ok result) :=
    PrimitiveCallReturn.read_current_return options limits (remaining+1) span #[] frame beforeMachine
      RootCompilerFacts.boolLayout (.scalar (.fromBool value)) valid0 live0 cached0 (by decide +kernel) noLocalClocks beforeGhost
  have pop : control.popFrame () before = (state,.ok frame) := by
    rw [stateEq]
    exact ActualPopPlan.pop_of_plan options limits (remaining+1) span #[] frame beforeMachine beforeTracker borrowFrame
      beforeTracked frameTracked releasedMemory plan thread active
  obtain ⟨updated,copied,size,length,mutable⟩ := copy_return limits span state place input binding tracker enabled race backend ghost shallow
    ready completed resolvedBefore value fuel debugOff validationFuel frame.returnPlace destination
  let after := CanonicalCopy.replaceAllocation state input.id input.entry.kind updated
  have cleanup := RootPhysicalReturnSupport.cleanup_actual_stop options limits (remaining+1) span after frame continuation immediateLocals varargs
  let block := RootBody.reflected.body.body.basicBlocks[10]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[10]? = some block := by rw [sourceBody];simp [block]
  have normal : block.cleanup = false := by with_unfolding_all rfl
  have empty : after.stack.frames = #[] := by rw [show after.stack.frames = state.stack.frames from rfl,stateEq]
  exact ⟨updated,RootPhysicalReturnSupport.normal_stop control () before before state after frame ⟨10,0⟩ block result
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt normal read pop copied cleanup continuation empty,size,length,mutable⟩

/-- Actual root Return step, including source accounting and a sequential release Plan. -/
theorem step_of_release_copy (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (beforeTracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (beforeTracked : beforeMachine.borrowTracker = some beforeTracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan beforeTracker.global.protectedTags borrowFrame.protectedTags.toList beforeMachine.memory releasedMemory)
    (thread : Miri.Concurrency.ThreadRecord) (active : beforeMachine.threads.activeThread? = some thread)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (stateEq : state = ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] frame
      (ActualPopPlan.released beforeMachine releasedMemory beforeTracker borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩)
    (sourceBody : frame.body = RootBody.reflected.body.body) (location : frame.location = .mir ⟨10,0⟩)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size) (noLocalClocks : frame.extra.dataRace = none)
    (beforeGhost : beforeMachine.user.payload.ghost = false) (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory)) (varargs : frame.vaList = #[])
    (place : MPlaceTy Provenance)
    (input : CurrentCallBoolScalarWrite.Window state.machine place)
    (binding : CandidateCallBindings.WindowBinding state.machine input.pointer input.id input.offset.toNat 1)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (race : state.machine.dataRace = none) (backend : state.machine.user.payload.payload.user.backend = .none)
    (ghost : state.machine.user.payload.ghost = false) (shallow : state.machine.user.payload.validation = .Shallow)
    (ready : CurrentCallBoolProtection.WindowReady state.machine input.id input.offset.toNat 1)
    (completed : (input.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (resolvedBefore : (PreparedContracts.actualConfig options () (remaining+1) span).access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine)
    (value : Bool) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool value))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (destination : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (initialMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (accountedEq : beforeMachine = (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining+1) span).terminators
      (Storage.withCurrent #[] frame initialMachine)).machine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initialMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initialMachine.user).gcInterval = 0)
    (fixed : initialMachine.threads.fixedScheduling = true) :
    ∃ updated, ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame initialMachine) = (CanonicalCopy.replaceAllocation state input.id input.entry.kind updated,.ok true) ∧
      updated.byteSize = input.entry.allocation.byteSize ∧ updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut := by
  obtain ⟨updated,returned,size,length,mutable⟩ := return_of_plan options limits remaining span frame beforeMachine beforeTracker borrowFrame
    beforeTracked frameTracked releasedMemory plan thread active state stateEq sourceBody location valid0 noLocalClocks beforeGhost continuation
    immediateLocals varargs place input binding tracker enabled race backend ghost shallow ready completed resolvedBefore value fuel debugOff validationFuel
    live0 cached0 destination
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] frame initialMachine
  let accounted := Storage.withCurrent #[] frame beforeMachine
  have accounting := SourceControl.before_terminator cfg limits () initial
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () initial = (accounted,.ok ()) := by
    simpa only [accounted,accountedEq,initial,SourceControl.accounted,Storage.withCurrent] using accounting
  let block := RootBody.reflected.body.body.basicBlocks[10]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[10]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[0]? = none := by with_unfolding_all rfl
  have kind : block.terminator.kind = .Return := by with_unfolding_all rfl
  exact ⟨updated,GenericCallReturn.return_step_exact cfg limits () initial accounted _ frame ⟨10,0⟩ block
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement kind accounting' returned,size,length,mutable⟩

end
end DuplicatePrefix.CurrentCallRootReturn
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallRootReturn." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current root return dependency {dependency}"
