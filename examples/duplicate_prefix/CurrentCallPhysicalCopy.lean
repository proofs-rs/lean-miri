import duplicate_prefix.S02SameDestinationAcceptedCopyDirectMemoryCore
import duplicate_prefix.CurrentCallBoolProtection
import duplicate_prefix.CopyHelperSteps
import duplicate_prefix.CopyHelperIntrinsic

/-! Adjacent initialized prefix copying with current direct provenance metadata
and synchronization entries outside each accessed window. Access completion is
an internal component certificate, to be derived by the logical consumer. -/
namespace DuplicatePrefix.CurrentCallPhysicalCopy
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.Concurrency Miri.Input
open CanonicalCopy MemoryCopyBridge
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem memory_access (context : PhysicalMachineWrite.Context)
    (machine : DuplicatePrefixCallSpecification.Before) (tracker : MachineHooks.BorrowState)
    (tree : BorrowTree) (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange) (write : Bool)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (ready : CurrentCallBoolProtection.WindowReady machine id range.start.bytes.toNat range.size.bytes.toNat)
    (completed : (tree.performBorrowAccessRange provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed) :
    PlaceMachine.memoryAccess context.access write ⟨machine,none⟩ tree id provenance range =
      ⟨⟨machine,none⟩,(tree.performBorrowAccessRange provenance range.start range.size
        (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed).tree,.ok ()⟩ := by
  obtain ⟨sync,present,outside⟩ := ready
  have present' : (context.extras.get machine.user).allocations.find? (fun row => row.1 == id) =
      some (id,⟨none,sync⟩) := present
  have syncDone := S04ReturnSyncOutside.sync_access_outside context.extras machine id range write ⟨none,sync⟩ present' outside
  have diagnostic : context.access.diagnostic write id range machine = .ok () machine := by
    simp [Context.access,EvalAccessMachine.make,EvalBackendMachine.access,EvalBackendMachine.handler,
      noBackend,noClocks,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,Except.pure,Except.bind]
  have weak : context.access.weakMemoryWrite = MemoryExtras.nonAtomicWrite context.extras := rfl
  have syncAccess : context.access.syncAccess = MemoryExtras.syncAccess context.extras := rfl
  unfold PlaceMachine.memoryAccess
  unfold_internal ".PlaceMachine.bridge"
  simp only [diagnostic,weak,syncAccess,pure,Id.run]
  rw [race_access_without_clocks machine id range (if write then some .Write else none) .Read noClocks]
  simp only [tracked]
  cases write
  · simp only [Bool.false_eq_true,↓reduceIte] at completed ⊢
    rw [syncDone]
    simp [completed]
  · simp only [↓reduceIte] at completed ⊢
    rw [S04ReturnExtrasAccess.weak_write_without_buffer context.extras machine id range sync present']
    simp only [tracked]
    rw [syncDone]
    simp [completed]

private theorem global_access (context : PhysicalMachineWrite.Context)
    (state : CanonicalConfigFacts.RootState) (tracker : MachineHooks.BorrowState)
    (allocation : Allocation Provenance BorrowTree) (kind : MemoryKind MiriMemoryKind)
    (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange) (write : Bool)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (ready : CurrentCallBoolProtection.WindowReady state.machine id range.start.bytes.toNat range.size.bytes.toNat)
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,⟨kind,allocation⟩))
    (completed : (allocation.extra.performBorrowAccessRange provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed) :
    source_global_access context.access write allocation id provenance range state =
      .ok (allocation.setExtra (allocation.extra.performBorrowAccessRange provenance range.start range.size
        (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed).tree)
        (replaceAllocation state id kind (allocation.setExtra (allocation.extra.performBorrowAccessRange provenance range.start range.size
          (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed).tree)) := by
  have accessed := memory_access context state.machine tracker allocation.extra id provenance range write noClocks noBackend tracked ready completed
  have retain : context.access.retainTouched = fun machine _ => machine := rfl
  unfold_internal ".GlobalMemoryCopyMachine.access"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind]
  rw [accessed]
  have anyLive := live_any_of_present state.machine.memory id ⟨kind,allocation⟩ live
  rw [anyLive,set_live_exact state.machine.memory id ⟨kind,allocation⟩ _ live]
  simp only [retain,pure,modify,modifyGet,MonadStateOf.modifyGet]
  rfl

theorem interval (context : PhysicalMachineWrite.Context)
    (state : CanonicalConfigFacts.RootState)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (bounded : offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : S02SameDestinationUninitProvenanceInput.DirectInput allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (readReady : CurrentCallBoolProtection.WindowReady state.machine id offset.toNat n.toNat)
    (writeReady : CurrentCallBoolProtection.WindowReady state.machine id (offset+n).toNat n.toNat)
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags
        .VisitChildrenOfAccessed).status = .Completed) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := replaceAllocation readState id kind writeAlloc
    ∃ result,
      GlobalMemoryCopyMachine.genericCopy context.access PointerMachine.User.addresses
        context.pointers.arithmetic (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset)))
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + (offset + n)))) (Size.ofBytes n) 1 true state =
        .ok () (replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset + n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len ∧
      S02SameDestinationAcceptedCopyPhysical.Physical result := by
  dsimp only
  let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  let readAlloc := allocation.setExtra readAccess.tree
  let readState := replaceAllocation state id kind readAlloc
  let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  let writeAlloc := readAlloc.setExtra writeAccess.tree
  let writeState := replaceAllocation readState id kind writeAlloc
  have readStorage := AllocationCopy.set_extra_preserves_storage allocation readAccess.tree
  have writeStorage := AllocationCopy.set_extra_preserves_storage readAlloc writeAccess.tree
  have writeBounds : offset.toNat + n.toNat + n.toNat ≤ writeAlloc.byteSize.bytes.toNat := by
    simpa only [writeAlloc, writeStorage.1, readAlloc, readStorage.1] using bounded
  have writeStored : writeAlloc.len = writeAlloc.byteSize.bytes.toNat := by
    simpa only [writeAlloc, writeStorage.1, writeStorage.2.1, readAlloc,
      readStorage.1, readStorage.2.1] using storage
  have writeMaskValid : InitMaskCopy.WellFormed writeAlloc.initializationMask := by
    simpa only [writeAlloc, writeStorage.2.2.1, readAlloc, readStorage.2.2.1] using maskValid
  have writeMaskLen : writeAlloc.initializationMask.len = writeAlloc.byteSize := by
    simpa only [writeAlloc, writeStorage.2.2.1, writeStorage.1, readAlloc,
      readStorage.2.2.1, readStorage.1] using maskLen
  have writeInitialized : InitMaskCopy.InitializedOn writeAlloc.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)) := by
    simpa only [writeAlloc, writeStorage.2.2.1, readAlloc, readStorage.2.2.1] using initialized
  have writeProvenance : S02SameDestinationUninitProvenanceInput.DirectInput writeAlloc.provenanceMap writeAlloc.len := by
    simpa only [writeAlloc, writeStorage.2.2.2.1, writeStorage.2.1, readAlloc,
      readStorage.2.2.2.1, readStorage.2.1] using valid
  have writeFits : writeAlloc.len + 64 < 18446744073709551616 := by
    simpa only [writeAlloc, writeStorage.2.1, readAlloc, readStorage.2.1] using storageFits
  have writeMutable : writeAlloc.mutability = .Mut := by
    simpa only [writeAlloc, writeStorage.2.2.2.2.1, readAlloc, readStorage.2.2.2.2.1] using mutable
  obtain ⟨result, copied, sizeResult, lenResult, extraResult, mutableResult,
      nativeResult, finalMaskValid, finalMaskLen, pointerBounds, bytesResult⟩ :=
    S02SameDestinationAcceptedCopyDirectAllocation.copy_adjacent_initialized_source writeAlloc offset n writeStored writeMaskValid writeMaskLen writeInitialized writeProvenance writeFits
      writeMutable positive writeBounds
  refine ⟨result, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have capFit : allocation.byteSize.bytes.toNat < 18446744073709551616 :=
      allocation.byteSize.bytes.toNat_lt_size
    have signedFits : n.toNat < 9223372036854775808 := by omega
    have fits : offset.toNat + n.toNat < 2 ^ 64 := by omega
    have equal : (offset + n).toNat = offset.toNat + n.toNat := by simp [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    have nBound : offset + n ≤ allocation.byteSize.bytes := by
      apply UInt64.le_iff_toNat_le.mpr
      omega
    have canonical : context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers := rfl
    have before : context.access.beforeAllocationAccess = fun _ => pure () := rfl
    have sourceGlobals : context.access.globalHooks =
        EvalGlobalAllocationMachine.make context.prepared context.image context.extras context.globals := rfl
    have pointerSize : context.pointers.arithmetic.pointerSize = Size.ofBytes 8 :=
      congrArg Miri.Memory.PointerArithmetic.pointerSize width
    have sourceCheck := MemoryCopyBridge.copy_pointer_stage_cached context.pointers context.access canonical
      state id tag base offset n ⟨kind, allocation⟩ width positive signedFits cached live
      (by change offset.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat; omega)
    have destinationCheck := MemoryCopyBridge.copy_pointer_stage_cached context.pointers context.access canonical
      state id tag base (offset + n) n ⟨kind, allocation⟩ width positive signedFits cached live (by
        change (offset + n).toNat + n.toNat ≤ allocation.byteSize.bytes.toNat
        omega)
    have probeId := MemoryCopyBridge.copy_probe_cached context.pointers context.access state.machine id tag base offset n width cached
    have probe := MemoryCopyBridge.before_allocation_stage_default context.access PointerMachine.User.addresses
      context.pointers.arithmetic state id before
    have sourceRaw := MemoryCopyBridge.source_raw_read_live context.access context.prepared context.image
      context.extras context.globals sourceGlobals state id ⟨kind, allocation⟩ live
    have readAccessFact := global_access context state tracker allocation kind id (.concrete tag)
      (allocRange (Size.ofBytes offset) (Size.ofBytes n)) false noClocks noBackend tracked readReady live readValid
    have readEffect : source_global_access context.access false allocation id (.concrete tag)
        (allocRange (Size.ofBytes offset) (Size.ofBytes n)) state = .ok readAlloc readState := by
      simpa only [Context.access, allocRange, Bool.false_eq_true, ↓reduceIte, readValid,
        readAccess, readAlloc, readState, replaceAllocation] using readAccessFact
    have readStored : readAlloc.len = readAlloc.byteSize.bytes.toNat := by
      simpa only [readAlloc, readStorage.1, readStorage.2.1] using storage
    have readMaskValid : InitMaskCopy.WellFormed readAlloc.initializationMask := by
      simpa only [readAlloc, readStorage.2.2.1] using maskValid
    have readMaskLen : readAlloc.initializationMask.len = readAlloc.byteSize := by
      simpa only [readAlloc, readStorage.2.2.1, readStorage.1] using maskLen
    have readInitialized : InitMaskCopy.InitializedOn readAlloc.initializationMask
        (Size.ofBytes offset) (Size.ofBytes (offset + n)) := by
      simpa only [readAlloc, readStorage.2.2.1] using initialized
    have readProvenance : S02SameDestinationUninitProvenanceInput.DirectInput readAlloc.provenanceMap readAlloc.len := by
      simpa only [readAlloc, readStorage.2.2.2.1, readStorage.2.1] using valid
    have readFits : readAlloc.len + 64 < 18446744073709551616 := by
      simpa only [readAlloc, readStorage.2.1] using storageFits
    have readMutable : readAlloc.mutability = .Mut := by
      simpa only [readAlloc, readStorage.2.2.2.2.1] using mutable
    have readBound : offset + n ≤ readAlloc.byteSize.bytes := by
      simpa only [readAlloc, readStorage.1] using nBound
    have snapshot := S02SameDestinationAcceptedCopyDirectAllocation.snapshot_checks_initialized_source context.access readAlloc offset n readState
      readStored readMaskValid readMaskLen readInitialized readProvenance readFits positive (by
        change offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat
        omega)
    have readLive : readState.machine.memory.live.find? (fun row => row.1 == id) =
        some (id, ⟨kind, readAlloc⟩) := replace_lookup state id kind readAlloc
    have destinationRaw := MemoryCopyBridge.source_raw_write_live context.access context.prepared context.image
      context.extras context.globals sourceGlobals readState id ⟨kind, readAlloc⟩ readLive readMutable
    have destinationBefore := MemoryCopyBridge.before_allocation_stage_default context.access PointerMachine.User.addresses
      context.pointers.arithmetic readState id before
    have writeAccessFact := global_access context readState tracker readAlloc kind id (.concrete tag)
      (allocRange (Size.ofBytes (offset+n)) (Size.ofBytes n)) true noClocks noBackend tracked writeReady readLive writeValid
    have writeEffect : source_global_access context.access true readAlloc id (.concrete tag)
        (allocRange (Size.ofBytes (offset + n)) (Size.ofBytes n)) readState = .ok writeAlloc writeState := by
      simpa only [Context.access, allocRange, Bool.true_eq, ↓reduceIte, writeValid,
        readAccess, readAlloc, writeAccess, writeAlloc, writeState, replaceAllocation,
        Allocation.setExtra, Allocation.mapExtra] using writeAccessFact
    have primitive : Allocation.copy readAlloc (allocRange (Size.ofBytes offset) (Size.ofBytes n))
        (Size.ofBytes (offset + n)) (Size.ofBytes 8) true true writeAlloc = .ok () result := by
      exact (AllocationCopy.copy_source_extra_irrelevant readAlloc writeAlloc
        (allocRange (Size.ofBytes offset) (Size.ofBytes n)) (Size.ofBytes (offset + n)) (Size.ofBytes 8) true true writeAccess.tree).symm.trans copied
    have copy : Allocation.copyRepeatedly readAlloc (allocRange (Size.ofBytes offset) (Size.ofBytes n))
        (Size.ofBytes (offset + n)) 1 context.pointers.arithmetic.pointerSize (id == id) true writeAlloc = .ok () result := by
      rw [pointerSize]
      simp only [beq_self_eq_true]
      exact primitive
    have writeLive : writeState.machine.memory.live.find? (fun row => row.1 == id) =
        some (id, ⟨kind, writeAlloc⟩) := replace_lookup readState id kind writeAlloc
    have commit := MemoryCopyBridge.set_live_exact writeState.machine.memory id ⟨kind, writeAlloc⟩ result writeLive
    have run := CopyComposition.generic_copy_success context.access PointerMachine.User.addresses context.pointers.arithmetic
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset)))
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + (offset + n)))) (Size.ofBytes n) (Size.ofBytes n) 1 true
      id id (Size.ofBytes offset) (Size.ofBytes (offset + n)) (.concrete tag) (.concrete tag)
      allocation readAlloc readAlloc writeAlloc result
      state state state state state readState readState readState readState writeState
      (replaceAllocation writeState id kind result).machine.memory
      sourceCheck (DuplicatePrefix.size_mul_one (Size.ofBytes n)) destinationCheck probeId probe sourceRaw
      (by rfl) readEffect (by simpa only [pointerSize] using snapshot) destinationRaw destinationBefore writeEffect copy commit
    simpa only [replaceAllocation, writeState, readState] using run
  · simpa only [writeAlloc, writeStorage.1, readAlloc, readStorage.1] using sizeResult
  · simpa only [writeAlloc, writeStorage.2.1, readAlloc, readStorage.2.1] using lenResult
  · simpa only [writeAlloc, Allocation.setExtra, Allocation.mapExtra] using extraResult
  · simpa only [writeAlloc, writeStorage.2.2.2.2.2.2, readAlloc,
      readStorage.2.2.2.2.2.2, writeStorage.2.1, readStorage.2.1] using bytesResult
  · exact ⟨mutableResult.trans writeMutable,finalMaskValid,finalMaskLen.trans sizeResult.symm,pointerBounds⟩



theorem actual_initialized_copy_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (location : frame.location = .mir ⟨7,8⟩)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : S02SameDestinationUninitProvenanceInput.DirectInput allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (readReady : CurrentCallBoolProtection.WindowReady machine id offset.toNat n.toNat)
    (writeReady : CurrentCallBoolProtection.WindowReady machine id (offset+n).toNat n.toNat)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
      (.concrete tag) (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (bounded : n ≤ (PreparedContracts.actualConfig options () remaining span).projection.maxSizeOfVal.bytes)
    (valid14 : (14 : MIR.LocalId) < frame.locals.size)
    (valid15 : (15 : MIR.LocalId) < frame.locals.size)
    (valid16 : (16 : MIR.LocalId) < frame.locals.size)
    (live14 : frame.locals[14].value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))))))
    (live15 : frame.locals[15].value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+(offset+n))))))))
    (live16 : frame.locals[16].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache14 : frame.locals[14].layout = some CopyCompilerFacts.sourcePointerLayout)
    (cache15 : frame.locals[15].layout = some CopyCompilerFacts.destPointerLayout)
    (cache16 : frame.locals[16].layout = some RootCompilerFacts.usizeLayout)
    (localClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    let state := Storage.withCurrent frames frame machine
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
    ∃ result,
      ExecutionMachine.step config limits () state =
        (Storage.withCurrent frames {frame with location := .mir ⟨7,9⟩}
          (CanonicalCopy.replaceAllocation writeState id kind result).machine,.ok true) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len ∧
      S02SameDestinationAcceptedCopyPhysical.Physical result := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨context, accessEq, arithmeticEq, alignment⟩ := fields.canonicalCopy
  have width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩ :=
    arithmeticEq.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have fullBounds : offset.toNat+n.toNat+n.toNat ≤ allocation.byteSize.bytes.toNat := by omega
  have copy := interval context state tracker id tag base offset n kind allocation
    width positive fullBounds storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend
    tracked readReady writeReady live cached readValid writeValid
  dsimp only at copy
  obtain ⟨result, copied, sizeEq, lenEq, treeEq, bytesEq,physical⟩ := copy
  refine ⟨result, ?_,sizeEq,lenEq,treeEq,bytesEq,physical⟩
  obtain ⟨other,otherArithmetic,otherResolve,reduction⟩ := CopyHelperIntrinsic.actual_generic_copy options limits remaining span debugOff
    frames frame machine (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))
    (Pointer.new (.concrete id tag) (Size.ofBytes (base+(offset+n)))) n valid14 valid15 valid16
    live14 live15 live16 cache14 cache15 cache16 localClocks ghost bounded
  rw [← otherArithmetic,arithmeticEq,accessEq] at reduction
  let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
  let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
  let finalMachine := (CanonicalCopy.replaceAllocation writeState id kind result).machine
  have effect : (ExecutionMachine.stepHooks config limits).intrinsic ()
      (.CopyNonOverlapping ⟨.Move ⟨14,#[]⟩,.Move ⟨15,#[]⟩,.Move ⟨16,#[]⟩⟩) state =
      (Storage.withCurrent frames frame finalMachine,.ok ()) := by
    rw [reduction]
    unfold MachineHooks.run Call.run
    simp only [Pointer.withOptionalProvenance, Pointer.new, state] at copied ⊢
    rw [copied]
    rfl
  exact CopyHelperSteps.intrinsic_of_actual_effect config limits frames frame frame machine finalMachine
    ⟨7,8⟩ _ location location (by rw [sourceBody];exact CopyHelperFacts.copy_intrinsic_statement) effect

end DuplicatePrefix.CurrentCallPhysicalCopy
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallPhysicalCopy." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current physical copy dependency {dependency}"
