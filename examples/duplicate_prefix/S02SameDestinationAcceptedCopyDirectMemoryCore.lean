import duplicate_prefix.CanonicalCopy
import duplicate_prefix.S02SameDestinationAcceptedCopyPhysical
import duplicate_prefix.S02SameDestinationAcceptedCopyDirectAllocation

namespace DuplicatePrefix.S02SameDestinationAcceptedCopyDirectMemoryCore
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.Concurrency Miri.Input
open DuplicatePrefix.CanonicalCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem interval {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
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
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
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
    have readAccessFact := MemoryCopyBridge.source_global_access_exact context.prepared context.image
      context.maximum context.fuel context.globalHooks context.pointers context.extras state tracker allocation
      kind id (.concrete tag) (allocRange (Size.ofBytes offset) (Size.ofBytes n)) false
      noClocks noBackend tracked extras live
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
    have writeAccessFact := MemoryCopyBridge.source_global_access_exact context.prepared context.image
      context.maximum context.fuel context.globalHooks context.pointers context.extras readState tracker readAlloc
      kind id (.concrete tag) (allocRange (Size.ofBytes (offset + n)) (Size.ofBytes n)) true
      noClocks noBackend tracked extras readLive
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



end DuplicatePrefix.S02SameDestinationAcceptedCopyDirectMemoryCore
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedCopyDirectMemoryCore.interval) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic copy memory core dependency {dependency}"
