import duplicate_prefix.MemoryCopyBridge
import duplicate_prefix.CopyComposition
import duplicate_prefix.BorrowCopyRanges
import duplicate_prefix.OffsetAllocationCopy
import duplicate_prefix.ProvenanceAllocationCopy
import duplicate_prefix.MixedBorrowAccess
import duplicate_prefix.CompleteAllocationCopy
import duplicate_prefix.ProtectedBorrowAccess

/-! Specialization of the actual copy driver to source-owned configuration
constructors and a concrete live byte allocation. Compiler/global capabilities
remain parameters, but core memory, Tree Borrows, extras storage and pointer
resolution are the original source implementations. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.CanonicalCopy
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open Miri.Input

abbrev User (Os R P H D O Aff B Host : Type) := EvalCoreMachine.User Os R P H D O Aff B Host

structure Context (Os R P H D O Aff B Host : Type) where
  prepared : CompilerProviders.Prepared
  image : AllocationImage.Imported
  maximum : Size
  fuel : Nat
  globals : GlobalAllocationMachine.Leaves MiriMemoryKind (User Os R P H D O Aff B Host)
  pointers : PointerMachine.Hooks MiriMemoryKind
    (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D O Aff B Host))
  sync : P → SyncObject.AccessKind → PlaceMachine.MachineM MiriMemoryKind
    (User Os R P H D O Aff B Host) Unit
  weakError : StoreBufferAllocError → StepError

def Context.extras (context : Context Os R P H D O Aff B Host) :=
  EvalCoreMachine.extras context.sync context.weakError

def Context.globalHooks (context : Context Os R P H D O Aff B Host) :=
  EvalGlobalAllocationMachine.make context.prepared context.image context.extras context.globals

def Context.access (context : Context Os R P H D O Aff B Host) :=
  EvalAccessMachine.make context.prepared context.image context.maximum context.fuel
    context.globalHooks context.pointers context.extras

/-- The exact heap update used by MemoryState.setLiveAllocation. It is a
post-state description; MemoryCopyBridge.set_live_exact connects it to the
original operation. -/
def replaceAllocation (state : MachineHooks.State K U) (id : AllocId) (kind : MemoryKind K)
    (allocation : Allocation Provenance BorrowTree) : MachineHooks.State K U :=
  {state with machine := {state.machine with memory := {state.machine.memory with live := (state.machine.memory.live.filter fun row => row.1 != id).push (id, ⟨kind, allocation⟩)}}}

theorem replace_lookup (state : MachineHooks.State K U) (id : AllocId) (kind : MemoryKind K)
    (allocation : Allocation Provenance BorrowTree) :
    (replaceAllocation state id kind allocation).machine.memory.live.find?
      (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩) := by
  exact MemoryCopyBridge.live_lookup_replaced state.machine.memory id ⟨kind, allocation⟩

private theorem canonical_prefix_success {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (bounded : n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (provenance : allocation.provenanceMap = ProvenanceMap.new)
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
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes n) (Size.ofBytes n) .Write tracker.global.protectedTags
        .VisitChildrenOfAccessed).status = .Completed) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes n) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := replaceAllocation readState id kind writeAlloc
    ∃ result,
      GlobalMemoryCopyMachine.genericCopy context.access PointerMachine.User.addresses
        context.pointers.arithmetic (Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + n))) (Size.ofBytes n) 1 true state =
        .ok () (replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 n.toNat ++
        (AllocationCopy.snapshot allocation).extract 0 n.toNat ++
        (AllocationCopy.snapshot allocation).extract (n + n).toNat allocation.len := by
  dsimp only
  let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
    Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  let readAlloc := allocation.setExtra readAccess.tree
  let readState := replaceAllocation state id kind readAlloc
  let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes n) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  let writeAlloc := readAlloc.setExtra writeAccess.tree
  let writeState := replaceAllocation readState id kind writeAlloc
  have readStorage := AllocationCopy.set_extra_preserves_storage allocation readAccess.tree
  have writeStorage := AllocationCopy.set_extra_preserves_storage readAlloc writeAccess.tree
  have writeBounds : n.toNat + n.toNat ≤ writeAlloc.byteSize.bytes.toNat := by
    simpa only [writeAlloc, writeStorage.1, readAlloc, readStorage.1] using bounded
  have writeStored : writeAlloc.len = writeAlloc.byteSize.bytes.toNat := by
    simpa only [writeAlloc, writeStorage.1, writeStorage.2.1, readAlloc,
      readStorage.1, readStorage.2.1] using storage
  have writeInitialized : writeAlloc.initializationMask = InitMask.new writeAlloc.byteSize true := by
    simpa only [writeAlloc, writeStorage.1, writeStorage.2.2.1, readAlloc,
      readStorage.1, readStorage.2.2.1] using initialized
  have writeProvenance : writeAlloc.provenanceMap = ProvenanceMap.new := by
    simpa only [writeAlloc, writeStorage.2.2.2.1, readAlloc, readStorage.2.2.2.1] using provenance
  have writeMutable : writeAlloc.mutability = .Mut := by
    simpa only [writeAlloc, writeStorage.2.2.2.2.1, readAlloc, readStorage.2.2.2.2.1] using mutable
  obtain ⟨result, copied, sizeResult, lenResult, extraResult, mutableResult, initResult,
      provenanceResult, nativeResult, bytesResult⟩ :=
    AllocationCopy.copy_adjacent_initialized writeAlloc n writeStored writeInitialized writeProvenance
      writeMutable positive writeBounds
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
  · have capFit : allocation.byteSize.bytes.toNat < 18446744073709551616 :=
      allocation.byteSize.bytes.toNat_lt_size
    have signedFits : n.toNat < 9223372036854775808 := by omega
    have nBound : n ≤ allocation.byteSize.bytes := by
      apply UInt64.le_iff_toNat_le.mpr
      omega
    have canonical : context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers := rfl
    have before : context.access.beforeAllocationAccess = fun _ => pure () := rfl
    have sourceGlobals : context.access.globalHooks =
        EvalGlobalAllocationMachine.make context.prepared context.image context.extras context.globals := rfl
    have pointerSize : context.pointers.arithmetic.pointerSize = Size.ofBytes 8 :=
      congrArg Miri.Memory.PointerArithmetic.pointerSize width
    have sourceCheck := MemoryCopyBridge.copy_pointer_stage_cached context.pointers context.access canonical
      state id tag base 0 n ⟨kind, allocation⟩ width positive signedFits cached live
      (by simpa using Nat.le_trans (Nat.le_add_right n.toNat n.toNat) bounded)
    simp only [UInt64.add_zero, Size.ofBytes] at sourceCheck
    have destinationCheck := MemoryCopyBridge.copy_pointer_stage_cached context.pointers context.access canonical
      state id tag base n n ⟨kind, allocation⟩ width positive signedFits cached live bounded
    have probeId := MemoryCopyBridge.copy_probe_cached context.pointers context.access state.machine id tag base 0 n width cached
    simp only [UInt64.add_zero] at probeId
    have probe := MemoryCopyBridge.before_allocation_stage_default context.access PointerMachine.User.addresses
      context.pointers.arithmetic state id before
    have sourceRaw := MemoryCopyBridge.source_raw_read_live context.access context.prepared context.image
      context.extras context.globals sourceGlobals state id ⟨kind, allocation⟩ live
    have readAccessFact := MemoryCopyBridge.source_global_access_exact context.prepared context.image
      context.maximum context.fuel context.globalHooks context.pointers context.extras state tracker allocation
      kind id (.concrete tag) (allocRange Size.ZERO (Size.ofBytes n)) false
      noClocks noBackend tracked extras live
    have readEffect : source_global_access context.access false allocation id (.concrete tag)
        (allocRange Size.ZERO (Size.ofBytes n)) state = .ok readAlloc readState := by
      simpa only [Context.access, allocRange, Bool.false_eq_true, ↓reduceIte, readValid,
        readAccess, readAlloc, readState, replaceAllocation] using readAccessFact
    have readStored : readAlloc.len = readAlloc.byteSize.bytes.toNat := by
      simpa only [readAlloc, readStorage.1, readStorage.2.1] using storage
    have readInitialized : readAlloc.initializationMask = InitMask.new readAlloc.byteSize true := by
      simpa only [readAlloc, readStorage.1, readStorage.2.2.1] using initialized
    have readProvenance : readAlloc.provenanceMap = ProvenanceMap.new := by
      simpa only [readAlloc, readStorage.2.2.2.1] using provenance
    have readMutable : readAlloc.mutability = .Mut := by
      simpa only [readAlloc, readStorage.2.2.2.2.1] using mutable
    have readBound : n ≤ readAlloc.byteSize.bytes := by
      simpa only [readAlloc, readStorage.1] using nBound
    have snapshot := MemoryCopyBridge.snapshot_checks_plain context.access readAlloc n readState
      readStored readInitialized readProvenance positive readBound
    have readLive : readState.machine.memory.live.find? (fun row => row.1 == id) =
        some (id, ⟨kind, readAlloc⟩) := replace_lookup state id kind readAlloc
    have destinationRaw := MemoryCopyBridge.source_raw_write_live context.access context.prepared context.image
      context.extras context.globals sourceGlobals readState id ⟨kind, readAlloc⟩ readLive readMutable
    have destinationBefore := MemoryCopyBridge.before_allocation_stage_default context.access PointerMachine.User.addresses
      context.pointers.arithmetic readState id before
    have writeAccessFact := MemoryCopyBridge.source_global_access_exact context.prepared context.image
      context.maximum context.fuel context.globalHooks context.pointers context.extras readState tracker readAlloc
      kind id (.concrete tag) (allocRange (Size.ofBytes n) (Size.ofBytes n)) true
      noClocks noBackend tracked extras readLive
    have writeEffect : source_global_access context.access true readAlloc id (.concrete tag)
        (allocRange (Size.ofBytes n) (Size.ofBytes n)) readState = .ok writeAlloc writeState := by
      simpa only [Context.access, allocRange, Bool.true_eq, ↓reduceIte, writeValid,
        readAccess, readAlloc, writeAccess, writeAlloc, writeState, replaceAllocation,
        Allocation.setExtra, Allocation.mapExtra] using writeAccessFact
    have primitive : Allocation.copy readAlloc (allocRange Size.ZERO (Size.ofBytes n))
        (Size.ofBytes n) (Size.ofBytes 8) true true writeAlloc = .ok () result := by
      exact (AllocationCopy.copy_source_extra_irrelevant readAlloc writeAlloc
        (allocRange Size.ZERO (Size.ofBytes n)) (Size.ofBytes n) (Size.ofBytes 8) true true writeAccess.tree).symm.trans copied
    have copy : Allocation.copyRepeatedly readAlloc (allocRange Size.ZERO (Size.ofBytes n))
        (Size.ofBytes n) 1 context.pointers.arithmetic.pointerSize (id == id) true writeAlloc = .ok () result := by
      rw [pointerSize]
      simp only [beq_self_eq_true]
      exact primitive
    have writeLive : writeState.machine.memory.live.find? (fun row => row.1 == id) =
        some (id, ⟨kind, writeAlloc⟩) := replace_lookup readState id kind writeAlloc
    have commit := MemoryCopyBridge.set_live_exact writeState.machine.memory id ⟨kind, writeAlloc⟩ result writeLive
    have run := CopyComposition.generic_copy_success context.access PointerMachine.User.addresses context.pointers.arithmetic
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + n))) (Size.ofBytes n) (Size.ofBytes n) 1 true
      id id Size.ZERO (Size.ofBytes n) (.concrete tag) (.concrete tag)
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

private theorem canonical_interval_success {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (bounded : offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (provenance : allocation.provenanceMap = ProvenanceMap.new)
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
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
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
  have writeInitialized : writeAlloc.initializationMask = InitMask.new writeAlloc.byteSize true := by
    simpa only [writeAlloc, writeStorage.1, writeStorage.2.2.1, readAlloc,
      readStorage.1, readStorage.2.2.1] using initialized
  have writeProvenance : writeAlloc.provenanceMap = ProvenanceMap.new := by
    simpa only [writeAlloc, writeStorage.2.2.2.1, readAlloc, readStorage.2.2.2.1] using provenance
  have writeMutable : writeAlloc.mutability = .Mut := by
    simpa only [writeAlloc, writeStorage.2.2.2.2.1, readAlloc, readStorage.2.2.2.2.1] using mutable
  obtain ⟨result, copied, sizeResult, lenResult, extraResult, mutableResult, initResult,
      provenanceResult, nativeResult, bytesResult⟩ :=
    OffsetAllocationCopy.copy_adjacent_at_initialized writeAlloc offset n writeStored writeInitialized writeProvenance
      writeMutable positive writeBounds
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
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
    have readInitialized : readAlloc.initializationMask = InitMask.new readAlloc.byteSize true := by
      simpa only [readAlloc, readStorage.1, readStorage.2.2.1] using initialized
    have readProvenance : readAlloc.provenanceMap = ProvenanceMap.new := by
      simpa only [readAlloc, readStorage.2.2.2.1] using provenance
    have readMutable : readAlloc.mutability = .Mut := by
      simpa only [readAlloc, readStorage.2.2.2.2.1] using mutable
    have readBound : offset + n ≤ readAlloc.byteSize.bytes := by
      simpa only [readAlloc, readStorage.1] using nBound
    have snapshot := OffsetAllocationCopy.snapshot_checks_interval context.access readAlloc offset n readState
      readStored readInitialized readProvenance positive (by
        change offset.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat
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

private theorem canonical_interval_provenance_success {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (bounded : offset.toNat + n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 16 < 18446744073709551616)
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
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
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
  have writeInitialized : writeAlloc.initializationMask = InitMask.new writeAlloc.byteSize true := by
    simpa only [writeAlloc, writeStorage.1, writeStorage.2.2.1, readAlloc,
      readStorage.1, readStorage.2.2.1] using initialized
  have writeProvenance : ProvenanceCopy.WellFormed writeAlloc.provenanceMap writeAlloc.len := by
    simpa only [writeAlloc, writeStorage.2.2.2.1, writeStorage.2.1, readAlloc,
      readStorage.2.2.2.1, readStorage.2.1] using valid
  have writeFits : writeAlloc.len + 16 < 18446744073709551616 := by
    simpa only [writeAlloc, writeStorage.2.1, readAlloc, readStorage.2.1] using storageFits
  have writeMutable : writeAlloc.mutability = .Mut := by
    simpa only [writeAlloc, writeStorage.2.2.2.2.1, readAlloc, readStorage.2.2.2.2.1] using mutable
  obtain ⟨result, copied, sizeResult, lenResult, extraResult, mutableResult, initResult,
      nativeResult, bytesResult⟩ :=
    ProvenanceAllocationCopy.copy_adjacent_at_initialized_provenance writeAlloc offset n writeStored writeInitialized writeProvenance writeFits
      writeMutable positive writeBounds
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
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
    have readInitialized : readAlloc.initializationMask = InitMask.new readAlloc.byteSize true := by
      simpa only [readAlloc, readStorage.1, readStorage.2.2.1] using initialized
    have readProvenance : ProvenanceCopy.WellFormed readAlloc.provenanceMap readAlloc.len := by
      simpa only [readAlloc, readStorage.2.2.2.1, readStorage.2.1] using valid
    have readFits : readAlloc.len + 16 < 18446744073709551616 := by
      simpa only [readAlloc, readStorage.2.1] using storageFits
    have readMutable : readAlloc.mutability = .Mut := by
      simpa only [readAlloc, readStorage.2.2.2.2.1] using mutable
    have readBound : offset + n ≤ readAlloc.byteSize.bytes := by
      simpa only [readAlloc, readStorage.1] using nBound
    have snapshot := ProvenanceAllocationCopy.snapshot_checks_interval_provenance context.access readAlloc offset n readState
      readStored readInitialized readProvenance readFits positive (by
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

private theorem canonical_interval_initialized_success {Os R P H D O Aff B Host : Type}
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
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
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
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
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
  have writeProvenance : ProvenanceCopy.WellFormed writeAlloc.provenanceMap writeAlloc.len := by
    simpa only [writeAlloc, writeStorage.2.2.2.1, writeStorage.2.1, readAlloc,
      readStorage.2.2.2.1, readStorage.2.1] using valid
  have writeFits : writeAlloc.len + 64 < 18446744073709551616 := by
    simpa only [writeAlloc, writeStorage.2.1, readAlloc, readStorage.2.1] using storageFits
  have writeMutable : writeAlloc.mutability = .Mut := by
    simpa only [writeAlloc, writeStorage.2.2.2.2.1, readAlloc, readStorage.2.2.2.2.1] using mutable
  obtain ⟨result, copied, sizeResult, lenResult, extraResult, mutableResult,
      nativeResult, finalMaskValid, finalMaskLen, bytesResult⟩ :=
    CompleteAllocationCopy.copy_adjacent_initialized_source writeAlloc offset n writeStored writeMaskValid writeMaskLen writeInitialized writeProvenance writeFits
      writeMutable positive writeBounds
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
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
    have readProvenance : ProvenanceCopy.WellFormed readAlloc.provenanceMap readAlloc.len := by
      simpa only [readAlloc, readStorage.2.2.2.1, readStorage.2.1] using valid
    have readFits : readAlloc.len + 64 < 18446744073709551616 := by
      simpa only [readAlloc, readStorage.2.1] using storageFits
    have readMutable : readAlloc.mutability = .Mut := by
      simpa only [readAlloc, readStorage.2.2.2.2.1] using mutable
    have readBound : offset + n ≤ readAlloc.byteSize.bytes := by
      simpa only [readAlloc, readStorage.1] using nBound
    have snapshot := CompleteAllocationCopy.snapshot_checks_initialized_source context.access readAlloc offset n readState
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

theorem canonical_prefix_copy {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (bounded : n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (provenance : allocation.provenanceMap = ProvenanceMap.new)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (Miri.DataStructures.DedupRangeMap.new allocation.byteSize (BorrowRangeAccess.childLocation false)))
    (protectors : tracker.global.protectedTags = BorrowRangeAccess.childProtected tag) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes n) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := replaceAllocation readState id kind writeAlloc
    ∃ result,
      GlobalMemoryCopyMachine.genericCopy context.access PointerMachine.User.addresses
        context.pointers.arithmetic (Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + n))) (Size.ofBytes n) 1 true state =
        .ok () (replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 n.toNat ++
        (AllocationCopy.snapshot allocation).extract 0 n.toNat ++
        (AllocationCopy.snapshot allocation).extract (n + n).toNat allocation.len := by
  have ranges := BorrowCopyRanges.canonical_copy_borrow_access rootTag tag allocation.byteSize.bytes n
    distinct positive bounded
  have readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, protectors, Size.ofBytes] using ranges.1
  have writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes n) (Size.ofBytes n) .Write tracker.global.protectedTags
        .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, protectors, Size.ofBytes] using ranges.2
  exact canonical_prefix_success context state tracker id tag base n kind allocation width positive bounded
    storage initialized provenance mutable noClocks noBackend tracked extras live cached readValid writeValid

theorem canonical_prefix_provenance_copy {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (bounded : n.toNat + n.toNat ≤ allocation.byteSize.bytes.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 16 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (Miri.DataStructures.DedupRangeMap.new allocation.byteSize (BorrowRangeAccess.childLocation false)))
    (protectors : tracker.global.protectedTags = BorrowRangeAccess.childProtected tag) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readAlloc := allocation.setExtra readAccess.tree
    let readState := replaceAllocation state id kind readAlloc
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes n) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAlloc := readAlloc.setExtra writeAccess.tree
    let writeState := replaceAllocation readState id kind writeAlloc
    ∃ result,
      GlobalMemoryCopyMachine.genericCopy context.access PointerMachine.User.addresses
        context.pointers.arithmetic (Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + n))) (Size.ofBytes n) 1 true state =
        .ok () (replaceAllocation writeState id kind result) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 n.toNat ++
        (AllocationCopy.snapshot allocation).extract 0 n.toNat ++
        (AllocationCopy.snapshot allocation).extract (n + n).toNat allocation.len := by
  have ranges := BorrowCopyRanges.canonical_copy_borrow_access rootTag tag allocation.byteSize.bytes n
    distinct positive bounded
  have readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, protectors, Size.ofBytes] using ranges.1
  have writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      Size.ZERO (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes n) (Size.ofBytes n) .Write tracker.global.protectedTags
        .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, protectors, Size.ofBytes] using ranges.2
  have result := canonical_interval_provenance_success context state tracker id tag base 0 n kind allocation
    width positive (by simpa using bounded) storage initialized valid storageFits mutable noClocks noBackend
    tracked extras live cached (by simpa only [Size.ZERO, Size.ofBytes] using readValid) (by simpa only [Size.ZERO, Size.ofBytes, UInt64.zero_add] using writeValid)
  simpa only [UInt64.zero_add, UInt64.add_zero, UInt64.toNat_zero, Nat.zero_add, Size.ZERO, Size.ofBytes] using result

theorem canonical_slice_provenance_copy {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 16 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false)))
    (protectors : tracker.global.protectedTags = BorrowRangeAccess.childProtected tag) :
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
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  have ranges := MixedBorrowAccess.canonical_slice_copy_borrow rootTag tag allocation.byteSize.bytes
    offset sliceLen n distinct positive sliceBounds copyBounds
  have readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, protectors] using ranges.1
  have writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags
        .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, protectors] using ranges.2.1
  exact canonical_interval_provenance_success context state tracker id tag base offset n kind allocation width positive
    (by omega) storage initialized valid storageFits mutable noClocks noBackend tracked extras live cached readValid writeValid

theorem canonical_slice_initialized_copy {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
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
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false)))
    (protectors : tracker.global.protectedTags = BorrowRangeAccess.childProtected tag) :
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
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  have ranges := MixedBorrowAccess.canonical_slice_copy_borrow rootTag tag allocation.byteSize.bytes
    offset sliceLen n distinct positive sliceBounds copyBounds
  have readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, protectors] using ranges.1
  have writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags
        .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, protectors] using ranges.2.1
  exact canonical_interval_initialized_success context state tracker id tag base offset n kind allocation width positive
    (by omega) storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached readValid writeValid

theorem canonical_slice_initialized_copy_protected {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (rootTag : BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
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
    (distinct : rootTag ≠ tag)
    (tree : allocation.extra = BorrowRangeAccess.canonicalChildTree rootTag tag
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false)))
    (rootFree : tracker.global.protectedTags.contains rootTag = false)
    (childHeld : tracker.global.protectedTags.contains tag = true) :
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
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  have ranges := ProtectedBorrowAccess.canonical_slice_copy_borrow2 rootTag tag tracker.global.protectedTags rootFree childHeld allocation.byteSize.bytes
    offset sliceLen n distinct positive sliceBounds copyBounds
  have readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree] using ranges.1
  have writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags
        .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree] using ranges.2.1
  exact canonical_interval_initialized_success context state tracker id tag base offset n kind allocation width positive
    (by omega) storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached readValid writeValid

theorem canonical_nested_initialized_copy {Os R P H D O Aff B Host : Type}
    (context : Context Os R P H D O Aff B Host)
    (state : MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (tags : Fin 6 → BorTag) (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
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
    (distinct : Function.Injective tags)
    (tagAt : tag = tags 5)
    (tree : allocation.extra = NestedBorrowAccess.nestedTree tags
      (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset + sliceLen)
        BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false)))
    (protectionMask : ProtectedBorrowAccess.SixMask tags tracker.global.protectedTags false) :
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
        (AllocationCopy.snapshot allocation).extract (offset + n + n).toNat allocation.len := by
  have ranges := ProtectedBorrowAccess.canonical_slice_copy_borrow6 tags tracker.global.protectedTags protectionMask allocation.byteSize.bytes
    offset sliceLen n distinct positive sliceBounds copyBounds
  have readValid : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, tagAt] using ranges.1
  have writeValid : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write tracker.global.protectedTags
        .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [tree, tagAt] using ranges.2.1
  exact canonical_interval_initialized_success context state tracker id tag base offset n kind allocation width positive
    (by omega) storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached readValid writeValid

#print axioms canonical_nested_initialized_copy
#print axioms canonical_slice_initialized_copy_protected
#print axioms canonical_slice_initialized_copy
#print axioms canonical_slice_provenance_copy

#print axioms canonical_prefix_provenance_copy
#print axioms canonical_prefix_copy

#print axioms canonical_prefix_success

open Lean Elab Command in
run_cmd do
  for declaration in [``canonical_prefix_success, ``canonical_interval_success, ``canonical_interval_provenance_success, ``canonical_prefix_copy, ``canonical_prefix_provenance_copy, ``canonical_slice_provenance_copy, ``canonical_interval_initialized_success, ``canonical_slice_initialized_copy, ``canonical_slice_initialized_copy_protected, ``canonical_nested_initialized_copy] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end DuplicatePrefix.CanonicalCopy
