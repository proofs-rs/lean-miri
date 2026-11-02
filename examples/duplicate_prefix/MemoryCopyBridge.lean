import duplicate_prefix.AllocationCopy
import duplicate_prefix.PointerArithmetic
import duplicate_prefix.PointerAccess
import Miri.Input.EvalAccessMachine

/-! Bridges to the canonical memory-copy machinery. The pointer lemmas use
the actual cached-address lookup and typed resolver supplied by
EvalAccessMachine.make; the cache and heap premises are concrete state facts,
not assumptions that a memory operation succeeds. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.MemoryCopyBridge
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Miri.Interpreter

open Lean Elab in
private def sourceHelper (suffix : String) : CoreM Name := do
  let candidates := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError "expected one original source helper {suffix}, found {candidates.length}"

open Lean Elab in
elab "source_snapshot_checks" : term => do
  return mkConst (← sourceHelper ".GlobalMemoryCopyMachine.snapshotChecks")

open Lean Elab in
elab "source_global_raw" : term => do
  return mkConst (← sourceHelper ".GlobalMemoryCopyMachine.raw")

open Lean Elab in
elab "source_global_access" : term => do
  return mkConst (← sourceHelper ".GlobalMemoryCopyMachine.access")

open Lean Elab in
elab "source_memory_hook" : term => do
  return mkConst (← sourceHelper ".GlobalMemoryCopyMachine.memoryHook")

open Lean Elab in
elab "source_tree_error" : term => do
  return mkConst (← sourceHelper ".PlaceMachine.treeError")

/-- Source-derived adapter, definitionally equal to the production hook below.
It exposes only the pointer stage so kernel proofs do not expand unrelated
fields of the complete memory-hook record. -/
private def sourceSignedAccess (config : PlaceMachine.AccessConfig K U)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) (signed : Int) :
    PlaceMachine.MachineM K U (Option (AllocId × Size × ProvenanceExtra)) := do
  if signed == 0 then return none
  let memory := (← get).memory
  let resolved ← config.resolvePointer memory pointer signed
  match checkAndDerefPtr arithmetic pointer signed .memoryAccess (fun _ _ => resolved) memory.getAllocInfo with
  | .ok result => return result.map fun checked =>
      (checked.pointer.allocId, checked.pointer.offset, checked.pointer.extra)
  | .error (.allocationLookup (.unavailable id)) => throw (.callback s!"missing allocation metadata {id.value}")
  | .error error => throw (.undefinedBehavior (toString error))

private def sourcePointerAccess (config : PlaceMachine.AccessConfig K U)
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance)) (size : Size) :
    PlaceMachine.MachineM K U (Option (AllocId × Size × ProvenanceExtra)) := do
  let signed ← match sizeAsI64 size with
    | .ok value => pure value
    | .error error => throw (.undefinedBehavior (toString error))
  sourceSignedAccess config arithmetic pointer signed

theorem pointer_access_source {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U) (addresses : U → GlobalAddressState)
    (arithmetic : PointerArithmetic) (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (state : PlaceMachine.AccessState K U) (pointer : Pointer (Option Provenance)) (size : Size) :
    (MemoryCopyMachine.genericHooks config addresses arithmetic).pointerAccess memory state pointer size =
      match sourcePointerAccess config arithmetic pointer size {state.machine with memory} with
      | .ok value machine => ⟨machine.memory, {state with machine}, .ok value⟩
      | .error error machine => ⟨machine.memory, ⟨machine, some error⟩, .error (reprStr error)⟩ := by
  unfold MemoryCopyMachine.genericHooks
  dsimp only
  unfold_internal ".MemoryCopyMachine.bridgeMemory"
  unfold_internal ".MemoryCopyMachine.access"
  unfold sourcePointerAccess sourceSignedAccess
  cases hs : sizeAsI64 size <;>
    simp only [hs, bind, EStateM.bind, pure, EStateM.pure]
  all_goals rfl'

theorem ptr_get_alloc_cached (addresses : GlobalAddressState) (id : AllocId)
    (tag : BorTag) (base offset : UInt64) (accessSize : Int64)
    (lookup : AddressLookupHooks) (arithmetic : PointerArithmetic)
    (width : arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : addresses.baseAddr.find? (fun entry => entry.allocId == id) =
      some ⟨id, base⟩) :
    addresses.ptrGetAlloc (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset)))
      accessSize lookup arithmetic = .ok (some (id, Size.ofBytes offset)) := by
  subst arithmetic
  unfold GlobalAddressState.ptrGetAlloc
  unfold_internal ".GlobalAddressState.findBase"
  simp only [Pointer.new, cached, Option.map_some, Bind.bind, Except.bind,
    Pure.pure, Except.pure, Size.ofBytes]
  have relative : base + offset - base = offset := by
    rw [UInt64.add_comm base offset, UInt64.add_sub_cancel]
  rw [relative]
  erw [DuplicatePrefix.PointerArithmetic.truncate_u64_identity]
  rfl

theorem typed_resolve_cached {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset : UInt64) (accessSize : Int)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (signedLower : -(2 ^ 63 : Int) ≤ accessSize)
    (signedUpper : accessSize < (2 ^ 63 : Int))
    (cached : machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) =
      some ⟨id, base⟩) :
    TypedMemoryProviders.resolvePointer pointers memory
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) accessSize machine =
      .ok (.ok ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩) machine := by
  unfold TypedMemoryProviders.resolvePointer
  have lowerFalse : (decide (accessSize < -(2 ^ 63 : Int))) = false := by simp; omega
  have upperFalse : (decide (accessSize ≥ (2 ^ 63 : Int))) = false := by simp; omega
  simp only [Pointer.new, lowerFalse, upperFalse, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure]
  erw [ptr_get_alloc_cached machine.user.addresses id tag base offset
    (Int64.ofInt accessSize) _ pointers.arithmetic width cached]
  rfl

theorem live_alloc_info {K Prov Extra : Type}
    (memory : MemoryState Prov Extra K) (id : AllocId)
    (entry : LocalAllocation Prov Extra K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    memory.getAllocInfo id = .ok
      ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩ := by
  unfold MemoryState.getAllocInfo
  rw [present]
  rfl

private theorem typed_resolve_count_cached {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset : UInt64) (count : Nat)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (signedFits : count < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩) :
    TypedMemoryProviders.resolvePointer pointers machine.memory
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (count : Int) machine =
      .ok (.ok ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩) machine := by
  exact typed_resolve_cached pointers machine.memory machine id tag base offset
    (count : Int) width (by omega) (by omega) cached

private theorem checked_live_dereference {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset : UInt64) (count : Nat)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (positiveNat : 0 < count) (signedFits : count < 9223372036854775808)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (bounds : offset.toNat + count ≤ entry.allocation.byteSize.bytes.toNat) :
    checkAndDerefPtr pointers.arithmetic
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base + offset)))
      (count : Int) .memoryAccess
      (fun _ _ => .ok ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩)
      machine.memory.getAllocInfo = .ok (some
        ⟨⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩,
          ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩⟩) := by
  exact DuplicatePrefix.PointerAccess.dereference_ok pointers.arithmetic
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base + offset))) count .memoryAccess
    (fun _ _ => .ok ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩)
    machine.memory.getAllocInfo ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩
    ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩
    positiveNat signedFits rfl (live_alloc_info machine.memory id entry present) (by simp) bounds

private theorem signed_stage_of_facts {K U : Type}
    (config : PlaceMachine.AccessConfig K U) (arithmetic : PointerArithmetic)
    (pointer : Pointer (Option Provenance)) (signed : Int)
    (machine : MachineHooks.MachineState K U) (resolved : ResolvedPointer ProvenanceExtra)
    (info : AllocationInfo)
    (nonzero : (signed == 0) = false)
    (resolution : config.resolvePointer machine.memory pointer signed machine = .ok (.ok resolved) machine)
    (checked : checkAndDerefPtr arithmetic pointer signed .memoryAccess
      (fun _ _ => .ok resolved) machine.memory.getAllocInfo = .ok (some ⟨resolved, info⟩)) :
    sourceSignedAccess config arithmetic pointer signed machine =
      .ok (some (resolved.allocId, resolved.offset, resolved.extra)) machine := by
  unfold sourceSignedAccess
  simp only [nonzero, Bool.false_eq_true, ↓reduceIte,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure]
  rw [resolution]
  dsimp only
  rw [checked]
  rfl

private theorem size_stage_of_facts {K U : Type}
    (config : PlaceMachine.AccessConfig K U) (arithmetic : PointerArithmetic)
    (pointer : Pointer (Option Provenance)) (size : Size) (signed : Int)
    (machine : MachineHooks.MachineState K U)
    (value : Option (AllocId × Size × ProvenanceExtra))
    (sizeFact : sizeAsI64 size = .ok signed)
    (action : sourceSignedAccess config arithmetic pointer signed machine = .ok value machine) :
    sourcePointerAccess config arithmetic pointer size machine = .ok value machine := by
  unfold sourcePointerAccess
  rw [sizeFact]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  exact action

/-- Full pointer-access stage of the real memory-copy hook. It preserves the
machine and derives successful signed-size, provenance, live-allocation and
range checks from concrete address-cache/heap facts. No memory-access callback
is supplied by the client: the resolver field is the canonical typed resolver.
-/
private theorem signed_pointer_access_cached {K U : Type} [DecidableEq K]
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset : UInt64) (count : Nat)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positiveNat : 0 < count) (signedFits : count < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (bounds : offset.toNat + count ≤ entry.allocation.byteSize.bytes.toNat) :
    sourceSignedAccess config pointers.arithmetic
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (count : Int) machine =
      .ok (some (id, Size.ofBytes offset, ProvenanceExtra.concrete tag)) machine := by
  have resolved := typed_resolve_count_cached pointers machine id tag base offset count width signedFits cached
  have checked := checked_live_dereference pointers machine id tag base offset count entry
    positiveNat signedFits present bounds
  have nonzero : ((count : Int) == 0) = false := by simp; omega
  exact signed_stage_of_facts config pointers.arithmetic
    (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (count : Int) machine
    ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩
    ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩
    nonzero (by simpa only [canonical] using resolved) checked

theorem source_pointer_access_cached {K U : Type} [DecidableEq K]
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset n : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n) (signedFits : n.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (bounds : offset.toNat + n.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    sourcePointerAccess config pointers.arithmetic
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Size.ofBytes n) machine =
      .ok (some (id, Size.ofBytes offset, ProvenanceExtra.concrete tag)) machine := by
  apply size_stage_of_facts config pointers.arithmetic
    (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Size.ofBytes n)
    (n.toNat : Int) machine (some (id, Size.ofBytes offset, ProvenanceExtra.concrete tag))
  · exact DuplicatePrefix.signed_size_ok (Size.ofBytes n) signedFits
  · exact signed_pointer_access_cached pointers config canonical machine id tag base offset n.toNat entry
      width (by simpa [UInt64.lt_iff_toNat_lt] using positive) signedFits cached present bounds

theorem copy_pointer_access_cached {K U : Type} [DecidableEq K]
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset n : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n) (signedFits : n.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (bounds : offset.toNat + n.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    (MemoryCopyMachine.genericHooks config PointerMachine.User.addresses pointers.arithmetic).pointerAccess
      machine.memory ⟨machine, none⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Size.ofBytes n) =
      ⟨machine.memory, ⟨machine, none⟩,
        .ok (some (id, Size.ofBytes offset, ProvenanceExtra.concrete tag))⟩ := by
  rw [pointer_access_source]
  erw [source_pointer_access_cached pointers config canonical machine id tag base offset n entry
    width positive signedFits cached present bounds]

theorem copy_probe_cached {K U : Type} [DecidableEq K]
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset n : UInt64)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩) :
    (MemoryCopyMachine.genericHooks config PointerMachine.User.addresses pointers.arithmetic).tryGetAllocId
      machine.memory ⟨machine, none⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) n = some id := by
  unfold MemoryCopyMachine.genericHooks
  dsimp only
  unfold_internal ".MemoryCopyMachine.probe"
  simp only [Pointer.new, bind, Option.bind]
  erw [ptr_get_alloc_cached machine.user.addresses id tag base offset (Int64.ofInt n.toNat)
    _ pointers.arithmetic width cached]
  rfl

theorem before_allocation_default {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U) (addresses : U → GlobalAddressState)
    (arithmetic : PointerArithmetic) (machine : MachineHooks.MachineState K U) (id : AllocId)
    (canonical : config.beforeAllocationAccess = fun _ => pure ()) :
    (MemoryCopyMachine.genericHooks config addresses arithmetic).beforeAllocationAccess
      machine.memory ⟨machine, none⟩ id = ⟨machine.memory, ⟨machine, none⟩, .ok ()⟩ := by
  unfold MemoryCopyMachine.genericHooks
  dsimp only
  unfold_internal ".MemoryCopyMachine.bridgeMemory"
  rw [canonical]
  rfl

private theorem memory_hook_unchanged {K U A : Type}
    (action : PlaceMachine.AccessState K U →
      MemoryStateHookResult Provenance Miri.TreeBorrows.BorrowTree K (PlaceMachine.AccessState K U) A)
    (state : MachineHooks.State K U) (value : A)
    (fact : action ⟨state.machine, none⟩ = ⟨state.machine.memory, ⟨state.machine, none⟩, .ok value⟩) :
    source_memory_hook action state = .ok value state := by
  unfold_internal ".GlobalMemoryCopyMachine.memoryHook"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  rw [fact]
  rfl

theorem copy_pointer_stage_cached {K U : Type} [DecidableEq K]
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (state : MachineHooks.State K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset n : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : 0 < n) (signedFits : n.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (bounds : offset.toNat + n.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    source_memory_hook (fun view =>
      (MemoryCopyMachine.genericHooks config PointerMachine.User.addresses pointers.arithmetic).pointerAccess
        view.machine.memory view
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Size.ofBytes n)) state =
      .ok (some (id, Size.ofBytes offset, ProvenanceExtra.concrete tag)) state := by
  apply memory_hook_unchanged
  exact copy_pointer_access_cached pointers config canonical state.machine id tag base offset n entry
    width positive signedFits cached present bounds

theorem before_allocation_stage_default {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U) (addresses : U → GlobalAddressState)
    (arithmetic : PointerArithmetic) (state : MachineHooks.State K U) (id : AllocId)
    (canonical : config.beforeAllocationAccess = fun _ => pure ()) :
    source_memory_hook (fun view =>
      (MemoryCopyMachine.genericHooks config addresses arithmetic).beforeAllocationAccess
        view.machine.memory view id) state = .ok () state := by
  apply memory_hook_unchanged
  exact before_allocation_default config addresses arithmetic state.machine id canonical

theorem race_access_without_clocks {K U : Type}
    (machine : MachineHooks.MachineState K U) (id : AllocId) (range : AllocRange)
    (writeType : Option Miri.Concurrency.NaWriteType) (readType : Miri.Concurrency.NaReadType)
    (disabled : machine.dataRace = none) :
    MachineHooks.memoryRaceAccess machine id range writeType readType = (machine, .ok ()) := by
  unfold MachineHooks.memoryRaceAccess
  rw [disabled]
  rfl

theorem weak_write_without_buffer {K U Payload : Type}
    (extras : MemoryExtras.Hooks K U Payload) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (range : AllocRange)
    (present : (extras.get machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩)) :
    MemoryExtras.nonAtomicWrite extras id range machine = .ok () machine := by
  unfold MemoryExtras.nonAtomicWrite MemoryExtras.lookup
  unfold_internal ".MemoryExtras.liftResult"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, present]

theorem sync_access_without_entries {K U Payload : Type}
    (extras : MemoryExtras.Hooks K U Payload) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (range : AllocRange) (write : Bool)
    (present : (extras.get machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩)) :
    MemoryExtras.syncAccess extras write id range machine = .ok () machine := by
  unfold MemoryExtras.syncAccess Miri.Concurrency.SyncObject.onMemoryAccess
    MemoryExtras.accessHooks MemoryExtras.lookup
  unfold_internal ".MemoryExtras.liftResult"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, present]
  simp [Array.qsort, bind, EStateM.bind, pure, EStateM.pure]

theorem get_raw_live {K Prov Extra S : Type} [DecidableEq K]
    (memory : MemoryState Prov Extra K) (state : S) (id : AllocId)
    (entry : LocalAllocation Prov Extra K) (kind : Option K)
    (globals : GlobalAllocationHooks Prov Extra K S)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    MemoryLifecycle.getAllocRaw memory state id kind globals =
      ⟨memory, globals.synchronizeMemory memory state, .ok entry.allocation⟩ := by
  unfold MemoryLifecycle.getAllocRaw
  rw [present]
  rfl

theorem get_raw_mut_live {K Prov Extra S : Type} [DecidableEq K]
    (memory : MemoryState Prov Extra K) (state : S) (id : AllocId)
    (entry : LocalAllocation Prov Extra K) (kind : Option K)
    (globals : GlobalAllocationHooks Prov Extra K S)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (mutable : entry.allocation.mutability = .Mut) :
    MemoryLifecycle.getAllocRawMut memory state id kind globals =
      ⟨memory, globals.synchronizeMemory memory state, .ok entry.allocation⟩ := by
  unfold MemoryLifecycle.getAllocRawMut
  rw [present]
  simp [mutable, bind, pure, Id.instMonad, Id.run]

theorem set_live_exact {K Prov Extra : Type} [DecidableEq K]
    (memory : MemoryState Prov Extra K) (id : AllocId)
    (entry : LocalAllocation Prov Extra K) (allocation : Allocation Prov Extra)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    memory.setLiveAllocation id allocation = .ok
      {memory with live := (memory.live.filter fun row => row.1 != id).push (id, {entry with allocation})} := by
  unfold MemoryState.setLiveAllocation
  unfold_internal ".MemoryState.findLive?"
  unfold_internal ".MemoryState.insertLive"
  simp [present, bind, Except.bind, pure, Except.pure]

theorem live_lookup_replaced {K Prov Extra : Type}
    (memory : MemoryState Prov Extra K) (id : AllocId)
    (entry : LocalAllocation Prov Extra K) :
    ((memory.live.filter fun row => row.1 != id).push (id, entry)).find?
      (fun row => row.1 == id) = some (id, entry) := by
  have noMatch : memory.live.find? (fun _ => false) = none := by
    simp [Array.find?_eq_none]
  simp [Array.find?_push, Array.find?_filter, noMatch]

theorem live_any_replaced {K Prov Extra : Type}
    (memory : MemoryState Prov Extra K) (id : AllocId)
    (entry : LocalAllocation Prov Extra K) :
    ((memory.live.filter fun row => row.1 != id).push (id, entry)).any
      (fun row => row.1 == id) = true := by
  simp

theorem live_any_of_present {K Prov Extra : Type}
    (memory : MemoryState Prov Extra K) (id : AllocId)
    (entry : LocalAllocation Prov Extra K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    memory.live.any (fun row => row.1 == id) = true := by
  apply Array.any_eq_true'.mpr
  exact ⟨(id, entry), Array.mem_of_find?_eq_some present, by simp⟩

theorem live_update_twice {K Prov Extra : Type}
    (memory : MemoryState Prov Extra K) (id : AllocId)
    (first second : LocalAllocation Prov Extra K) :
    let intermediate : MemoryState Prov Extra K := {memory with live := (memory.live.filter fun (row : AllocId × LocalAllocation Prov Extra K) => row.1 != id).push (id, first)}
    {intermediate with live := (intermediate.live.filter fun (row : AllocId × LocalAllocation Prov Extra K) => row.1 != id).push (id, second)} =
      {memory with live := (memory.live.filter fun (row : AllocId × LocalAllocation Prov Extra K) => row.1 != id).push (id, second)} := by
  dsimp only
  simp [Array.filter_push, Array.filter_filter]

theorem source_globals_synchronize {K U Payload : Type} [DecidableEq K]
    (prepared : Miri.Input.CompilerProviders.Prepared)
    (image : Miri.Input.AllocationImage.Imported)
    (extras : MemoryExtras.Hooks K U Payload) (leaves : GlobalAllocationMachine.Leaves K U)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (state : PlaceMachine.AccessState K U) :
    (Miri.Input.EvalGlobalAllocationMachine.make prepared image extras leaves).synchronizeMemory memory state =
      {state with machine := {state.machine with memory}} := by rfl

theorem snapshot_checks_plain {K U : Type}
    (config : PlaceMachine.AccessConfig K U)
    (allocation : Allocation Provenance Miri.TreeBorrows.BorrowTree)
    (n : UInt64) (state : MachineHooks.State K U)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (initialized : allocation.initializationMask = InitMask.new allocation.byteSize true)
    (provenance : allocation.provenanceMap = ProvenanceMap.new)
    (positive : 0 < n) (bounded : n ≤ allocation.byteSize.bytes) :
    source_snapshot_checks config allocation (allocRange Size.ZERO (Size.ofBytes n))
      (Size.ofBytes 8) state = .ok () state := by
  have full := DuplicatePrefix.AllocationCopy.full_bytes_ok allocation storage
  have prepared := DuplicatePrefix.AllocationCopy.empty_provenance_prepare (Prov := Provenance) n
    (DuplicatePrefix.AllocationCopy.snapshot allocation)
  have mask := DuplicatePrefix.AllocationCopy.initialized_prefix_prepare allocation.byteSize n positive bounded
  unfold_internal ".GlobalMemoryCopyMachine.snapshotChecks"
  rw [full]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [provenance]
  erw [prepared]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [initialized, mask]
  rfl

theorem source_raw_read_live {K U Payload : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U)
    (prepared : Miri.Input.CompilerProviders.Prepared)
    (image : Miri.Input.AllocationImage.Imported)
    (extras : MemoryExtras.Hooks K U Payload) (leaves : GlobalAllocationMachine.Leaves K U)
    (sourceGlobals : config.globalHooks =
      Miri.Input.EvalGlobalAllocationMachine.make prepared image extras leaves)
    (state : MachineHooks.State K U) (id : AllocId)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    source_global_raw config false id state = .ok entry.allocation state := by
  unfold_internal ".GlobalMemoryCopyMachine.raw"
  simp only [Bool.false_eq_true, ↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind]
  rw [get_raw_live state.machine.memory ⟨state.machine, none⟩ id entry
    config.globalKind config.globalHooks present]
  simp only [sourceGlobals, source_globals_synchronize]
  rfl

theorem source_raw_write_live {K U Payload : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U)
    (prepared : Miri.Input.CompilerProviders.Prepared)
    (image : Miri.Input.AllocationImage.Imported)
    (extras : MemoryExtras.Hooks K U Payload) (leaves : GlobalAllocationMachine.Leaves K U)
    (sourceGlobals : config.globalHooks =
      Miri.Input.EvalGlobalAllocationMachine.make prepared image extras leaves)
    (state : MachineHooks.State K U) (id : AllocId)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (mutable : entry.allocation.mutability = .Mut) :
    source_global_raw config true id state = .ok entry.allocation state := by
  unfold_internal ".GlobalMemoryCopyMachine.raw"
  simp only [↓reduceIte, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  rw [get_raw_mut_live state.machine.memory ⟨state.machine, none⟩ id entry
    config.globalKind config.globalHooks present mutable]
  simp only [sourceGlobals, source_globals_synchronize]
  rfl

/-- For the actual source access configuration, when vector clocks and
allocation-local synchronization metadata are absent, the only remaining
read/write failure is exactly the real Tree Borrows range failure. The
tracker remains enabled and its actual protector map is used. This is an
exact reduction for every tree, not a success premise for a callback. -/
theorem source_memory_access_reduces_to_tree {Os R P H D O Aff B Host : Type}
    (prepared : Miri.Input.CompilerProviders.Prepared)
    (image : Miri.Input.AllocationImage.Imported) (maximum : Size) (fuel : Nat)
    (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host)))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Miri.Input.EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host) P)
    (machine : MachineHooks.MachineState MiriMemoryKind
      (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (tree : Miri.TreeBorrows.BorrowTree)
    (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange) (write : Bool)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (present : (extras.get machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩)) :
    let config := Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras
    let result := PlaceMachine.memoryAccess config write ⟨machine, none⟩ tree id provenance range
    let access := tree.performBorrowAccessRange provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
    result.state.machine = machine ∧ result.extra = access.tree ∧
      (result.outcome = .ok () ↔ access.status = .Completed) := by
  dsimp only
  have diagnostic :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).diagnostic
        write id range machine = .ok () machine := by
    simp [Miri.Input.EvalAccessMachine.make,
      Miri.Input.EvalBackendMachine.access, Miri.Input.EvalBackendMachine.handler,
      noBackend, noClocks, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, pure, EStateM.pure, Except.pure, Except.bind]
  have weak :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).weakMemoryWrite =
        MemoryExtras.nonAtomicWrite extras := rfl
  have sync :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).syncAccess =
        MemoryExtras.syncAccess extras := rfl
  unfold PlaceMachine.memoryAccess
  unfold_internal ".PlaceMachine.bridge"
  simp only [diagnostic, weak, sync, pure, EStateM.pure, Id.run, bind, Id.instMonad]
  rw [race_access_without_clocks machine id range (if write then some .Write else none) .Read noClocks]
  simp only [tracked]
  cases write
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sync_access_without_entries extras machine id range false present]
    generalize hAccess : tree.performBorrowAccessRange provenance range.start range.size
      Miri.TreeBorrows.AccessKind.Read tracker.global.protectedTags .VisitChildrenOfAccessed = access
    by_cases completed : access.status = .Completed <;> simp [completed]
  · simp only [↓reduceIte]
    rw [weak_write_without_buffer extras machine id range present]
    simp only [tracked]
    rw [sync_access_without_entries extras machine id range true present]
    generalize hAccess : tree.performBorrowAccessRange provenance range.start range.size
      Miri.TreeBorrows.AccessKind.Write tracker.global.protectedTags .VisitChildrenOfAccessed = access
    by_cases completed : access.status = .Completed <;> simp [completed]

theorem source_memory_access_exact {Os R P H D O Aff B Host : Type}
    (prepared : Miri.Input.CompilerProviders.Prepared)
    (image : Miri.Input.AllocationImage.Imported) (maximum : Size) (fuel : Nat)
    (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host)))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Miri.Input.EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host) P)
    (machine : MachineHooks.MachineState MiriMemoryKind
      (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (tree : Miri.TreeBorrows.BorrowTree)
    (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange) (write : Bool)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (present : (extras.get machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩)) :
    let config := Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras
    let result := PlaceMachine.memoryAccess config write ⟨machine, none⟩ tree id provenance range
    let access := tree.performBorrowAccessRange provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
    result = if access.status = .Completed then
      ⟨⟨machine, none⟩, access.tree, .ok ()⟩
    else
      ⟨⟨machine, some (source_tree_error access.status)⟩, access.tree,
        .error (reprStr (source_tree_error access.status))⟩ := by
  dsimp only
  have diagnostic :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).diagnostic
        write id range machine = .ok () machine := by
    simp [Miri.Input.EvalAccessMachine.make,
      Miri.Input.EvalBackendMachine.access, Miri.Input.EvalBackendMachine.handler,
      noBackend, noClocks, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, pure, EStateM.pure, Except.pure, Except.bind]
  have weak :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).weakMemoryWrite =
        MemoryExtras.nonAtomicWrite extras := rfl
  have sync :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).syncAccess =
        MemoryExtras.syncAccess extras := rfl
  unfold PlaceMachine.memoryAccess
  unfold_internal ".PlaceMachine.bridge"
  simp only [diagnostic, weak, sync, pure, EStateM.pure, Id.run, bind, Id.instMonad]
  rw [race_access_without_clocks machine id range (if write then some .Write else none) .Read noClocks]
  simp only [tracked]
  cases write
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sync_access_without_entries extras machine id range false present]
    generalize hAccess : tree.performBorrowAccessRange provenance range.start range.size
      Miri.TreeBorrows.AccessKind.Read tracker.global.protectedTags .VisitChildrenOfAccessed = access
    by_cases completed : access.status = .Completed <;> simp [completed]

  · simp only [↓reduceIte]
    rw [weak_write_without_buffer extras machine id range present]
    simp only [tracked]
    rw [sync_access_without_entries extras machine id range true present]
    generalize hAccess : tree.performBorrowAccessRange provenance range.start range.size
      Miri.TreeBorrows.AccessKind.Write tracker.global.protectedTags .VisitChildrenOfAccessed = access
    by_cases completed : access.status = .Completed <;> simp [completed]

/-- Exact commit behavior of the actual global/local copy-access driver. Both
successful and failed Tree Borrows accesses commit their actual successor
tree to the live heap before returning the corresponding result. -/
theorem source_global_access_exact {Os R P H D O Aff B Host : Type}
    (prepared : Miri.Input.CompilerProviders.Prepared)
    (image : Miri.Input.AllocationImage.Imported) (maximum : Size) (fuel : Nat)
    (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host)))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Miri.Input.EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host) P)
    (state : MachineHooks.State MiriMemoryKind
      (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState)
    (allocation : Allocation Provenance Miri.TreeBorrows.BorrowTree)
    (kind : MemoryKind MiriMemoryKind) (id : AllocId) (provenance : ProvenanceExtra)
    (range : AllocRange) (write : Bool)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (tracked : state.machine.borrowTracker = some tracker)
    (present : (extras.get state.machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩)) :
    let config := Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras
    let access := allocation.extra.performBorrowAccessRange provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
    let updated := allocation.setExtra access.tree
    let memory := {state.machine.memory with live :=
      (state.machine.memory.live.filter fun row => row.1 != id).push (id, ⟨kind, updated⟩)}
    let after := {state with machine := {state.machine with memory}}
    source_global_access config write allocation id provenance range state =
      if access.status = .Completed then .ok updated after
      else .error (source_tree_error access.status) after := by
  have accessed := source_memory_access_exact prepared image maximum fuel globals pointers extras
    state.machine tracker allocation.extra id provenance range write noClocks noBackend tracked present
  dsimp only at accessed ⊢
  have retain :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).retainTouched =
        fun machine _ => machine := rfl
  unfold_internal ".GlobalMemoryCopyMachine.access"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  rw [accessed]
  have anyLive := live_any_of_present state.machine.memory id ⟨kind, allocation⟩ live
  generalize hAccess : allocation.extra.performBorrowAccessRange provenance range.start range.size
    (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed = access
  by_cases completed : access.status = .Completed
  · simp only [completed, ↓reduceIte]
    rw [anyLive, set_live_exact state.machine.memory id ⟨kind, allocation⟩
      (allocation.setExtra access.tree) live]
    simp only [retain, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    rfl
  · simp only [completed, ↓reduceIte]
    rw [anyLive, set_live_exact state.machine.memory id ⟨kind, allocation⟩
      (allocation.setExtra access.tree) live]
    simp only [retain, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    rfl

#print axioms ptr_get_alloc_cached
#print axioms typed_resolve_cached
#print axioms live_alloc_info
#print axioms copy_pointer_access_cached
#print axioms race_access_without_clocks
#print axioms weak_write_without_buffer
#print axioms sync_access_without_entries
#print axioms source_memory_access_reduces_to_tree
#print axioms source_memory_access_exact
#print axioms get_raw_live
#print axioms get_raw_mut_live
#print axioms set_live_exact
#print axioms live_lookup_replaced
#print axioms live_any_replaced
#print axioms source_globals_synchronize
#print axioms live_any_of_present
#print axioms snapshot_checks_plain
#print axioms source_raw_read_live
#print axioms source_raw_write_live
#print axioms source_global_access_exact
#print axioms copy_pointer_stage_cached
#print axioms copy_probe_cached
#print axioms before_allocation_default
#print axioms before_allocation_stage_default
#print axioms live_update_twice

end DuplicatePrefix.MemoryCopyBridge
