import empty_function.ProjectedAllocation
import empty_function.ProjectedScalar
import empty_function.ProjectedImage
namespace EmptyFunction.ProjectedOldWrite
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def access (s : Static) (maximum : Size) : PlaceMachine.AccessConfig MiriMemoryKind RootUser :=
  EvalAccessMachine.make s.prepared.compiler s.prepared.image maximum s.options.place.dynamicFuel
    (ConcreteProtection.source s).globals (ConcreteProtection.source s).pointers (ProjectedAllocation.extras s)

theorem access_source (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    s.cfg.access = access s metadata.construction.maximum := by
  obtain ⟨remaining,eq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have built := s.built
  rw [Configuration.rootConfig,eq,EvalConfigurationCore.make_eq_context,EvalConfigurationCore.makeWithForeignContext] at built
  simp (config := {zeta := false}) only [metadata.construction.maximum_eq,
    EvalConfigurationCore.pureQuery_eq,EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    metadata.construction.i32_eq,metadata.construction.bool_eq,metadata.construction.u8_eq,
    metadata.construction.unit_eq,metadata.construction.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  simp only [metadata.construction.maximum_eq,EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq,EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    metadata.construction.i32_eq,metadata.construction.bool_eq,metadata.construction.u8_eq,
    metadata.construction.unit_eq,metadata.construction.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  have same := Except.ok.inj built
  rw [←same]
  with_unfolding_all rfl

theorem diagnostic (s : Static) (maximum : Size) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : AllocId) (range : AllocRange)
    (backend : machine.user.payload.payload.user.backend = .none) (noClocks : machine.dataRace = none) :
    (access s maximum).diagnostic true id range machine = .ok () machine := by
  simp [access,EvalAccessMachine.make,EvalBackendMachine.access,EvalBackendMachine.handler,backend,noClocks,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure]

 theorem weak_write (s : Static) (maximum : Size) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : AllocId) (range : AllocRange)
    (extra : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun entry => entry.1 == id) =
      some (id,{weakMemory := none})) :
    (access s maximum).weakMemoryWrite id range machine = .ok () machine := by
  simp [access,EvalAccessMachine.make,EvalBackendMachine.access,ProjectedAllocation.extras,EvalCoreMachine.extras,
    MemoryExtras.nonAtomicWrite,MemoryExtras.lookup,extra,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  rfl

 theorem sync_write (s : Static) (maximum : Size) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : AllocId) (range : AllocRange)
    (extra : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun entry => entry.1 == id) =
      some (id,{weakMemory := none})) :
    (access s maximum).syncAccess true id range machine = .ok () machine := by
  simp [access,EvalAccessMachine.make,EvalBackendMachine.access,ProjectedAllocation.extras,EvalCoreMachine.extras,
    MemoryExtras.syncAccess,MemoryExtras.accessHooks,MemoryExtras.lookup,extra,Concurrency.SyncObject.onMemoryAccess,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  with_unfolding_all rfl

theorem before_write (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (id : AllocId) (tag : BorTag) (size : Size)
    (ghost : Bool) (backend : machine.user.payload.payload.user.backend = .none)
    (noClocks : machine.dataRace = none)
    (extra : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun entry => entry.1 == id) =
      some (id,{weakMemory := none})) :
    PlaceMachine.memoryAccess {s.cfg.access with ghostMode := ghost} true ⟨machine,none⟩
      (BorrowTree.new tag size) id (.concrete tag) (allocRange Size.ZERO size) =
      ⟨⟨machine,none⟩,BorrowTree.new tag size,.ok ()⟩ := by
  rw [access_source s metadata capacity]
  exact PlaceMachine.memoryAccess_fresh_write _ machine id tag size noClocks
    (diagnostic s metadata.construction.maximum machine id _ backend noClocks)
    (weak_write s metadata.construction.maximum machine id _ extra)
    (sync_write s metadata.construction.maximum machine id _ extra)

 theorem resolve (s : Static) (metadata : Metadata s) (maximum : Size)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (tag : BorTag) (base : UInt64) (amount : Int)
    (lower : -(2^63 : Int) ≤ amount) (upper : amount < 2^63)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) :
    (access s maximum).resolvePointer memory (Pointer.new (some (.concrete id tag)) (Size.ofBytes base)) amount machine =
      .ok (.ok ⟨id,Size.ZERO,.concrete tag⟩) machine := by
  have raw : machine.user.addresses.ptrGetAlloc
      (Pointer.new (.concrete id tag) (Size.ofBytes base)) (Int64.ofInt amount)
      { sizeOf := fun id => (memory.getAllocInfo id).toOption.map (·.size),
        isLive := fun id => some (memory.isAllocLive id) }
      (ConcreteProtection.source s).pointers.arithmetic = .ok (some (id,Size.ZERO)) := by
    unfold AllocAddresses.GlobalAddressState.ptrGetAlloc
    change (show Except AllocAddresses.AddressStateError (Option (AllocId × Size)) from do
      let some b := (machine.user.addresses.baseAddr.find? (fun (row : AllocAddresses.BaseAddressEntry) => row.allocId == id)).map AllocAddresses.BaseAddressEntry.address
        | throw (.missingBaseAddress id)
      let relative ← ((ConcreteProtection.source s).pointers.arithmetic.truncateToTargetUsize (base-b)).mapError AllocAddresses.AddressStateError.pointerArithmetic
      pure (some (id,Size.ofBytes relative))) = _
    simp [cached,ConcreteProtection.source_truncate s metadata.pointerSize,Except.mapError]
    with_unfolding_all rfl
  have pointerSource : (access s maximum).resolvePointer =
      TypedMemoryProviders.resolvePointer (ConcreteProtection.source s).pointers := by rfl
  rw [pointerSource]
  unfold TypedMemoryProviders.resolvePointer
  simp only [Pointer.new] at raw
  have notLower : ¬ amount < -(2^63 : Int) := by omega
  have notUpper : ¬ amount ≥ (2^63 : Int) := by omega
  change ¬ amount < -9223372036854775808 at notLower
  change ¬ 9223372036854775808 ≤ amount at notUpper
  simp [Pointer.new,notLower,notUpper,raw,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

theorem full_bounds (target : PointerArithmetic) (id : AllocId) (size : Size)
    (signed : size.bytes.toNat < 2^63) :
    checkedBounds target id size Size.ZERO (Int.ofNat size.bytes.toNat) .memoryAccess = .ok () := by
  have signedNat : size.bytes.toNat < 9223372036854775808 := by simpa using signed
  have lower : (-9223372036854775808 : Int) ≤ (size.bytes.toNat : Int) := by omega
  have upper : (size.bytes.toNat : Int) < 9223372036854775808 := by omega
  unfold checkedBounds
  with_unfolding_all change
    (if !(decide ((-9223372036854775808 : Int) ≤ (size.bytes.toNat : Int)) &&
      decide ((size.bytes.toNat : Int) < 9223372036854775808)) then _ else _) = Except.ok ()
  simp [lower,upper,Size.ZERO,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem allocation_access (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (id : AllocId) (tag : BorTag)
    (size : Size) (base : UInt64) (entry : InputDraft.Entry)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : entry.allocation.extra = BorrowTree.new tag size)
    (storage : entry.allocation.byteSize = size) (mutable : entry.allocation.mutability = .Mut)
    (positive : size.bytes ≠ 0) (signed : size.bytes.toNat < 2^63)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (last : (machine.memory.live.filter (fun row => row.1 != id)).push (id,entry) = machine.memory.live)
    (backend : machine.user.payload.payload.user.backend = .none) (noClocks : machine.dataRace = none)
    (extra : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id,{weakMemory := none})) :
    AllocationAccess.getPtrAllocMut machine.memory (⟨machine,none⟩ : PlaceMachine.AccessState MiriMemoryKind RootUser)
      ⟨s.prepared.compiler.runtime.target.pointerSize⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes base)) size false s.cfg.access.globalKind
      s.cfg.access.globalHooks (PlaceMachine.accessHooks s.cfg.access) =
      ⟨machine.memory,⟨machine,none⟩,some ⟨id,allocRange Size.ZERO size,entry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO size,entry.allocation⟩)⟩ := by
  let ptr : Pointer (Option Provenance) := Pointer.new (some (.concrete id tag)) (Size.ofBytes base)
  have signedNat : size.bytes.toNat < 9223372036854775808 := by simpa using signed
  have amountLower : -(2^63 : Int) ≤ (size.bytes.toNat : Int) := by change -9223372036854775808 ≤ (size.bytes.toNat : Int); omega
  have amountUpper : (size.bytes.toNat : Int) < (2^63 : Int) := by change (size.bytes.toNat : Int) < 9223372036854775808; omega
  have resolved := resolve s metadata metadata.construction.maximum machine machine.memory id tag base
    (Int.ofNat size.bytes.toNat) amountLower amountUpper cached
  rw [←access_source s metadata capacity] at resolved
  have resolveHook : (PlaceMachine.accessHooks s.cfg.access).resolvePointer machine.memory
      ⟨machine,none⟩ ptr (Int.ofNat size.bytes.toNat) =
      ⟨⟨machine,none⟩,.ok (.ok ⟨id,Size.ZERO,.concrete tag⟩)⟩ := by
    exact PlaceMachine.resolvePointer_ok s.cfg.access machine.memory machine ptr (Int.ofNat size.bytes.toNat) _ resolved
  have beforeHook : (PlaceMachine.accessHooks s.cfg.access).beforeAllocationAccess ⟨machine,none⟩ id =
      ⟨⟨machine,none⟩,.ok ()⟩ := by
    rw [access_source s metadata capacity]
    with_unfolding_all rfl
  have writeHook : (PlaceMachine.accessHooks s.cfg.access).beforeMemoryWrite ⟨machine,none⟩
      entry.allocation.extra ptr id (.concrete tag) (allocRange Size.ZERO size) =
      ⟨⟨machine,none⟩,entry.allocation.extra,.ok ()⟩ := by
    change PlaceMachine.memoryAccess s.cfg.access true ⟨machine,none⟩ entry.allocation.extra id (.concrete tag) _ = _
    rw [tree]
    have written := before_write s metadata capacity machine id tag size s.cfg.access.ghostMode backend noClocks extra
    simpa only [] using written
  have sync : s.cfg.access.globalHooks.synchronizeMemory machine.memory ⟨machine,none⟩ = ⟨machine,none⟩ := by
    rw [access_source s metadata capacity]
    change (ConcreteProtection.source s).globals.synchronizeMemory machine.memory ⟨machine,none⟩ = _
    rw [(ConcreteProtection.bindings s metadata capacity).2.2]
  apply AllocationAccess.live_mut_of_edges machine.memory (⟨machine,none⟩ : PlaceMachine.AccessState MiriMemoryKind RootUser)
    _ ptr size _ _ _ id entry (.concrete tag) (Int.ofNat size.bytes.toNat)
    (by simp [sizeAsI64,signedNat])
    (by intro h; have hn : size.bytes.toNat = 0 := by simpa using h
        exact positive (UInt64.toNat_inj.mp hn)) resolveHook live mutable sync
    (by rw [storage]; exact full_bounds _ id size signed) beforeHook writeHook last

theorem get_place (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (id : AllocId) (tag : BorTag)
    (layout : LocalLayout) (base : UInt64) (entry : InputDraft.Entry)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : entry.allocation.extra = BorrowTree.new tag layout.layout.size)
    (storage : entry.allocation.byteSize = layout.layout.size) (mutable : entry.allocation.mutability = .Mut)
    (sized : layout.layout.isSized = true) (positive : layout.layout.size.bytes ≠ 0)
    (signed : layout.layout.size.bytes.toNat < 2^63)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (last : (machine.memory.live.filter (fun row => row.1 != id)).push (id,entry) = machine.memory.live)
    (backend : machine.user.payload.payload.user.backend = .none) (noClocks : machine.dataRace = none)
    (extra : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id,{weakMemory := none})) :
    getPlaceAllocMut machine.memory (⟨machine,none⟩ : PlaceMachine.AccessState MiriMemoryKind RootUser)
      ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,localMemoryLayout layout⟩
      s.cfg.access.runtime false s.cfg.access.globalKind s.cfg.access.globalHooks
      (PlaceMachine.accessHooks s.cfg.access) s.cfg.access.dynamicLayout =
      ⟨machine.memory,⟨machine,none⟩,some ⟨id,allocRange Size.ZERO layout.layout.size,entry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO layout.layout.size,entry.allocation⟩)⟩ := by
  have notUnsized : layout.layout.backendRepr.isUnsized = false := by
    have h : !layout.layout.backendRepr.isUnsized = true := sized
    cases casesEq : layout.layout.backendRepr.isUnsized <;> simp_all
  have pointer : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace =
      .ok s.prepared.compiler.runtime.target.pointerSize := by
    rw [(MetadataBinding.fields s metadata capacity).runtime]
    simp [RuntimeTargetDataLayout.pointerSizeIn,RuntimeTargetDataLayout.pointerSpecIn,
      RuntimeTargetDataLayout.pointerSize,Except.pure]
    rfl
  exact getPlaceAllocMut_sized_of_access machine.memory (⟨machine,none⟩ : PlaceMachine.AccessState MiriMemoryKind RootUser)
    _ s.cfg.access.runtime _ _ _ _ _ _ notUnsized rfl pointer
    (allocation_access s metadata capacity machine id tag layout.layout.size base entry live tree storage mutable
      positive signed cached last backend noClocks extra)

end EmptyFunction.ProjectedOldWrite
