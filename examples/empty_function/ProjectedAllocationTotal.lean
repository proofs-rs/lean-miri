import empty_function.AllocatorActive
import empty_function.ProjectedReserveTotal
import empty_function.ProjectedCreate
import empty_function.StackAddressPartial
import empty_function.GeneratedGeometry
namespace EmptyFunction.ProjectedAllocationTotal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Successful root lookup, including a cached root at exhausted tag supply,
suffices for actual fresh-extra initialization. Numeric room is not assumed. -/
theorem init_extra_of_root (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker) (id : AllocId) (size : Size) (align : Align)
    (global : GlobalState) (tag : BorTag) (root : tracker.global.rootPointerTag id = .ok (global,tag))
    (backend : machine.user.payload.payload.user.backend = .none) (noRace : machine.dataRace = none)
    (vacant : machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false) :
    PlaceMachine.initStackExtra s.cfg.allocation.allocationTail id size align machine =
      .ok (BorrowTree.new tag size)
        (MemoryExtras.putAllocation (ProjectedAllocation.extras s)
          {machine with borrowTracker := some {tracker with global}} id {weakMemory := none}) := by
  have done := ProjectedAllocation.tail s metadata capacity {machine with borrowTracker := some {tracker with global}}
    id size align backend noRace vacant
  simp only [noRace] at done
  unfold PlaceMachine.initStackExtra
  simp [enabled,root,noRace,done,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    pure,Pure.pure,EStateM.pure,set,MonadStateOf.set,EStateM.set]

theorem root_error (s : Static) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (size : Size) (align : Align) (error : GlobalStateError)
    (root : tracker.global.rootPointerTag id = .error error) :
    PlaceMachine.initStackExtra s.cfg.allocation.allocationTail id size align machine =
      .error (.resourceExhaustion s!"allocation root tag: {repr error}") machine := by
  unfold PlaceMachine.initStackExtra
  simp [enabled,root,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    pure,Pure.pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

/-- Reservation failures are propagated after recording the real allocator
state. No root/address callback, old-value write or slot update then executes. -/
theorem reserve_error (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : State) (size : Size) (align : Align) (bytes : Allocation Provenance Unit)
    (storage : Allocation.tryNew (Prov := Provenance) size align .Uninit
      (fun size _ => some (Array.replicate size.bytesNat 0)) = .ok bytes)
    (sizeBound : bytes.byteSize.bytes ≤ s.cfg.allocation.maximumObjectSize.bytes)
    (notNative : bytes.nativeBuffer = none)
    (reserved : MemoryState Provenance BorrowTree MiriMemoryKind) (error : AllocationIdError)
    (reserve : state.machine.memory.reserveAllocId = (reserved,.error error)) :
    PlaceMachine.allocateStackRaw s.cfg.allocation size align state =
      .error (.resourceExhaustion s!"stack allocation ID: {repr error}")
        {state with machine := {state.machine with memory := reserved}} := by
  have native := ProjectedAllocation.native_storage s metadata capacity size align state
  have noOverflow : ¬s.cfg.allocation.maximumObjectSize.bytes < bytes.byteSize.bytes := UInt64.not_lt.mpr sizeBound
  unfold PlaceMachine.allocateStackRaw
  rw [ProjectedAllocation.native_binding s metadata capacity]
  simp [bind,Bind.bind,EStateM.bind,native,storage,pure,Pure.pure,EStateM.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch,noOverflow,get,getThe,
    MonadStateOf.get,EStateM.get,set,MonadStateOf.set,EStateM.set,reserve,notNative,
    throw,throwThe,MonadExceptOf.throw,EStateM.throw,EStateM.nonBacktrackable,EStateM.dummySave,EStateM.dummyRestore]

  rfl
/-- Typed root/initialization failures preserve the failed machine after the
successful ID reservation; the caller stack is retained. -/
theorem init_error (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : State) (size : Size) (align : Align) (bytes : Allocation Provenance Unit)
    (storage : Allocation.tryNew (Prov := Provenance) size align .Uninit
      (fun size _ => some (Array.replicate size.bytesNat 0)) = .ok bytes)
    (sizeBound : bytes.byteSize.bytes ≤ s.cfg.allocation.maximumObjectSize.bytes)
    (notNative : bytes.nativeBuffer = none)
    (reserved : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId)
    (reserve : state.machine.memory.reserveAllocId = (reserved,.ok id))
    (error : StepError) (failed : MachineHooks.MachineState MiriMemoryKind RootUser)
    (root : PlaceMachine.initStackExtra s.cfg.allocation.allocationTail id size align
      {state.machine with memory := reserved} = .error error failed) :
    PlaceMachine.allocateStackRaw s.cfg.allocation size align state =
      .error error {state with machine := failed} := by
  have noOverflow : ¬s.cfg.allocation.maximumObjectSize.bytes < bytes.byteSize.bytes := UInt64.not_lt.mpr sizeBound
  unfold PlaceMachine.allocateStackRaw
  rw [ProjectedAllocation.native_binding s metadata capacity]
  simp only [bind,Bind.bind,EStateM.bind,storage,pure,Pure.pure,EStateM.pure]
  simp only [tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch]
  simp only [noOverflow,↓reduceIte,get,getThe,MonadStateOf.get,EStateM.get,set,MonadStateOf.set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,reserve]
  rw [ProjectedAllocation.initialize_stack s metadata capacity]
  simp [root,notNative,get,getThe,MonadStateOf.get,EStateM.get,set,MonadStateOf.set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    throw,throwThe,MonadExceptOf.throw,EStateM.throw,EStateM.nonBacktrackable,EStateM.dummySave,EStateM.dummyRestore]
  rfl

theorem typed_error (s : Static) (layout : LocalLayout) (state failed : State) (error : StepError)
    (sized : layout.layout.isSized = true)
    (raw : PlaceMachine.allocateStackRaw s.cfg.allocation layout.layout.size layout.layout.align.abi state =
      .error error failed) :
    PlaceMachine.allocateStack s.cfg.allocation layout state = .error error failed := by
  simp [PlaceMachine.allocateStack,sized,raw,bind,Bind.bind,EStateM.bind]

structure Allocated (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (before : State) where
  reserved : MemoryState Provenance BorrowTree MiriMemoryKind
  id : AllocId
  global : GlobalState
  tag : BorTag
  bytes : Allocation Provenance Unit
  base : UInt64
  tape : ExecutionChoices.Tape
  addresses : AllocAddresses.GlobalAddressState
  after : State
  reservation : p.before.machine.memory.reserveAllocId = (reserved,.ok id)
  root : input.tracker.global.rootPointerTag id = .ok (global,tag)
  storage : Allocation.tryNew destination.baseLayout.layout.size destination.baseLayout.layout.align.abi .Uninit
    (fun n _ => some (Array.replicate n.bytesNat 0)) = .ok bytes
  size : bytes.byteSize = destination.baseLayout.layout.size
  alignment : bytes.align = destination.baseLayout.layout.align.abi
  native : bytes.nativeBuffer = none
  mutable : bytes.mutability = .Mut
  registry : reserved.live = p.before.machine.memory.live
  fresh : reserved.live.find? (fun row => row.1 == id) = none
  afterEq : after = ProjectedAddress.assigned
    (ChoiceProjection.tapeAccess.put
      (ProjectedCreate.registered s before reserved input.tracker global id bytes tag destination.baseLayout.layout.size) tape) addresses
  allocated : PlaceMachine.allocateStack s.cfg.allocation destination.baseLayout before =
    .ok ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,destination.baseLayout⟩ after
  cached : addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  extent : base.toNat + destination.baseLayout.layout.size.bytes.toNat < 2^64

theorem allocate (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (needed : InputDraft.NeedsEnclosingAllocation p)
    (state : State) (memory : state.machine.memory = p.before.machine.memory)
    (addresses : state.machine.user.addresses = p.before.machine.user.addresses)
    (tracked : state.machine.borrowTracker = some input.tracker)
    (backend : state.machine.user.payload.payload.user.backend = .none) (noRace : state.machine.dataRace = none)
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations =
      p.before.machine.user.payload.payload.user.runtime.extras.allocations) :
    (∃ error failed, PlaceMachine.allocateStack s.cfg.allocation destination.baseLayout state =
      .error error failed ∧ RunLoop.reportsUB error = false) ∨
    Nonempty (Allocated s p input destination state) := by
  have alignment := metadata.compilerLayoutAlignment destination.metadata.normalizedTy destination.baseLayout destination.metadata.lookup
  obtain ⟨bytes,created,sizeEq,lengthEq,notNative,mutable,alignEq⟩ :=
    ProjectedImage.create_uninit_full destination.baseLayout.layout.size destination.baseLayout.layout.align.abi alignment
  have maximumEq : s.cfg.allocation.maximumObjectSize = Size.ofBytes 9223372036854775807 := by
    rw [ProjectedAllocation.source s metadata capacity]
    exact ProjectedAllocation.maximum s metadata
  have byteBound : bytes.byteSize.bytes ≤ s.cfg.allocation.maximumObjectSize.bytes := by
    rw [sizeEq,maximumEq,UInt64.le_iff_toNat_le]
    have signed := destination.baseSigned
    change destination.baseLayout.layout.size.bytes.toNat ≤ 9223372036854775807
    omega
  rcases ProjectedReserveTotal.total s p input needed with failed | success
  · obtain ⟨reserved,error,reserveEq⟩ := failed
    have current : state.machine.memory.reserveAllocId = (reserved,.error error) := by rw [memory];exact reserveEq
    have raw := reserve_error s metadata capacity state destination.baseLayout.layout.size destination.baseLayout.layout.align.abi
      bytes created byteBound notNative reserved error current
    exact Or.inl ⟨_,_,typed_error s _ _ _ _ destination.baseSized raw,rfl⟩
  · obtain ⟨reserved,id,reserveEq,idEq,sameLive,vacantExtras,missing,missingLive⟩ := success
    have current : state.machine.memory.reserveAllocId = (reserved,.ok id) := by rw [memory];exact reserveEq
    have vacant : state.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false := by
      rw [extras];exact vacantExtras
    cases rootEq : input.tracker.global.rootPointerTag id with
    | error error =>
      have bad := root_error s {state.machine with memory := reserved} input.tracker tracked id
        destination.baseLayout.layout.size destination.baseLayout.layout.align.abi error rootEq
      have raw := init_error s metadata capacity state destination.baseLayout.layout.size destination.baseLayout.layout.align.abi
        bytes created byteBound notNative reserved id current _ _ bad
      exact Or.inl ⟨_,_,typed_error s _ _ _ _ destination.baseSized raw,rfl⟩
    | ok value =>
      obtain ⟨global,tag⟩ := value
      have rootFacts := RootTagPost.root input.tracker.global id global tag rootEq
      have initializedEq := init_extra_of_root s metadata capacity {state.machine with memory := reserved} input.tracker tracked
        id destination.baseLayout.layout.size destination.baseLayout.layout.align.abi global tag rootEq backend noRace vacant
      let initial := MemoryExtras.putAllocation (ProjectedAllocation.extras s)
        {{state.machine with memory := reserved} with borrowTracker := some {input.tracker with global}} id {weakMemory := none}
      let liveState := ProjectedCreate.registered s state reserved input.tracker global id bytes tag destination.baseLayout.layout.size
      have registeredLive : liveState.machine.memory.live.find? (fun row => row.1 == id) =
          some (id,⟨.stack,bytes.withExtra (BorrowTree.new tag destination.baseLayout.layout.size)⟩) := by
        change (reserved.live.push _).find? _ = _
        simp [Array.find?_push,sameLive,missingLive]
      let info : AllocationInfo := ⟨destination.baseLayout.layout.size,destination.baseLayout.layout.align.abi,.liveData,.Mut⟩
      have infoEq : liveState.machine.memory.getAllocInfo id = .ok info := by
        simp only [MemoryState.getAllocInfo,registeredLive,pure,Pure.pure,Except.pure]
        change Except.ok (⟨bytes.byteSize,bytes.align,.liveData,bytes.mutability⟩ : AllocationInfo) = _
        rw [sizeEq,alignEq,mutable]
      have isLive : liveState.machine.memory.isAllocLive id = true := by
        simp [MemoryState.isAllocLive,liveState,ProjectedCreate.registered,MemoryExtras.putAllocation,ProjectedAllocation.extras,
          EvalCoreMachine.extras,Array.any_push]
      have addrEq : liveState.machine.user.addresses = p.before.machine.user.addresses := addresses
      obtain ⟨generation,representation⟩ := input.projectedGeneration needed (AllocatorActive.of_success _ _ _ reserveEq)
      have addressTotal := StackAddressPartial.stack (ConcreteProtection.source s).pointers liveState id info generation
        (by rw [addrEq];exact missing) infoEq rfl isLive (by rw [addrEq];exact representation.managed)
        (by rw [addrEq];exact representation.current) (by rfl)
      have allocationPrefix := ProjectedAllocation.raw_prefix s metadata capacity state destination.baseLayout.layout.size
        destination.baseLayout.layout.align.abi bytes created byteBound notNative reserved id current
        (BorrowTree.new tag destination.baseLayout.layout.size) initial initializedEq
        {input.tracker with global} tag rfl rootFacts.1
      change PlaceMachine.allocateStackRaw s.cfg.allocation _ _ state =
        ((do let pointer ← s.cfg.allocation.adjustRootAddress id tag;pure pointer.withOptionalProvenance) :
          MachineHooks.M MiriMemoryKind RootUser (Pointer (Option Provenance))) liveState at allocationPrefix
      have adjust := ProjectedAllocation.adjust_source s metadata capacity liveState id tag
        (bytes.withExtra (BorrowTree.new tag destination.baseLayout.layout.size)) registeredLive
      change s.cfg.allocation.adjustRootAddress id tag liveState = _ at adjust
      rcases addressTotal with good | bad
      · obtain ⟨base,tape,finalAddresses,slack,addressEq,cached,generated⟩ := good
        change ExecutionAddressChoices.addrFromAllocId EvalCoreMachine.tape (ConcreteProtection.source s).pointers id (some .stack) liveState = _ at addressEq
        have numeric := GeneratedGeometry.outcome generation.generator info.size info.align slack base generated
        have finite := UInt64.toNat_lt (generation.generator.generate info.size info.align slack).state.nextBaseAddr
        rw [numeric.2.1] at finite
        have extent : base.toNat + destination.baseLayout.layout.size.bytes.toNat < 2^64 := by
          change base.toNat + max destination.baseLayout.layout.size.bytes.toNat 1 < 2^64 at finite
          omega
        simp only [bind,Bind.bind,EStateM.bind] at adjust
        rw [addressEq] at adjust
        simp only [bind,Bind.bind,EStateM.bind] at allocationPrefix
        rw [adjust] at allocationPrefix
        let after := ProjectedAddress.assigned (ChoiceProjection.tapeAccess.put liveState tape) finalAddresses
        have allocated : PlaceMachine.allocateStack s.cfg.allocation destination.baseLayout state =
            .ok ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,destination.baseLayout⟩ after := by
          unfold PlaceMachine.allocateStack
          simp only [destination.baseSized,Bool.not_true,Bool.false_eq_true,↓reduceIte,
            bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,allocationPrefix]
          rfl
        exact Or.inr ⟨⟨reserved,id,global,tag,bytes,base,tape,finalAddresses,after,reserveEq,rootEq,created,sizeEq,
          alignEq,notNative,mutable,sameLive,(by simpa only [sameLive] using missingLive),rfl,allocated,cached,extent⟩⟩
      · obtain ⟨error,failed,addressEq,safe⟩ := bad
        change ExecutionAddressChoices.addrFromAllocId EvalCoreMachine.tape (ConcreteProtection.source s).pointers id (some .stack) liveState = _ at addressEq
        simp only [bind,Bind.bind,EStateM.bind] at adjust
        rw [addressEq] at adjust
        simp only [bind,Bind.bind,EStateM.bind] at allocationPrefix
        rw [adjust] at allocationPrefix
        exact Or.inl ⟨error,failed,typed_error s _ _ _ _ destination.baseSized allocationPrefix,safe⟩

end EmptyFunction.ProjectedAllocationTotal
