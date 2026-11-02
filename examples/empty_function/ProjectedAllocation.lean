import empty_function.ConcreteProtection
import empty_function.RootTagPost

namespace EmptyFunction.ProjectedAllocation
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def extras (s : Static) := EvalCoreMachine.extras
  (Configuration.leaves s.prepared s.options.place.debugAssertions).sync ConcurrencyErrors.storeBuffer

def allocation (s : Static) (maximum : Size) : PlaceMachine.AllocationConfig MiriMemoryKind RootUser :=
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  let base := EvalConfiguration.allocation maximum leaves.storage (fun _ _ _ => pure ())
    (ConcreteProtection.source s).pointers (extras s)
  {base with
    nativeStorage := some (fun size align init => do
      let _ : WholeCall.State ← get
      pure (Allocation.tryNew (Prov := Provenance) size align init leaves.storage))
    nativeDrop := none}

 theorem source (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    s.cfg.allocation = allocation s metadata.construction.maximum := by
  obtain ⟨remaining,eq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have built := s.built
  rw [Configuration.rootConfig,eq,EvalConfigurationCore.make_eq_context,EvalConfigurationCore.makeWithForeignContext] at built
  simp (config := {zeta := false}) only [metadata.construction.maximum_eq,
    EvalConfigurationCore.pureQuery_eq,EvalConfigurationCore.liftConstruction_eq,
    EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    metadata.construction.i32_eq,metadata.construction.bool_eq,metadata.construction.u8_eq,
    metadata.construction.unit_eq,CompilerProviders.Prepared.rootSpan_eq,metadata.construction.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  simp only [metadata.construction.maximum_eq,EvalConfigurationCore.pureQuery_eq,
    EvalConfigurationCore.liftConstruction_eq,EvalMathMachine.hooks,CompilerCallConstruction.helpers,
    metadata.construction.i32_eq,metadata.construction.bool_eq,metadata.construction.u8_eq,
    metadata.construction.unit_eq,CompilerProviders.Prepared.rootSpan_eq,metadata.construction.rootSpan_eq,
    Except.mapError,Except.map,bind,Except.bind,pure,Except.pure] at built
  have same := Except.ok.inj built
  rw [←same]
  with_unfolding_all rfl

 theorem maximum (s : Static) (metadata : Metadata s) :
    metadata.construction.maximum = Size.ofBytes 9223372036854775807 := by
  have query := metadata.construction.maximum_eq
  simp [CompilerExecutionBounds.maximum,metadata.pointerSize,PointerArithmetic.maxSizeOfVal,
    Except.mapError] at query
  exact (Except.ok.inj query).symm

 theorem tail (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : AllocId) (size : Size) (align : Align)
    (backend : machine.user.payload.payload.user.backend = .none)
    (noRace : machine.dataRace = none)
    (vacant : machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false) :
    s.cfg.allocation.allocationTail id size align machine =
      .ok () (MemoryExtras.putAllocation (extras s) machine id ⟨none,#[]⟩) := by
  have absent : ¬ ∃ (index : Nat) (valid : index < machine.user.payload.payload.user.runtime.extras.allocations.size),
      (machine.user.payload.payload.user.runtime.extras.allocations[index]'valid).1 = id := by
    rintro ⟨index,valid,equal⟩
    have noMatch := Array.any_eq_false.mp vacant index valid
    simp [equal] at noMatch
  rw [source s metadata capacity]
  unfold allocation EvalConfiguration.allocation
  simp only
  simp [EvalBackendMachine.handler,backend,noRace,MemoryExtras.initAllocation,extras,EvalCoreMachine.extras,
    vacant,absent,MemoryExtras.putAllocation,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    pure,Pure.pure,EStateM.pure,set,MonadStateOf.set,EStateM.set,Except.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch]

 theorem root_ready (global : GlobalState) (id : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615) :
    ∃ after tag, global.rootPointerTag id = .ok (after,tag) := by
  cases cached : global.rootTag? id with
  | some tag => exact ⟨global,tag,by simp [GlobalState.rootPointerTag,cached,pure,Except.pure]⟩
  | none =>
    have created := UnitRetag.allocate_tag global room
    refine ⟨{global with
      nextPointerTag := UnitRetag.successorTag global.nextPointerTag room
      rootPointerTags := global.rootPointerTags.push (id,global.nextPointerTag)},global.nextPointerTag,?_⟩
    simp [GlobalState.rootPointerTag,cached,created,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

 theorem init_extra (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker) (id : AllocId) (size : Size) (align : Align)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (backend : machine.user.payload.payload.user.backend = .none) (noRace : machine.dataRace = none)
    (vacant : machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false) :
    ∃ global tag, tracker.global.rootPointerTag id = .ok (global,tag) ∧
      PlaceMachine.initStackExtra s.cfg.allocation.allocationTail id size align machine =
        .ok (BorrowTree.new tag size)
          (MemoryExtras.putAllocation (extras s) {machine with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩) ∧
      global.rootTag? id = some tag ∧ global.protectedTags = tracker.global.protectedTags ∧
      (∀ other old, tracker.global.rootTag? other = some old → global.rootTag? other = some old) := by
  obtain ⟨global,tag,rootEq⟩ := root_ready tracker.global id room
  have facts := RootTagPost.root tracker.global id global tag rootEq
  have done := tail s metadata capacity {machine with borrowTracker := some {tracker with global}}
    id size align backend noRace vacant
  refine ⟨global,tag,rootEq,?_,facts.1,facts.2.2.1,facts.2.1⟩
  simp only [noRace] at done
  unfold PlaceMachine.initStackExtra
  simp [enabled,rootEq,noRace,done,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    pure,Pure.pure,EStateM.pure,set,MonadStateOf.set,EStateM.set]

 theorem extras_fresh (s : Static) (p : Packet) (representation : InputDraft.AllocatorRepresentation p.before)
    (nonzero : p.before.machine.memory.nextAllocId ≠ 0) :
    p.before.machine.user.payload.payload.user.runtime.extras.allocations.any
      (fun row => row.1 == (⟨p.before.machine.memory.nextAllocId,nonzero⟩ : AllocId)) = false := by
  apply Array.any_eq_false.mpr
  intro index valid found
  have member := Array.getElem_mem valid
  have issued := representation.extrasIssued _ member
  have below := representation.issued _ issued
  have equal := beq_iff_eq.mp found
  rw [equal] at below
  exact Nat.lt_irrefl _ below

 theorem native_binding (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity) :
    s.cfg.allocation.nativeStorage = some (fun size align init =>
      pure (Allocation.tryNew (Prov := Provenance) size align init
        (fun size _ => some (Array.replicate size.bytesNat 0)))) := by
  rw [source s metadata capacity]
  apply congrArg Option.some
  funext size align init state
  simp [allocation,Configuration.leaves,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

 theorem native_storage (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (size : Size) (align : Align) (state : WholeCall.State) :
    (match s.cfg.allocation.nativeStorage with
      | some create => create size align .Uninit
      | none => pure (Allocation.tryNew (Prov := Provenance) size align .Uninit s.cfg.allocation.zeroedStorage)) state =
      .ok (Allocation.tryNew (Prov := Provenance) size align .Uninit
        (fun size _ => some (Array.replicate size.bytesNat 0))) state := by
  rw [source s metadata capacity]
  simp [allocation,Configuration.leaves,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

 theorem diagnostic (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (id : AllocId) (size : Size) (align : Align) :
    s.cfg.allocation.diagnostic id size align = pure () := by
  rw [source s metadata capacity]
  rfl

/-- Internal operation composition through registration. The storage,
reservation and root equations are derived from current raw resources before
this is used by a client theorem. Address assignment remains the actual call. -/
 theorem raw_prefix (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : WholeCall.State) (size : Size) (align : Align) (bytes : Allocation Provenance Unit)
    (storage : Allocation.tryNew (Prov := Provenance) size align .Uninit
      (fun size _ => some (Array.replicate size.bytesNat 0)) = .ok bytes)
    (sizeBound : bytes.byteSize.bytes ≤ s.cfg.allocation.maximumObjectSize.bytes)
    (notNative : bytes.nativeBuffer = none)
    (reserved : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId)
    (reserve : state.machine.memory.reserveAllocId = (reserved,.ok id))
    (tree : BorrowTree) (initialized : MachineHooks.MachineState MiriMemoryKind RootUser)
    (root : PlaceMachine.initStackExtra s.cfg.allocation.allocationTail id size align
      {state.machine with memory := reserved} = .ok tree initialized)
    (tracker : MachineHooks.BorrowState) (tag : BorTag)
    (enabled : initialized.borrowTracker = some tracker) (tagged : tracker.global.rootTag? id = some tag) :
    let committed : WholeCall.State := {state with machine := {initialized with memory :=
      {initialized.memory with live := initialized.memory.live.push (id,⟨.stack,bytes.withExtra tree⟩)}}}
    PlaceMachine.allocateStackRaw s.cfg.allocation size align state =
      ((do
        let pointer ← s.cfg.allocation.adjustRootAddress id tag
        pure pointer.withOptionalProvenance) : MachineHooks.M MiriMemoryKind RootUser (Pointer (Option Provenance))) committed := by
  dsimp only
  have native := native_storage s metadata capacity size align state
  have noOverflow : ¬s.cfg.allocation.maximumObjectSize.bytes < bytes.byteSize.bytes := UInt64.not_lt.mpr sizeBound
  unfold PlaceMachine.allocateStackRaw
  rw [native_binding s metadata capacity]
  simp only [bind,Bind.bind,EStateM.bind,native,storage,pure,Pure.pure,EStateM.pure]
  simp only [tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch]
  simp only [noOverflow,↓reduceIte,get,getThe,MonadStateOf.get,EStateM.get,set,MonadStateOf.set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,reserve]
  rw [diagnostic s metadata capacity]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,root]
  simp only [modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,bind,Bind.bind,EStateM.bind,
    pure,Pure.pure,EStateM.pure,enabled,tagged,get,getThe,MonadStateOf.get,EStateM.get,
    set,MonadStateOf.set,EStateM.set,EarlyReturnT.return,EarlyReturn.runK,
    ExceptT.bind,ExceptT.bindCont,ExceptT.mk,ExceptT.run,throw,throwThe,MonadExceptOf.throw]
  let committed : WholeCall.State := {state with machine := {initialized with memory :=
    {initialized.memory with live := initialized.memory.live.push (id,⟨.stack,bytes.withExtra tree⟩)}}}
  cases addressEq : s.cfg.allocation.adjustRootAddress id tag committed with
  | ok pointer after =>
    simp only [committed,enabled] at addressEq
    simp [addressEq,notNative,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      throw,throwThe,MonadExceptOf.throw,EStateM.throw,EStateM.nonBacktrackable,EStateM.dummySave,EStateM.dummyRestore]
  | error error after =>
    simp only [committed,enabled] at addressEq
    simp [addressEq,notNative,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      throw,throwThe,MonadExceptOf.throw,EStateM.throw,EStateM.nonBacktrackable,EStateM.dummySave,EStateM.dummyRestore]
    rfl

 theorem adjust_source (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : WholeCall.State) (id : AllocId) (tag : BorTag) (bytes : Allocation Provenance BorrowTree)
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,⟨.stack,bytes⟩)) :
    s.cfg.allocation.adjustRootAddress id tag state =
      ((do
        let address ← ExecutionAddressChoices.addrFromAllocId EvalCoreMachine.tape
          (ConcreteProtection.source s).pointers id (some .stack)
        pure (Pointer.new (.concrete id tag) (Size.ofBytes address))) :
          MachineHooks.M MiriMemoryKind RootUser (Pointer Provenance)) state := by
  rw [source s metadata capacity]
  simp [allocation,EvalConfiguration.allocation,Array.find?_map,Function.comp_def,live,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

 theorem reserve_initial (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition) (needed : InputDraft.NeedsEnclosingAllocation p) :
    ∃ (reserved : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId),
      p.before.machine.memory.reserveAllocId = (reserved,.ok id) ∧
      id.value = p.before.machine.memory.nextAllocId ∧
      p.before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false ∧
      p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none ∧
      p.before.machine.memory.live.find? (fun row => row.1 == id) = none := by
  have margins := resources.allocation needed
  have representation := input.projectedAllocator needed
    ⟨margins.available,margins.nonzero,fun active => ⟨margins.sourceAvailable active,margins.sourceNonzero active⟩⟩
  let id : AllocId := ⟨p.before.machine.memory.nextAllocId,margins.nonzero⟩
  obtain ⟨reserved,actual⟩ := MemoryState.reserve_of_highWater p.before.machine.memory margins.available margins.nonzero
    margins.sourceAvailable margins.sourceNonzero representation.issued representation.live representation.global representation.dead
  refine ⟨reserved,id,actual,rfl,extras_fresh s p representation margins.nonzero,?_,?_⟩
  · apply Array.find?_eq_none.mpr
    intro row member
    have issued := representation.basesIssued row member
    have below := representation.issued row.allocId issued
    have different : row.allocId ≠ id := by
      intro same
      rw [same] at below
      exact Nat.lt_irrefl _ below
    simpa only [beq_iff_eq] using different
  · apply Array.find?_eq_none.mpr
    intro row member
    have below := representation.live row member
    have different : row.1 ≠ id := by
      intro same
      rw [same] at below
      exact Nat.lt_irrefl _ below
    simpa only [beq_iff_eq] using different

/-- Reserving an ID changes supplies and issued ledgers, while current backing
and lookup metadata remain untouched until the new live row is registered. -/
 theorem reserve_registry (memory : MemoryState Provenance BorrowTree MiriMemoryKind) :
    let after := memory.reserveAllocId.1
    after.live = memory.live ∧ after.dead = memory.dead ∧
      after.getAllocInfo = memory.getAllocInfo ∧ after.isAllocLive = memory.isAllocLive := by
  unfold MemoryState.reserveAllocId
  simp only [Id.run,pure,Pure.pure]
  repeat' (first | split | constructor | rfl)

 theorem tag_room (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition) : input.tracker.global.nextPointerTag.value < 18446744073709551615 := by
  have bound := resources.tagRoom input.tracker input.world.enabled
  have budget : 64 ≤ resources.budget := by
    have reserve := resources.reserve
    unfold work at reserve
    omega
  change input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
  omega

end EmptyFunction.ProjectedAllocation
