import empty_function.ChoiceProjection
import empty_function.AddressPost
namespace EmptyFunction.ProjectedAddress
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

 theorem stack_cache (state : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationAddressInfo) (slack : Fin 16)
    (managed : state.addressMode = .managed) (current : state.generation = some generation)
    (missing : state.baseAddr.find? (fun row => row.allocId == id) = none)
    (live : info.live = true) (data : info.kind = .liveData) (stack : info.memoryKind = some .stack)
    (alignment : info.align.pow2 ≤ 29) (room : RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.intToPtrMap, row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    let result := state.addrFromAllocId id (some info) ⟨false,false,0,slack⟩
    result.outcome = .ok (.ready (RawGenerator.base generation.generator info.align slack)) ∧
      result.state.baseAddr.find? (fun row => row.allocId == id) =
        some ⟨id,RawGenerator.base generation.generator info.align slack⟩ := by
  have bounds := RawGenerator.base_bounds generation.generator info.size info.align alignment slack room
  have nonzero : RawGenerator.base generation.generator info.align slack ≠ 0 := by
    intro zero
    rw [zero] at bounds
    change _ ≤ 0 ∧ _ at bounds
    omega
  have afterAll : ∀ row ∈ state.intToPtrMap, row.address < RawGenerator.base generation.generator info.align slack := by
    intro row member
    apply UInt64.lt_iff_toNat_lt.mpr
    have earlier := frontier row member
    omega
  have geometry : RawAddressCache.Cut state.intToPtrMap (RawGenerator.base generation.generator info.align slack)
      state.intToPtrMap.size := by
    refine ⟨Nat.le_refl _,?_,?_⟩
    · intro index valid before
      exact afterAll _ (Array.getElem_mem valid)
    · intro index valid after
      omega
  have cache (next : AddressGenerationState) :
      (({state with generation := some next} : GlobalAddressState).cacheAddress id
        (RawGenerator.base generation.generator info.align slack)) =
      ⟨{state with
          generation := some next
          baseAddr := state.baseAddr.push ⟨id,RawGenerator.base generation.generator info.align slack⟩
          intToPtrMap := state.intToPtrMap.insertIdx state.intToPtrMap.size
            ⟨RawGenerator.base generation.generator info.align slack,id⟩ (Nat.le_refl _)},.ok ()⟩ := by
    exact AddressPost.cache_at_cut ({state with generation := some next} : GlobalAddressState) id _ _ geometry missing nonzero
  have generated := RawGenerator.generated generation.generator info.size info.align alignment slack room
  unfold GlobalAddressState.addrFromAllocId
  unfold_source_base
  unfold_source_generation
  simp only [missing,Option.map_none,live,data,stack,managed,current,
    beq_self_eq_true,Bool.not_true,↓reduceIte,ReusePool.takeAddr,Id.run,pure,beq_iff_eq,generated]
  simp only [←managed,cache]
  simp [Array.find?_push,missing]

abbrev State := ChoiceProjection.S
abbrev Hooks := ChoiceProjection.H

def assigned (before : State) (addresses : GlobalAddressState) : State :=
  {before with machine := {before.machine with user := {before.machine.user with addresses}}}


def stackAttempt (state : State) (id : AllocId) (size : Size) (align : Align) (slack : Fin 16) :=
  state.machine.user.addresses.addrFromAllocId id
    (some ⟨.liveData,true,size,align,some .stack,UInt32.ofNat state.machine.threads.activeThread.toNat⟩)
    ⟨false,false,0,slack⟩

 theorem assign_exact (hooks : Hooks) (state : State) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState) (slack : Fin 16)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation)
    (alignment : info.align.pow2 ≤ 29) (room : RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.machine.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    let view : AllocationAddressInfo := ⟨.liveData,true,info.size,info.align,some .stack,
      UInt32.ofNat state.machine.threads.activeThread.toNat⟩
    let addresses := (state.machine.user.addresses.addrFromAllocId id (some view) ⟨false,false,0,slack⟩).state
    PointerMachine.addrFromAllocId hooks id (some .stack) ⟨false,false,0,slack⟩ state =
      .ok (RawGenerator.base generation.generator info.align slack) (assigned state addresses) ∧
      addresses.baseAddr.find? (fun row => row.allocId == id) =
        some ⟨id,RawGenerator.base generation.generator info.align slack⟩ := by
  dsimp only
  let view : AllocationAddressInfo := ⟨.liveData,true,info.size,info.align,some .stack,
    UInt32.ofNat state.machine.threads.activeThread.toNat⟩
  have ready := stack_cache state.machine.user.addresses generation id view slack managed current missing rfl rfl rfl
    alignment room positive frontier
  refine ⟨?_,ready.2⟩
  unfold PointerMachine.addrFromAllocId
  unfold_pointer_address_helpers
  simp [missing,metadata,data,live,managed,view,assigned,ready.1,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]

 theorem stack_exact (hooks : Hooks) (state : State) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation)
    (alignment : info.align.pow2 ≤ 29) (room : ∀ slack, RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.machine.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat)
    (supply : ChoiceSupply.Environment ChoiceSupply.stackMissPlan (ChoiceProjection.tapeAccess.get state)) :
    ∃ (value : Nat) (supported : value < 16) (addresses : GlobalAddressState),
      ExecutionAddressChoices.addrFromAllocId ChoiceProjection.tapeAccess hooks id (some .stack) state =
        .ok (RawGenerator.base generation.generator info.align ⟨value,supported⟩)
          (assigned (ChoiceProjection.afterDraw state value) addresses) ∧
      addresses.baseAddr.find? (fun row => row.allocId == id) =
        some ⟨id,RawGenerator.base generation.generator info.align ⟨value,supported⟩⟩ ∧
      addresses = (stackAttempt state id info.size info.align ⟨value,supported⟩).state ∧
      (stackAttempt state id info.size info.align ⟨value,supported⟩).outcome =
        .ok (.ready (RawGenerator.base generation.generator info.align ⟨value,supported⟩)) := by
  obtain ⟨value,bound,head⟩ := ChoiceSupply.stack_fits _ |>.mp supply.fits
  have request := ChoiceProjection.stack_request hooks state id info generation missing metadata data live managed current
  have draw := ExecutionChoices.index_supplied ChoiceProjection.tapeAccess state (ChoiceProjection.tapeAccess.get state)
    .addressSlack 16 value rfl supply.strict head bound
  have supplied : ExecutionAddressChoices.addrFromAllocId ChoiceProjection.tapeAccess hooks id (some .stack) state =
      PointerMachine.addrFromAllocId hooks id (some .stack) ⟨false,false,0,⟨value,bound⟩⟩
        (ChoiceProjection.afterDraw state value) := by
    rw [request]
    simp only [bind,Bind.bind,EStateM.bind,draw,bound,↓reduceDIte]
    rfl
  have actual := assign_exact hooks (ChoiceProjection.afterDraw state value) id info generation ⟨value,bound⟩
    missing metadata data live managed current alignment (room _) positive frontier
  have outcome := stack_cache state.machine.user.addresses generation id
    ⟨.liveData,true,info.size,info.align,some .stack,UInt32.ofNat state.machine.threads.activeThread.toNat⟩
    ⟨value,bound⟩ managed current missing rfl rfl rfl alignment (room _) positive frontier
  exact ⟨value,bound,_,supplied.trans actual.1,actual.2,rfl,outcome.1⟩


/-- Internal address-stage composition for any legal tape policy. The supplied
index equation is discharged by PolicyChoiceSupply, including fallback draws. -/
theorem stack_after_index (hooks : Hooks) (state : State) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation)
    (alignment : info.align.pow2 ≤ 29) (room : ∀ slack, RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.machine.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat)
    (value : Nat) (supported : value < 16) (nextTape : ExecutionChoices.Tape)
    (draw : ExecutionChoices.index ChoiceProjection.tapeAccess .addressSlack 16 state =
      .ok value (ChoiceProjection.tapeAccess.put state nextTape)) :
    ∃ addresses : GlobalAddressState,
      ExecutionAddressChoices.addrFromAllocId ChoiceProjection.tapeAccess hooks id (some .stack) state =
        .ok (RawGenerator.base generation.generator info.align ⟨value,supported⟩)
          (assigned (ChoiceProjection.tapeAccess.put state nextTape) addresses) ∧
      addresses.baseAddr.find? (fun row => row.allocId == id) =
        some ⟨id,RawGenerator.base generation.generator info.align ⟨value,supported⟩⟩ ∧
      addresses = (stackAttempt state id info.size info.align ⟨value,supported⟩).state ∧
      (stackAttempt state id info.size info.align ⟨value,supported⟩).outcome =
        .ok (.ready (RawGenerator.base generation.generator info.align ⟨value,supported⟩)) := by
  have request := ChoiceProjection.stack_request hooks state id info generation missing metadata data live managed current
  have supplied : ExecutionAddressChoices.addrFromAllocId ChoiceProjection.tapeAccess hooks id (some .stack) state =
      PointerMachine.addrFromAllocId hooks id (some .stack) ⟨false,false,0,⟨value,supported⟩⟩
        (ChoiceProjection.tapeAccess.put state nextTape) := by
    rw [request]
    simp only [bind,Bind.bind,EStateM.bind,draw,supported,↓reduceDIte]
  have actual := assign_exact hooks (ChoiceProjection.tapeAccess.put state nextTape) id info generation ⟨value,supported⟩
    missing metadata data live managed current alignment (room _) positive frontier
  have outcome := stack_cache state.machine.user.addresses generation id
    ⟨.liveData,true,info.size,info.align,some .stack,UInt32.ofNat state.machine.threads.activeThread.toNat⟩
    ⟨value,supported⟩ managed current missing rfl rfl rfl alignment (room _) positive frontier
  exact ⟨_,supplied.trans actual.1,actual.2,rfl,outcome.1⟩
end EmptyFunction.ProjectedAddress
