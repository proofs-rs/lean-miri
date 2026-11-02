import empty_function.ReuseEnsure
import empty_function.ChoiceExecution
import empty_function.ChoiceFloatSupport
namespace EmptyFunction.BumpAddress
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
private theorem pure_bump (state : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationAddressInfo) (choices : AddressRandomChoices)
    (managed : state.addressMode = .managed)
    (current : state.generation = some generation)
    (uncached : state.baseAddr.find? (fun row => row.allocId == id) = none)
    (live : info.live = true) (data : info.kind = .liveData)
    (kind : info.memoryKind = some .other)
    (taken : generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex
      info.size info.align .other info.thread = ⟨generation.reusePool,.ok none⟩)
    (alignment : info.align.pow2 ≤ 29)
    (room : RawGenerator.Room generation.generator info.size info.align choices.slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    (state.addrFromAllocId id (some info) choices).outcome =
      .ok (.ready (RawGenerator.base generation.generator info.align choices.slack)) := by
  have bounds := RawGenerator.base_bounds generation.generator info.size info.align alignment choices.slack room
  have nonzero : RawGenerator.base generation.generator info.align choices.slack ≠ 0 := by
    intro zero
    rw [zero] at bounds
    change _ ≤ 0 ∧ _ at bounds
    omega
  have afterAll : ∀ row ∈ state.intToPtrMap,
      row.address < RawGenerator.base generation.generator info.align choices.slack := by
    intro row member
    apply UInt64.lt_iff_toNat_lt.mpr
    have earlier := frontier row member
    omega
  have cache (next : AddressGenerationState) :
      (({state with generation := some next} : GlobalAddressState).cacheAddress id
        (RawGenerator.base generation.generator info.align choices.slack)).outcome = .ok () :=
    RawAddressCache.cache_after _ id _ uncached nonzero afterAll
  have generated := RawGenerator.generated generation.generator info.size info.align alignment choices.slack room
  unfold GlobalAddressState.addrFromAllocId
  unfold_source_base
  unfold_source_generation
  simp only [uncached,Option.map_none,live,data,kind,managed,current,
    Bool.not_true,
    Id.run,pure,beq_iff_eq,taken,generated]
  simp only [← managed, cache]
  simp

private theorem assign_bump (hooks : ChoiceExecution.H) (state : ChoiceExecution.S) (id : AllocId)
    (info : AllocationInfo) (generation : AllocAddresses.AddressGenerationState)
    (choices : AllocAddresses.AddressRandomChoices)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (current : state.user.addresses.generation = some generation)
    (taken : generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex
      info.size info.align .other (UInt32.ofNat state.threads.activeThread.toNat) = ⟨generation.reusePool,.ok none⟩)
    (alignment : info.align.pow2 ≤ 29)
    (room : RawGenerator.Room generation.generator info.size info.align choices.slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    ∃ after, MachineAddress.assign hooks id (some .other) choices state =
      .ok (RawGenerator.base generation.generator info.align choices.slack) after ∧
      after.memory = state.memory ∧ after.borrowTracker = state.borrowTracker ∧
      after.threads = state.threads ∧ after.dataRace = state.dataRace ∧
      after.user.payload = state.user.payload := by
  let addressInfo : AllocAddresses.AllocationAddressInfo := {
    kind := .liveData, live := true, size := info.size, align := info.align,
    memoryKind := some .other, thread := UInt32.ofNat state.threads.activeThread.toNat }
  have ready := pure_bump state.user.addresses generation id addressInfo choices
    managed current missing rfl rfl rfl taken alignment room positive frontier
  cases actual : state.user.addresses.addrFromAllocId id (some addressInfo) choices ⟨none⟩ with
  | mk afterAddress outcome =>
    have outcomeReady : outcome = .ok (.ready (RawGenerator.base generation.generator info.align choices.slack)) := by
      simpa only [actual] using ready
    subst outcome
    simp only [addressInfo] at actual
    unfold MachineAddress.assign
    unfold_machine_address_helpers
    simp [missing,metadata,notDead,notType,live,managed,actual,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]


/-- Every legal no-reuse response follows the source fresh-address path. The
pool's no-hole result is derived, rather than supplied as an operation law. -/
theorem no_reuse (hooks : ChoiceExecution.H) (state : ChoiceExecution.S) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState) (slack : Fin 16)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (current : state.user.addresses.generation = some generation)
    (lower : Float.le 0.0 generation.reusePool.addressReuseRate = true)
    (upper : Float.le generation.reusePool.addressReuseRate 1.0 = true)
    (support : ChoiceSupply.Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
      (.boolean .addressReuse false))
    (alignment : info.align.pow2 ≤ 29)
    (room : RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    ∃ after, MachineAddress.assign hooks id (some .other) ⟨false,false,0,slack⟩ state =
      .ok (RawGenerator.base generation.generator info.align slack) after ∧
      after.memory = state.memory ∧ after.borrowTracker = state.borrowTracker ∧
      after.threads = state.threads ∧ after.dataRace = state.dataRace ∧
      after.user.payload = state.user.payload := by
  apply assign_bump hooks state id info generation _ missing metadata notDead notType live managed current
  · exact (ReuseTake.no_reuse generation.reusePool info.size info.align
      (UInt32.ofNat state.threads.activeThread.toNat) false 0
      (ChoiceFloatSupport.allowed_of_supported .reuse _ false lower upper support)).2
  · exact alignment
  · exact room
  · exact positive
  · exact frontier
/-- A source empty current interval takes the checked bump path, including
reuse=true/cross-thread choices, without changing to a no-reuse profile. -/
theorem empty_bucket (hooks : ChoiceExecution.H) (state : ChoiceExecution.S) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState) (slack : Fin 16)
    (bucket : Array ReusableAddress) (bytes : UInt64) (cross : Bool)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (current : state.user.addresses.generation = some generation)
    (present : generation.reusePool.pool[info.align.pow2]? = some bucket)
    (abiBytes : Align.bytes info.align = .ok bytes) (normalized : Align.fromBytes bytes = .ok info.align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross = true)
    (empty : (ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).2 =
      (ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).1)
    (room : RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    ∃ after, MachineAddress.assign hooks id (some .other) ⟨true,cross,0,slack⟩ state =
      .ok (RawGenerator.base generation.generator info.align slack) after ∧
      after.memory = state.memory ∧ after.borrowTracker = state.borrowTracker ∧
      after.threads = state.threads ∧ after.dataRace = state.dataRace ∧
      after.user.payload = state.user.payload := by
  apply assign_bump hooks state id info generation _ missing metadata notDead notType live managed current
  · exact ReuseTake.take_empty generation.reusePool bucket info.size info.align bytes
      (UInt32.ofNat state.threads.activeThread.toNat) cross 0 present abiBytes normalized reuseAllowed crossAllowed empty
  · exact RawGenerator.normalized_exponent info.align bytes normalized
  · exact room
  · exact positive
  · exact frontier
end EmptyFunction.BumpAddress
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.BumpAddress.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved bump address axiom {dependency} in {name}"
