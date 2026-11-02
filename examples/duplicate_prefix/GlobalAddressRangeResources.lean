import duplicate_prefix.GlobalAddressGcSizeFormation
namespace DuplicatePrefix.GlobalAddressRangeResources
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressRangeFormation GlobalAddressBumpRangeFormation GlobalAddressManagedBumpFormation GlobalAddressManagedBumpState WildcardEmptyFamilyFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Raw recurring address resources. Size suppliers are actual live rows or
MEMORY/STATIC descriptors; function/vaList metadata is outside this certificate. -/
structure State {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (sizes : AllocId → Size) : Prop where
  recurring : GlobalAddressRecurringFormation.State memory addresses
  apart : Apart addresses.intToPtrMap sizes
  rows : Rows memory addresses.intToPtrMap sizes

theorem sizeRows {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (initial : State memory addresses sizes) :
    ∀ row ∈ addresses.intToPtrMap, WildcardMetadataGap.SizeRow memory row.allocId (sizes row.allocId) :=
  fun row member => GlobalAddressLiveSizeFormation.sizeRow memory _ _ (initial.rows row member)

/-- Real initialization forms all geometry and supplier resources, plus the
source cursor frontier. No initial Apart or SizeRow is supplied. -/
theorem seed {K} (memory : MemoryState Provenance BorrowTree K) (sizes : AllocId → Size)
    (provenanceMode : ProvenanceMode) (start stop : UInt64) (config : AddressReuseConfig)
    (reuse : (Float.le 0.0 config.addressReuseRate && Float.le config.addressReuseRate 1.0) = true)
    (cross : (Float.le 0.0 config.addressReuseCrossThreadRate && Float.le config.addressReuseCrossThreadRate 1.0) = true) :
    ∃ addresses, GlobalAddressState.new provenanceMode .managed start stop config = .ok addresses ∧
      State memory addresses sizes ∧ Frontier addresses.intToPtrMap sizes (AddressGenerator.new start stop) := by
  obtain ⟨addresses,actual,apart,rows,frontier⟩ := GlobalAddressManagedBumpState.seed memory sizes provenanceMode start stop config reuse cross
  obtain ⟨other,otherActual,recurring⟩ := GlobalAddressRecurringFormation.new memory provenanceMode .managed start stop config reuse cross
  have same : other=addresses := Except.ok.inj (otherActual.symm.trans actual)
  subst other
  exact ⟨addresses,actual,⟨recurring,apart,rows⟩,frontier⟩

/-- Actual managed source address assignment, not caller-supplied Placement,
forms the next recurring resources from a physical live allocation row. -/
theorem managed_bump {K} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState) (sizes : AllocId → Size)
    (initial : State memory addresses sizes) (frontier : Frontier addresses.intToPtrMap sizes generation.generator)
    (managed : addresses.addressMode = .managed) (generationEq : addresses.generation = some generation)
    (cursor : generation.generator.nextBaseAddr ≠ 0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (sizeEq : sizes id = entry.allocation.byteSize)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (fresh : id ∉ addresses.intToPtrMap.toList.map InverseAddressEntry.allocId)
    (kind : AddressMemoryKind) (thread : AddressThreadId) (slack : Fin 16)
    (allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true)
    (room : Room generation.generator entry.allocation.byteSize slack) :
    let output := addresses.addrFromAllocId id (some (info entry.allocation.byteSize kind thread)) (choices slack)
    output.outcome = .ok (.ready (base generation.generator slack)) ∧ State memory output.state sizes ∧
      Frontier output.state.intToPtrMap sizes (next generation.generator entry.allocation.byteSize slack) := by
  dsimp only
  have data := GlobalAddressManagedBumpState.advance memory addresses generation sizes initial.apart initial.rows frontier
    managed generationEq cursor id entry present sizeEq uncached kind thread slack allowed room
  have actual := (source addresses generation sizes initial.apart frontier managed generationEq cursor id entry.allocation.byteSize sizeEq uncached kind thread slack allowed room).1
  have partition := (placement addresses.intToPtrMap sizes generation.generator frontier id entry.allocation.byteSize sizeEq slack room).1
  have positive : base generation.generator slack ≠ 0 := by
    intro zero
    have value := base_nat generation.generator entry.allocation.byteSize slack room
    rw [zero] at value
    change (0:Nat)=generation.generator.nextBaseAddr.toNat+slack.val at value
    have nz : generation.generator.nextBaseAddr.toNat ≠ 0 := by intro eq;exact cursor (UInt64.toNat_inj.mp eq)
    omega
  have live : memory.isAllocLive id=true := by
    have any := MemoryCopyBridge.live_any_of_present memory id entry present
    simp only [MemoryState.isAllocLive,any,Bool.true_or]
  have stagedRecurring : GlobalAddressRecurringFormation.State memory (ready addresses generation entry.allocation.byteSize slack) :=
    ⟨initial.recurring.live,initial.recurring.ordered,initial.recurring.unique⟩
  have recurring := (GlobalAddressRecurringFormation.cache memory (ready addresses generation entry.allocation.byteSize slack)
    stagedRecurring id live (base generation.generator slack) uncached fresh positive addresses.intToPtrMap.size partition).2
  refine ⟨data.1,⟨?_,data.2.1,data.2.2.1⟩,data.2.2.2⟩
  rw [actual]
  exact recurring

/-- Successful coherent free removes the only inverse identity; range and raw
size resources survive even a later pool error. The retained base cache is
not confused with a still-live inverse row. -/
theorem free {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (initial : State memory addresses sizes) (id : AllocId) (baseAddress : UInt64) (position : Nat)
    (valid : position < addresses.intToPtrMap.size) (row : addresses.intToPtrMap[position]? = some ⟨baseAddress,id⟩)
    (cached : addresses.baseAddr.find? (fun entry => entry.allocId == id) = some ⟨id,baseAddress⟩)
    (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    State (source_memory_remove_live memory id).1 (addresses.freeAllocId id size align kind thread reuseChoice clock).state sizes := by
  have injective : ∀ i (hi:i<addresses.intToPtrMap.size) j (hj:j<addresses.intToPtrMap.size),
      addresses.intToPtrMap[i].allocId=addresses.intToPtrMap[j].allocId → i=j := by
    intro i hi j hj same
    apply initial.recurring.unique.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
    simpa using same
  have different := GlobalAddressFreeHistoryFormation.free_shrinks_live addresses (fun _=>True)
    ⟨fun _ _=>True.intro,fun _ _=>True.intro⟩ id baseAddress position valid initial.recurring.ordered row cached injective size align kind thread reuseChoice clock
  refine ⟨GlobalAddressRecurringFormation.free memory addresses initial.recurring id baseAddress position valid row cached size align kind thread reuseChoice clock,
    GlobalAddressRangeFormation.free addresses sizes initial.apart initial.recurring.ordered id baseAddress position valid row cached size align kind thread reuseChoice clock,?_⟩
  intro current member
  have old := (GlobalAddressFreeHistoryFormation.free_subsets addresses id size align kind thread reuseChoice clock).1 current member
  exact GlobalAddressLiveSizeFormation.remove_other memory id current.allocId (different.1 current member).2 _ (initial.rows current old)

theorem expose {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (initial : State memory addresses sizes) (provenance : Provenance) (tracking : Bool) (hook : Option (Except String Unit)) :
    let live := match provenance with | .wildcard => none | .concrete id _ => some (memory.isAllocLive id)
    State memory (addresses.exposeProvenance provenance live tracking hook).state sizes := by
  refine ⟨GlobalAddressRecurringFormation.expose memory addresses initial.recurring provenance tracking hook,
    GlobalAddressRangeFormation.expose addresses sizes initial.apart provenance _ tracking hook,?_⟩
  rw [GlobalAddressExposureFormation.expose_inverse]
  exact initial.rows

end DuplicatePrefix.GlobalAddressRangeResources
