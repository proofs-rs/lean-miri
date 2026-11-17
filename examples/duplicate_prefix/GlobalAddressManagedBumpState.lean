import duplicate_prefix.GlobalAddressManagedBumpFormation
namespace DuplicatePrefix.GlobalAddressManagedBumpState
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressRangeFormation GlobalAddressBumpRangeFormation GlobalAddressManagedBumpFormation WildcardEmptyFamilyFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Rows {K : Type} (memory : MemoryState Provenance BorrowTree K) (entries : Array InverseAddressEntry) (sizes : AllocId → Size) : Prop :=
  ∀ row ∈ entries, GlobalAddressLiveSizeFormation.Row memory row.allocId (sizes row.allocId)

theorem cache_inverse (addresses : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none) (nonzero : address ≠ 0)
    (cut : Nat) (partition : WildcardInteriorHitAddress.Cut addresses.intToPtrMap address cut) :
    (addresses.cacheAddress id address).state.intToPtrMap = addresses.intToPtrMap.insertIdx cut ⟨address,id⟩ partition.1 := by
  have search := WildcardInteriorHitAddress.inverse_cut addresses.intToPtrMap address cut partition
  have nz : (address == 0) = false := by simpa using nonzero
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  simp only [uncached,Option.map_none,search,nz,Bool.false_eq_true,↓reduceIte,partition.1,↓reduceDIte]
  rfl

theorem frontier_insert (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (generator : AddressGenerator) (initial : Frontier entries sizes generator)
    (id : AllocId) (size : Size) (sizeEq : sizes id = size) (slack : Fin 16) (room : Room generator size slack)
    (bounded : entries.size ≤ entries.size) :
    Frontier (entries.insertIdx entries.size ⟨base generator slack,id⟩ bounded) sizes (next generator size slack) := by
  intro row member
  have nextValue := next_nat generator size slack room
  rcases Array.mem_insertIdx.mp member with same | old
  · subst row
    rw [sizeEq,base_nat generator size slack room,nextValue]
    omega
  · have prior := initial row old
    rw [nextValue]
    omega

/-- Actual managed allocation-address assignment forms both range separation
and raw live size suppliers from source generation and actual memory rows.
The recurring frontier supplies Placement internally. -/
theorem advance {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (generation : AddressGenerationState) (sizes : AllocId → Size)
    (apart : Apart addresses.intToPtrMap sizes) (rows : Rows memory addresses.intToPtrMap sizes)
    (frontier : Frontier addresses.intToPtrMap sizes generation.generator)
    (managed : addresses.addressMode = .managed) (generationEq : addresses.generation = some generation)
    (cursor : generation.generator.nextBaseAddr ≠ 0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (sizeEq : sizes id = entry.allocation.byteSize)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (kind : AddressMemoryKind) (thread : AddressThreadId) (slack : Fin 16)
    (allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true)
    (room : Room generation.generator entry.allocation.byteSize slack) :
    let output := addresses.addrFromAllocId id (some (info entry.allocation.byteSize kind thread)) (choices slack)
    output.outcome = .ok (.ready (base generation.generator slack)) ∧
    Apart output.state.intToPtrMap sizes ∧ Rows memory output.state.intToPtrMap sizes ∧
    Frontier output.state.intToPtrMap sizes (next generation.generator entry.allocation.byteSize slack) := by
  dsimp only
  obtain ⟨actual,ranges⟩ := source addresses generation sizes apart frontier managed generationEq cursor id entry.allocation.byteSize sizeEq uncached kind thread slack allowed room
  rw [actual]
  have placementFacts := placement addresses.intToPtrMap sizes generation.generator frontier id entry.allocation.byteSize sizeEq slack room
  have positive : base generation.generator slack ≠ 0 := by
    intro zero
    have value := base_nat generation.generator entry.allocation.byteSize slack room
    rw [zero] at value
    change (0:Nat) = generation.generator.nextBaseAddr.toNat+slack.val at value
    have nz : generation.generator.nextBaseAddr.toNat ≠ 0 := by intro eq;exact cursor (UInt64.toNat_inj.mp eq)
    omega
  refine ⟨rfl,ranges,?_,?_⟩
  all_goals rw [cache_inverse (ready addresses generation entry.allocation.byteSize slack) id (base generation.generator slack)
    uncached positive addresses.intToPtrMap.size placementFacts.1]
  · intro row member
    rcases Array.mem_insertIdx.mp member with same | old
    · subst row
      rw [sizeEq]
      exact .localRow entry present
    · exact rows row old
  · exact frontier_insert addresses.intToPtrMap sizes generation.generator frontier id entry.allocation.byteSize sizeEq slack room (Nat.le_refl _)

/-- Real address-state initialization supplies empty physical geometry and
metadata for any actual memory; it never assumes a prebuilt range invariant. -/
theorem seed {K : Type} (memory : MemoryState Provenance BorrowTree K) (sizes : AllocId → Size)
    (provenanceMode : ProvenanceMode) (start stop : UInt64) (config : AddressReuseConfig)
    (reuse : (Float.le 0.0 config.addressReuseRate && Float.le config.addressReuseRate 1.0) = true)
    (cross : (Float.le 0.0 config.addressReuseCrossThreadRate && Float.le config.addressReuseCrossThreadRate 1.0) = true) :
    ∃ addresses, GlobalAddressState.new provenanceMode .managed start stop config = .ok addresses ∧
      Apart addresses.intToPtrMap sizes ∧ Rows memory addresses.intToPtrMap sizes ∧
      Frontier addresses.intToPtrMap sizes (AddressGenerator.new start stop) := by
  unfold GlobalAddressState.new ReusePool.new
  unfold_internal ".ReusePool.validRate"
  simp only [reuse,cross,Bool.not_true,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,Except.mapError,bind,Except.bind,pure,Except.pure]
  refine ⟨_,rfl,?_,?_,?_⟩
  · intro left right valid less
    change right < 0 at valid
    omega
  · intro row member
    change row ∈ (#[] : Array InverseAddressEntry) at member
    simp only [Array.not_mem_empty] at member
  · intro row member
    change row ∈ (#[] : Array InverseAddressEntry) at member
    simp only [Array.not_mem_empty] at member

end DuplicatePrefix.GlobalAddressManagedBumpState
