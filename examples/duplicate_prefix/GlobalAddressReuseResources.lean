import duplicate_prefix.GlobalAddressReusePoolFrontier
namespace DuplicatePrefix.GlobalAddressReuseResources
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressReuseContents GlobalAddressReuseHoleGeometry GlobalAddressReusePairwise GlobalAddressReusePoolFrontier GlobalAddressBumpRangeFormation GlobalAddressRangeFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

structure State {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId → Size) : Prop where
  resources : GlobalAddressRangeResources.State memory addresses sizes
  generationEq : addresses.generation=some generation
  managed : addresses.addressMode=.managed
  cursor : generation.generator.nextBaseAddr≠0
  frontier : Frontier addresses.intToPtrMap sizes generation.generator
  holes : Contents generation.reusePool (Hole addresses.intToPtrMap sizes)
  bounded : Contents generation.reusePool (Bounded generation.generator)
  pairwise : Pairwise generation.reusePool

theorem stage {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation next : AddressGenerationState) (sizes : AllocId → Size) (initial : State memory addresses generation sizes)
    (cursor : next.generator.nextBaseAddr≠0) (frontier : Frontier addresses.intToPtrMap sizes next.generator)
    (holes : Contents next.reusePool (Hole addresses.intToPtrMap sizes))
    (bounded : Contents next.reusePool (Bounded next.generator)) (pairwise : Pairwise next.reusePool) :
    State memory {addresses with generation:=some next} next sizes :=
  ⟨⟨⟨initial.resources.recurring.live,initial.resources.recurring.ordered,initial.resources.recurring.unique⟩,initial.resources.apart,initial.resources.rows⟩,rfl,initial.managed,cursor,frontier,holes,bounded,pairwise⟩

theorem cache {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId → Size) (initial : State memory addresses generation sizes)
    (id : AllocId) (allocation : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,allocation)) (sizeEq : sizes id=allocation.allocation.byteSize)
    (address : UInt64) (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (fresh : id∉addresses.intToPtrMap.toList.map InverseAddressEntry.allocId) (positive : address≠0)
    (cut : Nat) (partition : WildcardInteriorHitAddress.Cut addresses.intToPtrMap address cut)
    (placement : Placement addresses.intToPtrMap sizes id address cut)
    (bound : address.toNat+max 1 allocation.allocation.byteSize.bytes.toNat≤generation.generator.nextBaseAddr.toNat)
    (holes : Contents generation.reusePool (Hole (addresses.intToPtrMap.insertIdx cut ⟨address,id⟩ partition.1) sizes)) :
    (addresses.cacheAddress id address).outcome=.ok () ∧
    State memory (addresses.cacheAddress id address).state generation sizes := by
  have live : memory.isAllocLive id=true := by
    have any:=MemoryCopyBridge.live_any_of_present memory id allocation present
    simp only [MemoryState.isAllocLive,any,Bool.true_or]
  have recurring:=GlobalAddressRecurringFormation.cache memory addresses initial.resources.recurring id live address uncached fresh positive cut partition
  have apart:=GlobalAddressRangeFormation.cache addresses sizes initial.resources.apart id address uncached positive cut partition placement
  have inverse:=GlobalAddressManagedBumpState.cache_inverse addresses id address uncached positive cut partition
  refine ⟨apart.1,⟨⟨recurring.2,apart.2,?_⟩,?_,?_,initial.cursor,?_,?_,initial.bounded,initial.pairwise⟩⟩
  · rw [inverse]
    intro row member
    rcases Array.mem_insertIdx.mp member with same | old
    · subst row
      rw [sizeEq]
      exact .localRow allocation present
    · exact initial.resources.rows row old
  · unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [uncached,Option.map_none]
    split <;> try exact initial.generationEq
    split <;> split <;> try exact initial.generationEq
    all_goals split <;> exact initial.generationEq
  · unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [uncached,Option.map_none]
    split <;> try exact initial.managed
    split <;> split <;> try exact initial.managed
    all_goals split <;> exact initial.managed
  · rw [inverse]
    intro row member
    rcases Array.mem_insertIdx.mp member with same | old
    · subst row
      simpa only [sizeEq] using bound
    · exact initial.frontier row old
  · rw [inverse]
    exact holes
end DuplicatePrefix.GlobalAddressReuseResources
