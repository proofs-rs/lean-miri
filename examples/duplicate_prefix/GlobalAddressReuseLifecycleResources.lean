import duplicate_prefix.GlobalAddressReuseManagedResources
namespace DuplicatePrefix.GlobalAddressReuseLifecycleResources
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressReuseResources GlobalAddressReuseContents GlobalAddressReuseHoleGeometry GlobalAddressReusePairwise GlobalAddressReusePoolFrontier GlobalAddressBumpRangeFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem seed {K} (memory : MemoryState Provenance BorrowTree K) (sizes : AllocId → Size)
    (mode : ProvenanceMode) (start stop : UInt64) (config : AddressReuseConfig) (positive : start≠0)
    (reuse : (Float.le 0.0 config.addressReuseRate && Float.le config.addressReuseRate 1.0)=true)
    (cross : (Float.le 0.0 config.addressReuseCrossThreadRate && Float.le config.addressReuseCrossThreadRate 1.0)=true) :
    ∃ addresses generation,GlobalAddressState.new mode .managed start stop config=.ok addresses ∧ State memory addresses generation sizes := by
  let generation : AddressGenerationState:=⟨AddressGenerator.new start stop,⟨config.addressReuseRate,config.addressReuseCrossThreadRate,#[]⟩⟩
  let addresses : GlobalAddressState:=⟨#[],#[],#[],mode,.managed,some generation,#[]⟩
  have source : GlobalAddressState.new mode .managed start stop config=.ok addresses := by
    unfold GlobalAddressState.new ReusePool.new
    unfold_internal ".ReusePool.validRate"
    simp only [reuse,cross,Bool.not_true,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,Except.mapError,bind,Except.bind,pure,Except.pure]
    rfl
  obtain ⟨other,actual,resources,frontier⟩:=GlobalAddressRangeResources.seed memory sizes mode start stop config reuse cross
  have same : other=addresses:=Except.ok.inj (actual.symm.trans source)
  subst other
  refine ⟨addresses,generation,source,⟨resources,rfl,rfl,positive,frontier,?_,?_,?_⟩⟩
  · intro bucket member
    change bucket∈(#[] : Array (Array ReusableAddress)) at member
    simp only [Array.not_mem_empty] at member
  · intro bucket member
    change bucket∈(#[] : Array (Array ReusableAddress)) at member
    simp only [Array.not_mem_empty] at member
  · intro left right a b one
    change GlobalAddressReusePairwise.peek #[] left=some a at one
    simp only [GlobalAddressReusePairwise.peek,Array.getElem?_empty,Option.bind_none] at one
    cases one

theorem free {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId → Size) (initial : State memory addresses generation sizes)
    (id : AllocId) (address : UInt64) (nonzero : address≠0) (size : Size) (sizeEq : sizes id=size)
    (position : Nat) (valid : position<addresses.intToPtrMap.size) (row : addresses.intToPtrMap[position]?=some ⟨address,id⟩)
    (cached : addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,address⟩)
    (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) (choice : Bool) (clock : Unit → VClock) :
    let result:=addresses.freeAllocId id size align kind thread choice clock
    State (source_memory_remove_live memory id).1 result.state
      {generation with reusePool:=(generation.reusePool.addAddr choice address size align kind thread clock).state} sizes := by
  dsimp only
  let next:={generation with reusePool:=(generation.reusePool.addAddr choice address size align kind thread clock).state}
  have frame:=GlobalAddressFreeHistoryFormation.free_erases addresses id address position valid initial.resources.recurring.ordered row cached size align kind thread choice clock
  have search:=WildcardOrderedHitAddress.inverse_hit addresses.intToPtrMap address id position valid initial.resources.recurring.ordered row
  have actual : addresses.intToPtrMap[position]=⟨address,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  have generationEq : (addresses.freeAllocId id size align kind thread choice clock).state.generation=some next := by
    unfold GlobalAddressState.freeAllocId
    unfold_internal ".GlobalAddressState.findBase"
    simp only [cached,Option.map_some,search,Bool.not_true,Bool.false_eq_true,↓reduceIte,valid,↓reduceDIte,actual,bne_self_eq_false,initial.generationEq]
    cases (generation.reusePool.addAddr choice address size align kind thread clock).outcome <;> rfl
  have managed : (addresses.freeAllocId id size align kind thread choice clock).state.addressMode=.managed := by
    unfold GlobalAddressState.freeAllocId
    unfold_internal ".GlobalAddressState.findBase"
    simp only [cached,Option.map_some,search,Bool.not_true,Bool.false_eq_true,↓reduceIte,valid,↓reduceDIte,actual,bne_self_eq_false,initial.generationEq]
    cases (generation.reusePool.addAddr choice address size align kind thread clock).outcome <;> exact initial.managed
  obtain ⟨holeGeneration,holeEq,holes⟩:=GlobalAddressReuseFreeHoles.free addresses generation sizes initial.generationEq initial.resources.recurring.ordered initial.resources.apart initial.holes id address nonzero size sizeEq position valid row cached align kind thread choice clock
  have same : holeGeneration=next:=Option.some.inj (holeEq.symm.trans generationEq)
  subst holeGeneration
  have separate:=GlobalAddressReuseFreePairwise.released generation.reusePool addresses.intToPtrMap sizes initial.holes id address size sizeEq position valid row thread (clock ())
  have pairwise:=GlobalAddressReuseAddPairwise.add generation.reusePool initial.pairwise choice address size align kind thread clock separate
  have releasedBound:=GlobalAddressReusePoolFrontier.released generation.generator addresses.intToPtrMap sizes initial.frontier id address size sizeEq position valid row thread (clock ())
  have bounded:=GlobalAddressReuseAddContents.add generation.reusePool (Bounded generation.generator) initial.bounded choice address size align kind thread clock releasedBound
  refine ⟨GlobalAddressRangeResources.free memory addresses sizes initial.resources id address position valid row cached size align kind thread choice clock,generationEq,managed,initial.cursor,?_,holes,bounded,pairwise⟩
  rw [frame.1]
  intro current present
  exact initial.frontier current (Array.mem_of_mem_eraseIdx present)
end DuplicatePrefix.GlobalAddressReuseLifecycleResources
