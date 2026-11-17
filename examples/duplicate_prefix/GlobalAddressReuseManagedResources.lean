import duplicate_prefix.GlobalAddressReuseResources
namespace DuplicatePrefix.GlobalAddressReuseManagedResources
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressReuseResources GlobalAddressReuseContents GlobalAddressReuseHoleGeometry GlobalAddressReusePoolFrontier GlobalAddressAlignedBumpFormation
open GlobalAddressBumpRangeFormation (Frontier)
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.split false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def Post {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (sizes : AllocId → Size) : Prop :=
  ∃ generation,State memory addresses generation sizes

theorem returned {K} (memory : MemoryState Provenance BorrowTree K) (staged : GlobalAddressState)
    (id : AllocId) (address : UInt64) (sizes : AllocId → Size)
    (good : Post memory (staged.cacheAddress id address).state sizes) (clockResult : Except String Unit) :
    Post memory (GlobalAddressState.completeAcquire (match (staged.cacheAddress id address).outcome with
      | .ok _ => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id address).state,.ok (.ready address)⟩)
      | .error error => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id address).state,.error error⟩)) clockResult).state sizes := by
  cases (staged.cacheAddress id address).outcome <;> exact good

/-- Every managed choice and clock outcome preserves the recurring live-row,
size, nonoverlap, pool-hole pairwise/availability and cursor resources. Fresh
fallback geometry comes from numeric source room, and reuse geometry from
actual stored holes; no operation-success or final-geometry input is used. -/
theorem complete {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId → Size) (initial : State memory addresses generation sizes)
    (id : AllocId) (allocation : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,allocation))
    (sizeEq : sizes id=allocation.allocation.byteSize)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (fresh : id∉addresses.intToPtrMap.toList.map InverseAddressEntry.allocId)
    (align : Align) (valid : align.pow2≤29) (kind : AddressMemoryKind) (thread : AddressThreadId) (choices : AddressRandomChoices)
    (room : Room generation.generator allocation.allocation.byteSize align choices.slack) (clockResult : Except String Unit) :
    Post memory (GlobalAddressState.completeAcquire (addresses.addrFromAllocId id
      (some (GlobalAddressAlignedManagedFormation.info allocation.allocation.byteSize align kind thread)) choices) clockResult).state sizes := by
  let size:=allocation.allocation.byteSize
  let taken:=generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex size align kind thread
  have takeFacts:=GlobalAddressReuseHoleGeometry.take_separated generation.reusePool addresses.intToPtrMap sizes initial.holes initial.resources.recurring.ordered id size sizeEq
    choices.reuse choices.crossThread choices.poolIndex align kind thread
  have pairFacts:=GlobalAddressReuseTakePairwise.take generation.reusePool (Hole addresses.intToPtrMap sizes) initial.holes initial.pairwise choices.reuse choices.crossThread choices.poolIndex size align kind thread
  have boundFacts:=GlobalAddressReusePoolFrontier.take generation.reusePool generation.generator initial.bounded choices.reuse choices.crossThread choices.poolIndex size align kind thread
  let afterTake:={addresses with generation:=some {generation with reusePool:=taken.state}}
  have afterTakeGood : State memory afterTake {generation with reusePool:=taken.state} sizes :=
    stage memory addresses generation _ sizes initial initial.cursor initial.frontier takeFacts.1 boundFacts.1 pairFacts.1
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,GlobalAddressAlignedManagedFormation.info,initial.managed,initial.generationEq,
    show (AllocationAddressKind.liveData==AllocationAddressKind.dead)=false from rfl,beq_iff_eq,reduceCtorEq,
    Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  simp only [←initial.managed]
  cases outcome : (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex allocation.allocation.byteSize align kind thread).outcome with
  | error error => exact ⟨_,afterTakeGood⟩
  | ok optional =>
    try dsimp only
    cases optional with
    | none =>
      try dsimp only
      have bump:=generated generation.generator size align valid choices.slack room
      dsimp only [size] at bump
      simp only [bump]
      have geometry:=placement addresses.intToPtrMap sizes generation.generator initial.frontier id size align valid choices.slack room
      have positive : base generation.generator align choices.slack≠0 := by
        intro zero
        have lower:=(base_bounds generation.generator size align valid choices.slack room).1
        rw [zero] at lower
        change generation.generator.nextBaseAddr.toNat+choices.slack.val≤0 at lower
        have nz : generation.generator.nextBaseAddr.toNat≠0 := by intro eq;exact initial.cursor (UInt64.toNat_inj.mp eq)
        omega
      have nextValue:=next_nat generation.generator size align valid choices.slack room
      have grows : generation.generator.nextBaseAddr.toNat≤(next generation.generator size align choices.slack).nextBaseAddr.toNat := by
        have lower:=(base_bounds generation.generator size align valid choices.slack room).1
        omega
      have nextPositive : (next generation.generator size align choices.slack).nextBaseAddr≠0 := by
        intro zero
        have nz : generation.generator.nextBaseAddr.toNat≠0 := by intro eq;exact initial.cursor (UInt64.toNat_inj.mp eq)
        rw [zero] at grows
        change generation.generator.nextBaseAddr.toNat≤0 at grows
        omega
      let nextPool:=if (next generation.generator size align choices.slack).nextBaseAddr > (next generation.generator size align choices.slack).endAddr/2 then taken.state.addressSpaceShortage else taken.state
      let nextGeneration:AddressGenerationState:=⟨next generation.generator size align choices.slack,nextPool⟩
      let staged:={addresses with generation:=some nextGeneration}
      have poolSame : nextPool.pool=taken.state.pool := by
        unfold nextPool
        split
        · unfold ReusePool.addressSpaceShortage;split <;> rfl
        · rfl
      have stagedGood : State memory staged nextGeneration sizes := by
        apply stage memory addresses generation nextGeneration sizes initial nextPositive
        · intro row member
          have old:=initial.frontier row member
          exact Nat.le_trans old grows
        · change Contents nextPool _
          unfold Contents
          rw [poolSame]
          exact takeFacts.1
        · have mono:=GlobalAddressReusePoolFrontier.mono taken.state generation.generator _ boundFacts.1 grows
          change Contents nextPool _
          unfold Contents
          rw [poolSame]
          exact mono
        · change GlobalAddressReusePairwise.Pairwise nextPool
          unfold GlobalAddressReusePairwise.Pairwise
          rw [poolSame]
          exact pairFacts.1
      have newHoles : Contents nextPool (Hole (addresses.intToPtrMap.insertIdx addresses.intToPtrMap.size ⟨base generation.generator align choices.slack,id⟩ geometry.1.1) sizes) := by
        unfold Contents
        rw [poolSame]
        exact fresh_insert taken.state addresses.intToPtrMap sizes generation.generator takeFacts.1 boundFacts.1 id size align valid choices.slack room _ geometry.1.1
      have cached:=GlobalAddressReuseResources.cache memory staged nextGeneration sizes stagedGood id allocation present sizeEq _ uncached fresh positive _ geometry.1 geometry.2 (Nat.le_of_eq nextValue.symm) newHoles
      try simp only [←initial.managed]
      change Post memory (GlobalAddressState.completeAcquire (match (staged.cacheAddress id (base generation.generator align choices.slack)).outcome with
        | .ok _ => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id (base generation.generator align choices.slack)).state,.ok (.ready (base generation.generator align choices.slack))⟩)
        | .error error => (show AddressStateResult AddressAssignment from ⟨(staged.cacheAddress id (base generation.generator align choices.slack)).state,.error error⟩)) clockResult).state sizes
      exact returned memory staged id _ sizes ⟨_,cached.2⟩ clockResult
    | some used =>
      try dsimp only
      obtain ⟨positive,cut,partition,placement⟩:=takeFacts.2 used outcome
      obtain ⟨entry,_,same,fits,remaining⟩:=pairFacts.2.2 used outcome
      have inserted:=GlobalAddressReuseInsertedHoles.take generation.reusePool addresses.intToPtrMap sizes initial.holes initial.pairwise choices.reuse choices.crossThread choices.poolIndex size align kind thread id sizeEq
      have newHoles:=inserted.2 used outcome cut partition.1
      have bound:=boundFacts.2 used outcome
      have cached:=GlobalAddressReuseResources.cache memory afterTake _ sizes afterTakeGood id allocation present sizeEq used.address uncached fresh positive cut partition placement bound newHoles
      cases clock : used.clockToAcquire with
      | some clock =>
        dsimp only
        cases clockResult with
        | error message => exact ⟨_,afterTakeGood⟩
        | ok unit =>
          cases unit
          try simp only [←initial.managed]
          change Post memory (match (afterTake.cacheAddress id used.address).outcome with
            | .ok _ => (show AddressStateResult AddressAssignment from ⟨(afterTake.cacheAddress id used.address).state,.ok (.ready used.address)⟩)
            | .error error => (show AddressStateResult AddressAssignment from ⟨(afterTake.cacheAddress id used.address).state,.error error⟩)).state sizes
          cases (afterTake.cacheAddress id used.address).outcome <;> exact ⟨_,cached.2⟩
      | none =>
        dsimp only
        try simp only [←initial.managed]
        exact returned memory afterTake id used.address sizes ⟨_,cached.2⟩ clockResult
end DuplicatePrefix.GlobalAddressReuseManagedResources
