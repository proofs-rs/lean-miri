import duplicate_prefix.GlobalAddressLocalGc
namespace DuplicatePrefix.GlobalAddressLocalManaged
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressLocalRowFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.split false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem cache {K} (memory : MemoryState Provenance BorrowTree K) (state : GlobalAddressState) (sizes : AllocId→Size)
    (initial : Rows memory state.intToPtrMap sizes) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,entry)) (sizeEq : sizes id=entry.allocation.byteSize)
    (address : UInt64) : Rows memory (state.cacheAddress id address).state.intToPtrMap sizes := by
  unfold GlobalAddressState.cacheAddress
  dsimp only
  split
  · exact initial
  · split
    · exact initial
    · split
      · split <;> exact initial
      · split
        · rename_i bounded
          change Rows memory (state.intToPtrMap.insertIdx _ ⟨address,id⟩ bounded) sizes
          intro row member
          rcases Array.mem_insertIdx.mp member with same | prior
          · subst row
            exact ⟨entry,present,sizeEq⟩
          · exact initial row prior
        · exact initial

theorem returned {K} (memory : MemoryState Provenance BorrowTree K) (state : GlobalAddressState) (sizes : AllocId→Size)
    (initial : Rows memory state.intToPtrMap sizes) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,entry)) (sizeEq : sizes id=entry.allocation.byteSize)
    (address : UInt64) (clock : Except String Unit) :
    Rows memory (GlobalAddressState.completeAcquire (match (state.cacheAddress id address).outcome with
      | .ok _ => (show AddressStateResult AddressAssignment from ⟨(state.cacheAddress id address).state,.ok (.ready address)⟩)
      | .error error => (show AddressStateResult AddressAssignment from ⟨(state.cacheAddress id address).state,.error error⟩)) clock).state.intToPtrMap sizes := by
  cases (state.cacheAddress id address).outcome <;> exact cache memory state sizes initial id entry present sizeEq address

theorem returnedRaw {K} (memory : MemoryState Provenance BorrowTree K) (state : GlobalAddressState) (sizes : AllocId→Size)
    (initial : Rows memory state.intToPtrMap sizes) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,entry)) (sizeEq : sizes id=entry.allocation.byteSize)
    (address : UInt64) :
    Rows memory (match (state.cacheAddress id address).outcome with
      | .ok _ => (show AddressStateResult AddressAssignment from ⟨(state.cacheAddress id address).state,.ok (.ready address)⟩)
      | .error error => (show AddressStateResult AddressAssignment from ⟨(state.cacheAddress id address).state,.error error⟩)).state.intToPtrMap sizes := by
  cases (state.cacheAddress id address).outcome <;> exact cache memory state sizes initial id entry present sizeEq address

/-- Managed fresh/reuse assignment, including all error and clock outcomes,
introduces only the supplied actual local row. No liveness/global-kind branch
is supplied after the operation. -/
theorem complete {K} (memory : MemoryState Provenance BorrowTree K) (state : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : Rows memory state.intToPtrMap sizes)
    (managed : state.addressMode=.managed) (generationEq : state.generation=some generation)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,entry)) (sizeEq : sizes id=entry.allocation.byteSize)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none)
    (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) (choices : AddressRandomChoices)
    (clockResult : Except String Unit) :
    Rows memory (GlobalAddressState.completeAcquire (state.addrFromAllocId id
      (some (GlobalAddressAlignedManagedFormation.info entry.allocation.byteSize align kind thread)) choices) clockResult).state.intToPtrMap sizes := by
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,GlobalAddressAlignedManagedFormation.info,managed,generationEq,
    show (AllocationAddressKind.liveData==AllocationAddressKind.dead)=false from rfl,beq_iff_eq,reduceCtorEq,
    Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  cases outcome : (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex entry.allocation.byteSize align kind thread).outcome with
  | error error=>exact initial
  | ok optional=>
    try dsimp only
    cases optional with
    | none=>
      try dsimp only
      cases generated : (generation.generator.generate entry.allocation.byteSize align choices.slack).outcome with
      | error error=>exact initial
      | ok address=>
        try dsimp only
        simp only [←managed]
        let staged : GlobalAddressState := {state with generation:=some ⟨(generation.generator.generate entry.allocation.byteSize align choices.slack).state,
            if (generation.generator.generate entry.allocation.byteSize align choices.slack).state.getRemaining.start >
                (generation.generator.generate entry.allocation.byteSize align choices.slack).state.getRemaining.stop/2 then
              ((generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex entry.allocation.byteSize align kind thread).state).addressSpaceShortage
            else (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex entry.allocation.byteSize align kind thread).state⟩}
        exact returned memory staged sizes initial id entry present sizeEq address clockResult
    | some used=>
      try dsimp only
      simp only [←managed]
      let staged : GlobalAddressState := {state with generation:=some {generation with reusePool:=
        (generation.reusePool.takeAddr choices.reuse choices.crossThread choices.poolIndex entry.allocation.byteSize align kind thread).state}}
      cases clock : used.clockToAcquire with
      | none=>
        exact returned memory staged sizes initial id entry present sizeEq used.address clockResult
      | some vc=>
        cases clockResult with
        | error message=>exact initial
        | ok unit=>
          cases unit
          exact returnedRaw memory staged sizes initial id entry present sizeEq used.address
end DuplicatePrefix.GlobalAddressLocalManaged
