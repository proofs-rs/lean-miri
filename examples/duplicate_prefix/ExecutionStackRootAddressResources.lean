import duplicate_prefix.ExecutionStackRootAddressFormation
namespace DuplicatePrefix.ExecutionStackRootAddressResources
open Miri Miri.Input Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressStackManagedFormation GlobalAddressAlignedBumpFormation ExecutionStackRootAddressFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Source cache insertion stores the selected base even on its partial-error
paths. Successful generation/inverse insertion is proved separately by the
production callback, not required by this storage theorem. -/
theorem cached (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none) :
    (state.cacheAddress id address).state.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,address⟩ := by
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.insertBase"
  simp only [uncached,Option.map_none]
  split
  · exact GlobalAddressBaseCacheFormation.base_insert_same _ _ _
  · split
    · split <;> exact GlobalAddressBaseCacheFormation.base_insert_same _ _ _
    · split <;> exact GlobalAddressBaseCacheFormation.base_insert_same _ _ _

/-- The actual sampler/callback output retains physical storage and has the
full managed range/reuse resource invariant together with the chosen cache
entry. All postconditions derive from source actions and raw resources. -/
theorem resources
    (before : EvalAllocationMachine.State Os R P H D O Aff B Host)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : before.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (sizeEq : sizes id=entry.allocation.byteSize)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (fresh : id∉before.machine.user.addresses.intToPtrMap.toList.map InverseAddressEntry.allocId)
    (valid : entry.allocation.align.pow2≤29) (slack : Fin 16)
    (room : Room generation.generator entry.allocation.byteSize entry.allocation.align slack) :
    let final := ManagedStackPointerFormation.after (chosen before slack) generation entry.allocation.byteSize entry.allocation.align id slack
    final.machine.memory=before.machine.memory ∧
    GlobalAddressReuseManagedResources.Post final.machine.memory final.machine.user.addresses sizes ∧
    final.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=
      some ⟨id,base generation.generator entry.allocation.align slack⟩ := by
  dsimp only
  have source:=(GlobalAddressStackManagedFormation.source before.machine.user.addresses generation sizes
    initial.resources.apart initial.frontier initial.managed initial.generationEq initial.cursor id
    entry.allocation.byteSize sizeEq entry.allocation.align valid uncached
    (UInt32.ofNat before.machine.threads.activeThread.toNat) slack room).1
  have good:=GlobalAddressReuseManagedResources.complete before.machine.memory before.machine.user.addresses generation sizes initial
    id entry present sizeEq uncached fresh entry.allocation.align valid .stack (UInt32.ofNat before.machine.threads.activeThread.toNat)
    (choices slack) room (.ok ())
  dsimp only [GlobalAddressAlignedManagedFormation.info] at good
  dsimp only [info] at source
  simp only [source,GlobalAddressState.completeAcquire] at good
  refine ⟨rfl,good,?_⟩
  exact cached (ready before.machine.user.addresses generation entry.allocation.byteSize entry.allocation.align slack)
    id (base generation.generator entry.allocation.align slack) uncached
end DuplicatePrefix.ExecutionStackRootAddressResources
