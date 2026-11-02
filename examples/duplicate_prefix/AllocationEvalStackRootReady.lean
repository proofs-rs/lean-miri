import duplicate_prefix.AllocationEvalAddressTransport
namespace DuplicatePrefix.AllocationEvalStackRootReady
open Miri Miri.Input Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressAlignedBumpFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def pre
    (onAccess : P→SyncObject.AccessKind→PlaceMachine.MachineM MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) Unit)
    (weakError : StoreBufferAllocError→StepError)
    (before : EvalCoreMachine.State Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (allocation : Allocation Provenance Unit) :=
  AllocationConfiguredFormation.insertedState (EvalCoreMachine.extras onAccess weakError) before tracker .stack allocation

def post
    (onAccess : P→SyncObject.AccessKind→PlaceMachine.MachineM MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) Unit)
    (weakError : StoreBufferAllocError→StepError)
    (before : EvalCoreMachine.State Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (allocation : Allocation Provenance Unit) (generation : AddressGenerationState) (slack : Fin 16) :=
  ManagedStackPointerFormation.after (ExecutionStackRootAddressFormation.chosen (pre onAccess weakError before tracker allocation) slack)
    generation allocation.byteSize Align.ONE AllocationLifecycleFormation.id slack

/-- The real canonical callback's entire postcondition follows from INITIAL
address resources, tape and numeric room. Canonical source extras/root/live
installation supplies every pre-callback resource; none is a final premise. -/
theorem root
    (pointers : PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (onAccess : P→SyncObject.AccessKind→PlaceMachine.MachineM MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) Unit)
    (weakError : StoreBufferAllocError→StepError)
    (config : PlaceMachine.AllocationConfig MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host))
    (before : EvalCoreMachine.State Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (allocation : Allocation Provenance Unit) (aligned : allocation.align=Align.ONE)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (empty : before.machine.memory={})
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (sizeEq : sizes AllocationLifecycleFormation.id=allocation.byteSize)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==AllocationLifecycleFormation.id)=none)
    (slack : Fin 16)
    (supplied : (EvalAllocationMachine.tape.get before).inputs[(EvalAllocationMachine.tape.get before).cursor]?=
      some (.index .addressSlack slack.val))
    (room : Room generation.generator allocation.byteSize Align.ONE slack) :
    let extras:=EvalCoreMachine.extras onAccess weakError
    let final:=post onAccess weakError before tracker allocation generation slack
    (EvalAllocationMachine.allocation pointers extras config).adjustRootAddress AllocationLifecycleFormation.id BorTag.one
      (pre onAccess weakError before tracker allocation)=
        .ok (Pointer.new (.concrete AllocationLifecycleFormation.id BorTag.one)
          (Size.ofBytes (base generation.generator Align.ONE slack))) final ∧
    GlobalAddressReuseManagedResources.Post final.machine.memory final.machine.user.addresses sizes ∧
    final.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==AllocationLifecycleFormation.id)=
      some ⟨AllocationLifecycleFormation.id,base generation.generator Align.ONE slack⟩ ∧
    final.machine.memory=AllocationLifecycleFormation.inserted .stack allocation := by
  dsimp only
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    ⟨.stack,allocation.withExtra (BorrowTree.new BorTag.one allocation.byteSize)⟩
  have state:=AllocationEvalAddressTransport.resources onAccess weakError before tracker allocation generation sizes empty initial
  have singleton : (pre onAccess weakError before tracker allocation).machine.memory.live=#[(AllocationLifecycleFormation.id,entry)] := rfl
  have present : (pre onAccess weakError before tracker allocation).machine.memory.live.find? (fun row=>row.1==AllocationLifecycleFormation.id)=
      some (AllocationLifecycleFormation.id,entry) := by simp only [singleton];simp
  have valid : entry.allocation.align.pow2≤29 := by change allocation.align.pow2≤29;rw [aligned];decide
  have fresh : AllocationLifecycleFormation.id∉(pre onAccess weakError before tracker allocation).machine.user.addresses.intToPtrMap.toList.map InverseAddressEntry.allocId := by
    intro member
    obtain ⟨row,member,same⟩:=List.mem_map.mp member
    have frame:=AllocationEvalAddressTransport.frame onAccess weakError before tracker allocation
    have addressEq : (pre onAccess weakError before tracker allocation).machine.user.addresses=before.machine.user.addresses := frame.2.1
    have old : row∈before.machine.user.addresses.intToPtrMap := by
      rw [←addressEq]
      simpa using member
    have live:=initial.resources.recurring.live.1 row old
    dsimp only at live
    rw [empty] at live
    simpa [MemoryState.isAllocLive,KeyedArray.contains,KeyedArray.empty] using live
  have selectedRoom : Room generation.generator entry.allocation.byteSize entry.allocation.align slack := by
    change Room generation.generator allocation.byteSize allocation.align slack
    simpa only [aligned] using room
  have actual:=ExecutionStackRootAddressFormation.callback pointers (EvalCoreMachine.extras onAccess weakError) config
    (pre onAccess weakError before tracker allocation) generation sizes state AllocationLifecycleFormation.id entry BorTag.one
    singleton rfl sizeEq uncached valid slack supplied selectedRoom
  have facts:=ExecutionStackRootAddressResources.resources (pre onAccess weakError before tracker allocation) generation sizes state
    AllocationLifecycleFormation.id entry present sizeEq uncached fresh valid slack selectedRoom
  dsimp only [entry,Allocation.withExtra] at actual facts
  simp only [aligned] at actual facts
  exact ⟨actual,facts.2.1,facts.2.2,facts.1⟩
end DuplicatePrefix.AllocationEvalStackRootReady
