import duplicate_prefix.ManagedStackPointerFormation
import Miri.Input.EvalAllocationMachine
namespace DuplicatePrefix.ExecutionStackRootAddressFormation
open Miri Miri.Input Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressStackManagedFormation GlobalAddressAlignedBumpFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def chosen (before : EvalAllocationMachine.State Os R P H D O Aff B Host) (slack : Fin 16) :=
  EvalAllocationMachine.tape.put before (ExecutionAddressSlackFormation.consumed (EvalAllocationMachine.tape.get before) slack)

/-- The actual production tape provider and source stack address sampler consume
one legal supplied slack event. All allocator/range conditions are formed
before the callback; the callback's successful operation is the conclusion. -/
theorem address
    (pointers : PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (before : EvalAllocationMachine.State Os R P H D O Aff B Host)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : before.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (sizeEq : sizes id=entry.allocation.byteSize)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (valid : entry.allocation.align.pow2≤29) (slack : Fin 16)
    (supplied : (EvalAllocationMachine.tape.get before).inputs[(EvalAllocationMachine.tape.get before).cursor]?=
      some (.index .addressSlack slack.val))
    (room : Room generation.generator entry.allocation.byteSize entry.allocation.align slack) :
    ExecutionAddressChoices.addrFromAllocId EvalAllocationMachine.tape pointers id (some .stack) before=
      .ok (base generation.generator entry.allocation.align slack)
        (ManagedStackPointerFormation.after (chosen before slack) generation entry.allocation.byteSize entry.allocation.align id slack) := by
  have live : before.machine.memory.isAllocLive id=true := by
    have any:=MemoryCopyBridge.live_any_of_present before.machine.memory id entry present
    simp only [MemoryState.isAllocLive,any,Bool.true_or]
  have metadata : before.machine.memory.getAllocInfo id=.ok
      ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
    simp only [MemoryState.getAllocInfo,present]
    rfl
  have prepared : generation.reusePool.prepareTakeAddr false false entry.allocation.byteSize entry.allocation.align .stack
      (UInt32.ofNat before.machine.threads.activeThread.toNat)=⟨generation.reusePool,.ok none⟩ := by rfl
  have unchanged : {before.machine.user.addresses with generation:=some {generation with reusePool:=generation.reusePool}}=
      before.machine.user.addresses := by
    change {before.machine.user.addresses with generation:=some generation}=before.machine.user.addresses
    rw [←initial.generationEq]
  have selected:=ExecutionAddressSlackFormation.index EvalAllocationMachine.tape before slack supplied
  have assigned:=ManagedStackPointerFormation.assign pointers (chosen before slack) generation sizes initial id entry present sizeEq uncached valid slack room
  unfold ExecutionAddressChoices.addrFromAllocId
  unfold_internal ".ExecutionAddressChoices.setAddresses"
  unfold_internal ".ExecutionAddressChoices.slack"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,uncached,metadata,live,initial.managed,initial.generationEq,
    show (Miri.Memory.AllocationKind.liveData==Miri.Memory.AllocationKind.dead)=false from rfl,
    show (Miri.Memory.AllocationKind.liveData==Miri.Memory.AllocationKind.typeId)=false from rfl,
    beq_self_eq_true,bne_self_eq_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,Bool.false_and,Bool.false_or,
    prepared,unchanged]
  simp only [←initial.managed,unchanged]
  simp only [selected]
  simpa only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    slack.isLt,↓reduceDIte,chosen,choices] using assigned
/-- The configured production callback selects the just-created singleton
stack allocation and returns its concrete source pointer after real tape
sampling, generation and cache insertion. The allocation wrapper supplies the
singleton facts; no arbitrary callback is substituted. -/
theorem callback
    (pointers : PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalAllocationMachine.User Os R P H D O Aff B Host) P)
    (config : PlaceMachine.AllocationConfig MiriMemoryKind (EvalAllocationMachine.User Os R P H D O Aff B Host))
    (before : EvalAllocationMachine.State Os R P H D O Aff B Host)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tag : BorTag)
    (singleton : before.machine.memory.live=#[(id,entry)]) (stack : entry.kind=.stack)
    (sizeEq : sizes id=entry.allocation.byteSize)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (valid : entry.allocation.align.pow2≤29) (slack : Fin 16)
    (supplied : (EvalAllocationMachine.tape.get before).inputs[(EvalAllocationMachine.tape.get before).cursor]?=
      some (.index .addressSlack slack.val))
    (room : Room generation.generator entry.allocation.byteSize entry.allocation.align slack) :
    (EvalAllocationMachine.allocation pointers extras config).adjustRootAddress id tag before=
      .ok (Pointer.new (.concrete id tag) (Size.ofBytes (base generation.generator entry.allocation.align slack)))
        (ManagedStackPointerFormation.after (chosen before slack) generation entry.allocation.byteSize entry.allocation.align id slack) := by
  have present : before.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry) := by simp [singleton]
  have allocated:=address pointers before generation sizes initial id entry present sizeEq uncached valid slack supplied room
  have selectedLive : ((before.machine.memory.live.map fun (id,entry)=>(id,entry.kind,entry.allocation)).find? (fun row=>row.1==id))=
      some (id,.stack,entry.allocation) := by
    rw [Array.find?_map]
    change (before.machine.memory.live.find? (fun row=>row.1==id)).map (fun row=>(row.1,row.2.kind,row.2.allocation))=_
    simp only [present,Option.map_some,stack]
  unfold EvalAllocationMachine.allocation
  unfold_internal ".EvalAllocationMachine.addressKind"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,selectedLive]
  rw [allocated]
end DuplicatePrefix.ExecutionStackRootAddressFormation
