import duplicate_prefix.ExecutionAddressSlackFormation
import duplicate_prefix.GlobalAddressBaseCacheFormation
namespace DuplicatePrefix.ManagedStackPointerFormation
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressStackManagedFormation GlobalAddressAlignedBumpFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def addresses (before : GlobalAddressState) (generation : AddressGenerationState) (size : Size) (align : Align)
    (id : AllocId) (slack : Fin 16) : GlobalAddressState :=
  ((ready before generation size align slack).cacheAddress id (base generation.generator align slack)).state

def after (before : PointerMachine.State K U) (generation : AddressGenerationState)
    (size : Size) (align : Align) (id : AllocId) (slack : Fin 16) : PointerMachine.State K U :=
  {before with machine:={before.machine with user:={before.machine.user with
    addresses:=addresses before.machine.user.addresses generation size align id slack}}}

/-- Source stack assignment goes through the actual pointer-machine metadata
lookup and managed address algorithm. External address/clock hooks are not
called on this source branch. -/
theorem assign {K U} (h : PointerMachine.Hooks K U) (before : PointerMachine.State K U)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : before.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (sizeEq : sizes id=entry.allocation.byteSize)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (valid : entry.allocation.align.pow2≤29) (slack : Fin 16)
    (room : Room generation.generator entry.allocation.byteSize entry.allocation.align slack) :
    PointerMachine.addrFromAllocId h id (some .stack) (choices slack) before=
      .ok (base generation.generator entry.allocation.align slack)
        (after before generation entry.allocation.byteSize entry.allocation.align id slack) := by
  have live : before.machine.memory.isAllocLive id=true := by
    have any:=MemoryCopyBridge.live_any_of_present before.machine.memory id entry present
    simp only [MemoryState.isAllocLive,any,Bool.true_or]
  have metadata : before.machine.memory.getAllocInfo id=.ok
      ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
    simp only [MemoryState.getAllocInfo,present]
    rfl
  have source:=(GlobalAddressStackManagedFormation.source before.machine.user.addresses generation sizes
    initial.resources.apart initial.frontier initial.managed initial.generationEq initial.cursor id
    entry.allocation.byteSize sizeEq entry.allocation.align valid uncached
    (UInt32.ofNat before.machine.threads.activeThread.toNat) slack room).1
  unfold PointerMachine.addrFromAllocId
  unfold_internal ".PointerMachine.addresses"
  unfold_internal ".PointerMachine.finish"
  unfold_internal ".PointerMachine.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,uncached,metadata,live,initial.managed,
    show (AllocationKind.liveData==AllocationKind.dead)=false from rfl,
    show (AllocationKind.liveData==AllocationKind.typeId)=false from rfl,
    beq_self_eq_true,bne_self_eq_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,Bool.false_and,Bool.false_or]
  dsimp only [info] at source
  simp only [source,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  rfl
end DuplicatePrefix.ManagedStackPointerFormation
