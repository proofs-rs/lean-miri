import duplicate_prefix.GlobalAddressRawReuseAssignment
import duplicate_prefix.AddressReuseClockFormation
namespace DuplicatePrefix.ManagedReusePointerFormation
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressRawReuseAssignment GlobalAddressReuseRawSelection
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def after (before : PointerMachine.State K U) (generation : AddressGenerationState)
    (size : Size) (align : Align) (id : AllocId) (cross : Bool)
    (raw : Input generation.reusePool size align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross) : PointerMachine.State K U :=
  {before with machine:={before.machine with user:={before.machine.user with addresses:=
    ((staged before.machine.user.addresses generation size align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw).cacheAddress id
      (used generation.reusePool size align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw).address).state}}}

/-- Actual pointer assignment consumes a source-selected reusable hole. When
race tracking is disabled, source acquireRequired correctly skips the clock
hook before caching; this is not a fabricated successful acquire callback. -/
theorem assign_without_race {K U} (h : PointerMachine.Hooks K U) (before : PointerMachine.State K U)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : before.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (sizeEq : sizes id=entry.allocation.byteSize)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (valid : entry.allocation.align.pow2≤29) (cross : Bool)
    (raw : Input generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross=true)
    (race : before.machine.dataRace=none) :
    PointerMachine.addrFromAllocId h id (some .other)
        (choices generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw) before=
      .ok (used generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw).address
        (after before generation entry.allocation.byteSize entry.allocation.align id cross raw) := by
  have live : before.machine.memory.isAllocLive id=true := by
    have any:=MemoryCopyBridge.live_any_of_present before.machine.memory id entry present
    simp only [MemoryState.isAllocLive,any,Bool.true_or]
  have metadata : before.machine.memory.getAllocInfo id=.ok
      ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
    simp only [MemoryState.getAllocInfo,present]
    rfl
  have source:=GlobalAddressRawReuseAssignment.assign before.machine.memory before.machine.user.addresses generation sizes initial id
    entry.allocation.byteSize sizeEq entry.allocation.align valid (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw uncached reuseAllowed crossAllowed
  have actual:=source.1
  dsimp only [GlobalAddressAlignedManagedFormation.info] at actual
  unfold PointerMachine.addrFromAllocId
  unfold_internal ".PointerMachine.addresses"
  unfold_internal ".PointerMachine.finish"
  unfold_internal ".PointerMachine.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,uncached,metadata,live,initial.managed,
    show (AllocationKind.liveData==AllocationKind.dead)=false from rfl,
    show (AllocationKind.liveData==AllocationKind.typeId)=false from rfl,
    beq_self_eq_true,bne_self_eq_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,Bool.false_and,Bool.false_or,actual]
  cases clock : (used generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw).clockToAcquire with
  | none=>
    simp only [pending,clock,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
    rfl
  | some donor=>
    simp only [pending,clock,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,race,source.2]
    simp only [after,race]
end DuplicatePrefix.ManagedReusePointerFormation
