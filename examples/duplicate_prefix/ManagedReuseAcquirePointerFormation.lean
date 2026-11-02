import duplicate_prefix.ManagedReusePointerFormation
namespace DuplicatePrefix.ManagedReuseAcquirePointerFormation
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressRawReuseAssignment GlobalAddressReuseRawSelection
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def after (before : PointerMachine.State K U) (generation : AddressGenerationState)
    (size : Size) (align : Align) (id : AllocId) (cross : Bool)
    (raw : Input generation.reusePool size align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross)
    (global : Miri.Concurrency.GlobalState) (index : VectorIdx) (clocks : ThreadClockSet) : PointerMachine.State K U :=
  let assigned:=ManagedReusePointerFormation.after before generation size align id cross raw
  {assigned with machine:={assigned.machine with dataRace:=some {global with vectorClocks:=global.vectorClocks.set index.toNat {clocks with clock:=clocks.clock.join (raw.bucket[raw.selected]'raw.valid).clock}}}}

/-- Real cross-thread reuse joins the donor snapshot using actual active
thread metadata, then performs the source cache insertion. Raw list entries
and stored-row/thread facts replace every acquire-success premise. -/
theorem assign {K U} (h : PointerMachine.Hooks K U) (before : PointerMachine.State K U)
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
    (different : (raw.bucket[raw.selected]'raw.valid).thread≠UInt32.ofNat before.machine.threads.activeThread.toNat)
    (global : Miri.Concurrency.GlobalState) (race : before.machine.dataRace=some global)
    (index : VectorIdx) (extra : ThreadExtraState) (clocks : ThreadClockSet)
    (threadPresent : global.threadInfo[before.machine.threads.activeThread.toNat]?=some extra)
    (threadIndex : extra.vectorIndex=some index)
    (clockPresent : global.vectorClocks[index.toNat]?=some clocks) :
    PointerMachine.addrFromAllocId h id (some .other)
        (choices generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw) before=
      .ok (used generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw).address
        (after before generation entry.allocation.byteSize entry.allocation.align id cross raw global index clocks) := by
  have live : before.machine.memory.isAllocLive id=true := by
    have any:=MemoryCopyBridge.live_any_of_present before.machine.memory id entry present
    simp only [MemoryState.isAllocLive,any,Bool.true_or]
  have metadata : before.machine.memory.getAllocInfo id=.ok
      ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
    simp only [MemoryState.getAllocInfo,present];rfl
  have source:=GlobalAddressRawReuseAssignment.assign before.machine.memory before.machine.user.addresses generation sizes initial id
    entry.allocation.byteSize sizeEq entry.allocation.align valid (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw uncached reuseAllowed crossAllowed
  have actual:=source.1
  dsimp only [GlobalAddressAlignedManagedFormation.info] at actual
  have needed : (used generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw).clockToAcquire=
      some (raw.bucket[raw.selected]'raw.valid).clock := by simp only [used];simp only [beq_iff_eq,different,↓reduceIte]
  have acquired:=AddressReuseClockFormation.acquire global before.machine.threads index extra clocks (raw.bucket[raw.selected]'raw.valid).clock
    threadPresent threadIndex clockPresent
  unfold PointerMachine.addrFromAllocId
  unfold_internal ".PointerMachine.addresses"
  unfold_internal ".PointerMachine.finish"
  unfold_internal ".PointerMachine.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,uncached,metadata,live,initial.managed,
    show (AllocationKind.liveData==AllocationKind.dead)=false from rfl,
    show (AllocationKind.liveData==AllocationKind.typeId)=false from rfl,
    beq_self_eq_true,bne_self_eq_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,Bool.false_and,Bool.false_or,actual]
  simp only [pending,needed,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,race,acquired,source.2]
  rfl
end DuplicatePrefix.ManagedReuseAcquirePointerFormation
