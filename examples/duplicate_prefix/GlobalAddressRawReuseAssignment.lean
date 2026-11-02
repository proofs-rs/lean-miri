import duplicate_prefix.GlobalAddressReuseRawSelection
namespace DuplicatePrefix.GlobalAddressRawReuseAssignment
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressReuseRawSelection
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def used (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId) (cross : Bool)
    (raw : Input pool size align thread cross) : ReusedAddress :=
  ⟨(raw.bucket[raw.selected]'raw.valid).address,
    if (raw.bucket[raw.selected]'raw.valid).thread==thread then none else some (raw.bucket[raw.selected]'raw.valid).clock⟩

def choices (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId) (cross : Bool)
    (raw : Input pool size align thread cross) : AddressRandomChoices := ⟨true,cross,raw.selected,⟨0,by decide⟩⟩

def staged (addresses : GlobalAddressState) (generation : AddressGenerationState) (size : Size) (align : Align)
    (thread : AddressThreadId) (cross : Bool) (raw : Input generation.reusePool size align thread cross) : GlobalAddressState :=
  {addresses with generation:=some {generation with reusePool:=output generation.reusePool size align thread cross raw}}

def pending (addresses : GlobalAddressState) (id : AllocId) (used : ReusedAddress) : AddressStateResult AddressAssignment :=
  match used.clockToAcquire with
  | some clock=>⟨addresses,.ok (.acquireRequired id used.address clock)⟩
  | none=>⟨(addresses.cacheAddress id used.address).state,.ok (.ready used.address)⟩

/-- Actual stored-hole geometry and raw selected-row constraints derive the
production assignment and cache success; cross-thread clock acquisition stays
at its actual caller boundary. No assignment/take/cache success is assumed. -/
theorem assign {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State memory addresses generation sizes)
    (id : AllocId) (size : Size) (sizeEq : sizes id=size) (align : Align) (valid : align.pow2≤29)
    (thread : AddressThreadId) (cross : Bool) (raw : Input generation.reusePool size align thread cross)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross=true) :
    addresses.addrFromAllocId id (some (GlobalAddressAlignedManagedFormation.info size align .other thread))
        (choices generation.reusePool size align thread cross raw)=
      pending (staged addresses generation size align thread cross raw) id (used generation.reusePool size align thread cross raw) ∧
    ((staged addresses generation size align thread cross raw).cacheAddress id
      (used generation.reusePool size align thread cross raw).address).outcome=.ok () := by
  have taken:=GlobalAddressReuseRawSelection.take generation.reusePool size align thread cross raw valid reuseAllowed crossAllowed
  have takeOutcome : (generation.reusePool.takeAddr true cross raw.selected size align .other thread).outcome=
      .ok (some (used generation.reusePool size align thread cross raw)) := congrArg ReusePoolResult.outcome taken
  have holes:=GlobalAddressReuseHoleGeometry.take_separated generation.reusePool addresses.intToPtrMap sizes initial.holes
    initial.resources.recurring.ordered id size sizeEq true cross raw.selected align .other thread
  obtain ⟨positive,cut,partition,placement⟩:=holes.2 _ takeOutcome
  have cached:=(GlobalAddressExposureFormation.cache_ordered_completed (staged addresses generation size align thread cross raw)
    id (used generation.reusePool size align thread cross raw).address uncached positive cut partition initial.resources.recurring.ordered).1
  refine ⟨?_,cached⟩
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,GlobalAddressAlignedManagedFormation.info,initial.managed,initial.generationEq,
    show (AllocationAddressKind.liveData==AllocationAddressKind.dead)=false from rfl,beq_iff_eq,reduceCtorEq,
    Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,choices,taken]
  simp only [←initial.managed]
  dsimp only [staged,used] at cached
  simp only [pending,staged,used,beq_iff_eq]
  cases clock : (if (raw.bucket[raw.selected]'raw.valid).thread=thread then none else some (raw.bucket[raw.selected]'raw.valid).clock) with
  | some donor=>simp only [clock]
  | none=>simp only [clock,cached]
end DuplicatePrefix.GlobalAddressRawReuseAssignment
