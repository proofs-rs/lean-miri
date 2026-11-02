import duplicate_prefix.GlobalAddressInsertedMemoryResources
namespace DuplicatePrefix.GlobalAddressPhysicalRowHistory
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressReuseResources GlobalAddressReuseManagedResources GeneralBorrowGcMachineMemoryRetentionLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Address-operation histories over actual raw data/MEMORY/STATIC size
resources. Allocation consumes a physical live row already present in memory;
reserve/storage/initialization and physicalCaller formation are separate
contracts. This extension additionally admits actual fresh local-row insertion,
without assuming the resulting address resources. Numeric headroom and coherent source lookup inputs constrain each
operation, never its success or final geometric resources. -/
inductive History {K : Type} [DecidableEq K] (sizes : AllocId → Size) :
    MemoryState Provenance BorrowTree K → GlobalAddressState → Prop where
  | seed (memory : MemoryState Provenance BorrowTree K) (mode : ProvenanceMode) (start stop : UInt64)
      (config : AddressReuseConfig) (positive : start≠0)
      (reuse : (Float.le 0.0 config.addressReuseRate && Float.le config.addressReuseRate 1.0)=true)
      (cross : (Float.le 0.0 config.addressReuseCrossThreadRate && Float.le config.addressReuseCrossThreadRate 1.0)=true)
      (addresses : GlobalAddressState) (actual : GlobalAddressState.new mode .managed start stop config=.ok addresses) : History sizes memory addresses
  | insert {memory addresses} (before : History sizes memory addresses)
      (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
      (fresh : id∉addresses.intToPtrMap.toList.map InverseAddressEntry.allocId) :
      History sizes (source_range_insert_live memory id entry) addresses
  | allocate {memory addresses} (before : History sizes memory addresses) (generation : AddressGenerationState)
      (generationEq : addresses.generation=some generation) (id : AllocId) (allocation : LocalAllocation Provenance BorrowTree K)
      (present : memory.live.find? (fun row=>row.1==id)=some (id,allocation)) (sizeEq : sizes id=allocation.allocation.byteSize)
      (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
      (fresh : id∉addresses.intToPtrMap.toList.map InverseAddressEntry.allocId)
      (align : Align) (valid : align.pow2≤29) (kind : AddressMemoryKind) (thread : AddressThreadId)
      (choices : AddressRandomChoices) (room : GlobalAddressAlignedBumpFormation.Room generation.generator allocation.allocation.byteSize align choices.slack)
      (clockResult : Except String Unit) :
      History sizes memory (GlobalAddressState.completeAcquire (addresses.addrFromAllocId id
        (some (GlobalAddressAlignedManagedFormation.info allocation.allocation.byteSize align kind thread)) choices) clockResult).state
  | free {memory addresses} (before : History sizes memory addresses) (id : AllocId) (address : UInt64)
      (nonzero : address≠0) (size : Size) (sizeEq : sizes id=size) (position : Nat) (valid : position<addresses.intToPtrMap.size)
      (row : addresses.intToPtrMap[position]?=some ⟨address,id⟩)
      (cached : addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,address⟩)
      (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) (choice : Bool) (clock : Unit → VClock) :
      History sizes (source_memory_remove_live memory id).1 (addresses.freeAllocId id size align kind thread choice clock).state
  | expose {memory addresses} (before : History sizes memory addresses) (provenance : Provenance)
      (tracking : Bool) (hook : Option (Except String Unit)) :
      History sizes memory (addresses.exposeProvenance provenance
        (match provenance with | .wildcard=>none | .concrete id _=>some (memory.isAllocLive id)) tracking hook).state
  | gc (views : MachineGCRoots.Views User Os R Payload H D O) (lens : FunctionPointers.AddressLens User AddressPayload)
      (state : MachineHooks.State K User) (before : History sizes state.machine.memory (lens.get state.machine.user).addresses) :
      History sizes (stateOf (MachineGCRoots.run views lens state)).machine.memory
        (lens.get (stateOf (MachineGCRoots.run views lens state)).machine.user).addresses

/-- Arbitrary finite recurrence from actual initialization. Every permitted
prefix retains live inverse identities, order/uniqueness, actual size suppliers,
physical nonoverlap, and pairwise reusable holes available after new allocation.
Error outcomes remain errors; this theorem does not certify MIR execution. -/
theorem invariant {K : Type} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : History sizes memory addresses) : Post memory addresses sizes := by
  induction history with
  | seed memory mode start stop config positive reuse cross addresses actual =>
    obtain ⟨other,generation,source,good⟩:=GlobalAddressReuseLifecycleResources.seed memory sizes mode start stop config positive reuse cross
    have same : other=addresses:=Except.ok.inj (source.symm.trans actual)
    subst other
    exact ⟨generation,good⟩
  | insert before id entry fresh ih =>
    obtain ⟨generation,good⟩:=ih
    exact ⟨generation,GlobalAddressInsertedMemoryResources.insert _ _ generation sizes good id entry fresh⟩
  | allocate before generation generationEq id allocation present sizeEq uncached fresh align valid kind thread choices room clockResult ih =>
    obtain ⟨previous,good⟩:=ih
    have same : previous=generation:=Option.some.inj (good.generationEq.symm.trans generationEq)
    subst previous
    exact GlobalAddressReuseManagedResources.complete _ _ generation sizes good id allocation present sizeEq uncached fresh align valid kind thread choices room clockResult
  | free before id address nonzero size sizeEq position valid row cached align kind thread choice clock ih =>
    obtain ⟨generation,good⟩:=ih
    exact ⟨_,GlobalAddressReuseLifecycleResources.free _ _ generation sizes good id address nonzero size sizeEq position valid row cached align kind thread choice clock⟩
  | expose before provenance tracking hook ih =>
    obtain ⟨generation,good⟩:=ih
    exact ⟨_,GlobalAddressReuseFrameResources.expose _ _ generation sizes good provenance tracking hook⟩
  | gc views lens state before ih =>
    obtain ⟨generation,good⟩:=ih
    exact ⟨_,GlobalAddressReuseFrameResources.gc views lens state generation sizes good⟩
/-- A fresh physical local row is inserted and its address acquired in one
source step. The live-row lookup required by address acquisition is derived
from actual insertion, rather than exposed as a final premise. Allocation
storage and concrete init/root hooks remain outside this row-history layer. -/
theorem insert_allocate {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (before : History sizes memory addresses) (generation : AddressGenerationState)
    (generationEq : addresses.generation=some generation) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (sizeEq : sizes id=entry.allocation.byteSize)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (fresh : id∉addresses.intToPtrMap.toList.map InverseAddressEntry.allocId)
    (align : Align) (valid : align.pow2≤29) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (choices : AddressRandomChoices)
    (room : GlobalAddressAlignedBumpFormation.Room generation.generator entry.allocation.byteSize align choices.slack)
    (clockResult : Except String Unit) :
    History sizes (source_range_insert_live memory id entry)
      (GlobalAddressState.completeAcquire (addresses.addrFromAllocId id
        (some (GlobalAddressAlignedManagedFormation.info entry.allocation.byteSize align kind thread)) choices) clockResult).state :=
  .allocate (.insert before id entry fresh) generation generationEq id entry
    (MemoryCopyBridge.live_lookup_replaced memory id entry) sizeEq uncached fresh align valid kind thread choices room clockResult

end DuplicatePrefix.GlobalAddressPhysicalRowHistory
