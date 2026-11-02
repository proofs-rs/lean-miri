import duplicate_prefix.ManagedReusePointerFormation
import duplicate_prefix.ExecutionBernoulliNumericFormation
import duplicate_prefix.ExecutionIndexNumericFormation
import Miri.Input.EvalAllocationMachine
namespace DuplicatePrefix.ExecutionReuseAddressFormation
open Miri Miri.Input Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressReuseRawSelection
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def reuseDraw (before : EvalAllocationMachine.State Os R P H D O Aff B Host) (pool : ReusePool) :=
  EvalAllocationMachine.tape.put before (ExecutionBernoulliNumericFormation.consumed (EvalAllocationMachine.tape.get before)
    .addressReuse pool.addressReuseRate.toBits true)

def crossDraw (before : EvalAllocationMachine.State Os R P H D O Aff B Host) (pool : ReusePool) (cross : Bool) :=
  EvalAllocationMachine.tape.put (reuseDraw before pool) (ExecutionBernoulliNumericFormation.consumed
    (EvalAllocationMachine.tape.get (reuseDraw before pool)) .addressCrossThread pool.addressReuseCrossThreadRate.toBits cross)

def poolDraw (before : EvalAllocationMachine.State Os R P H D O Aff B Host) (pool : ReusePool) (cross : Bool)
    (begin stop selected : Nat) :=
  EvalAllocationMachine.tape.put (crossDraw before pool cross) (ExecutionIndexNumericFormation.consumed
    (EvalAllocationMachine.tape.get (crossDraw before pool cross)) .addressPool (stop-begin) (selected-begin))

/-- Actual production nonstack reuse takes three fresh tape events (reuse,
cross-thread and eligible-pool index). Raw support and stored-row constraints
supply each event; no choice/preparation/take success is assumed. -/
theorem address_without_race
    (pointers : PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (before : EvalAllocationMachine.State Os R P H D O Aff B Host)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : before.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (sizeEq : sizes id=entry.allocation.byteSize)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (valid : entry.allocation.align.pow2≤29) (cross : Bool)
    (raw : Input generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross)
    (reuseLegal : ExecutionBernoulliNumericFormation.Legal generation.reusePool.addressReuseRate.toBits true)
    (crossLegal : ExecutionBernoulliNumericFormation.Legal generation.reusePool.addressReuseCrossThreadRate.toBits cross)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross=true)
    (reuseInput : (EvalAllocationMachine.tape.get before).inputs[(EvalAllocationMachine.tape.get before).cursor]?=some (.boolean .addressReuse true))
    (crossInput : (EvalAllocationMachine.tape.get before).inputs[(EvalAllocationMachine.tape.get before).cursor+1]?=some (.boolean .addressCrossThread cross))
    (poolInput : (EvalAllocationMachine.tape.get before).inputs[(EvalAllocationMachine.tape.get before).cursor+2]?=
      some (.index .addressPool (raw.selected-(range raw.bucket entry.allocation.byteSize (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1)))
    (race : before.machine.dataRace=none) :
    let interval:=range raw.bucket entry.allocation.byteSize (UInt32.ofNat before.machine.threads.activeThread.toNat) cross
    let selected:=poolDraw before generation.reusePool cross interval.1 interval.2 raw.selected
    ExecutionAddressChoices.addrFromAllocId EvalAllocationMachine.tape pointers id (some .other) before=
      .ok (GlobalAddressRawReuseAssignment.used generation.reusePool entry.allocation.byteSize entry.allocation.align (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw).address
        (ManagedReusePointerFormation.after selected generation entry.allocation.byteSize entry.allocation.align id cross raw) := by
  dsimp only
  let interval:=range raw.bucket entry.allocation.byteSize (UInt32.ofNat before.machine.threads.activeThread.toNat) cross
  have within : raw.selected-interval.1<interval.2-interval.1 := by
    have lower:=raw.lower;have upper:=raw.upper;dsimp only [interval];omega
  have selectedEq : interval.1+(raw.selected-interval.1)=raw.selected := by have h:=raw.lower;dsimp only [interval];omega
  have first:=ExecutionBernoulliNumericFormation.bernoulli EvalAllocationMachine.tape before .addressReuse
    generation.reusePool.addressReuseRate.toBits true reuseLegal reuseInput
  have second:=ExecutionBernoulliNumericFormation.bernoulli EvalAllocationMachine.tape (reuseDraw before generation.reusePool) .addressCrossThread
    generation.reusePool.addressReuseCrossThreadRate.toBits cross crossLegal crossInput
  have third:=ExecutionIndexNumericFormation.index EvalAllocationMachine.tape (crossDraw before generation.reusePool cross)
    .addressPool (interval.2-interval.1) (raw.selected-interval.1) within poolInput
  have prepared:=GlobalAddressReuseRawSelection.prepare generation.reusePool entry.allocation.byteSize entry.allocation.align
    (UInt32.ofNat before.machine.threads.activeThread.toNat) cross raw valid reuseAllowed crossAllowed
  have live : before.machine.memory.isAllocLive id=true := by
    have any:=MemoryCopyBridge.live_any_of_present before.machine.memory id entry present
    simp only [MemoryState.isAllocLive,any,Bool.true_or]
  have metadata : before.machine.memory.getAllocInfo id=.ok
      ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
    simp only [MemoryState.getAllocInfo,present];rfl
  have unchanged : {before.machine.user.addresses with generation:=some {generation with reusePool:=generation.reusePool}}=
      before.machine.user.addresses := by
    change {before.machine.user.addresses with generation:=some generation}=before.machine.user.addresses
    rw [←initial.generationEq]
  have assigned:=ManagedReusePointerFormation.assign_without_race pointers (poolDraw before generation.reusePool cross interval.1 interval.2 raw.selected)
    generation sizes initial id entry present sizeEq uncached valid cross raw reuseAllowed crossAllowed race
  dsimp only [reuseDraw] at second
  dsimp only [crossDraw,reuseDraw] at third
  unfold ExecutionAddressChoices.addrFromAllocId
  unfold_internal ".ExecutionAddressChoices.rate"
  unfold_internal ".ExecutionAddressChoices.setAddresses"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,uncached,metadata,live,initial.managed,initial.generationEq,
    show (Miri.Memory.AllocationKind.liveData==Miri.Memory.AllocationKind.dead)=false from rfl,
    show (Miri.Memory.AllocationKind.liveData==Miri.Memory.AllocationKind.typeId)=false from rfl,
    show (AddressMemoryKind.other==AddressMemoryKind.stack)=false from rfl,
    beq_self_eq_true,bne_self_eq_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,Bool.false_and,Bool.false_or]
  simp only [first,↓reduceIte,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  simp only [second,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,prepared]
  dsimp only [EvalAllocationMachine.tape,interval] at third assigned selectedEq
  simp only [EvalAllocationMachine.tape,prepared,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  simp only [←initial.managed,unchanged]
  simp only [third,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,selectedEq]
  simpa only [GlobalAddressRawReuseAssignment.choices,reuseDraw,crossDraw,poolDraw,EvalAllocationMachine.tape] using assigned
end DuplicatePrefix.ExecutionReuseAddressFormation
