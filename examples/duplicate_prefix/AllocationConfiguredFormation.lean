import duplicate_prefix.AllocationPointerFormation
import Miri.Interpreter.ReallocationDriver
namespace DuplicatePrefix.AllocationConfiguredFormation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open AllocationLifecycleFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def insertedState (extras : MemoryExtras.Hooks K (PointerMachine.User U) P)
    (before : MachineHooks.State K (PointerMachine.User U)) (tracker : MachineHooks.BorrowState)
    (kind : MemoryKind K) (allocation : Allocation Provenance Unit) :=
  {before with machine:=(synchronize (inserted kind allocation)
    (AllocationLifecycleFormation.initialized extras before.machine tracker))}

def finishRoot (before : MachineHooks.State K (PointerMachine.User U))
    (result : EStateM.Result StepError (MachineHooks.State K (PointerMachine.User U)) (Pointer Provenance)) :
    EStateM.Result StepError (MachineHooks.State K (PointerMachine.User U)) (Pointer Provenance) :=
  EStateM.tryCatch (fun _=>result) (fun error=>EStateM.throw error) before

theorem finishRoot_ok (before : MachineHooks.State K (PointerMachine.User U)) (pointer : Pointer Provenance)
    (next : MachineHooks.State K (PointerMachine.User U)) : finishRoot before (.ok pointer next)=.ok pointer next := rfl

/-- Production allocateConfigured reaches its actual address callback after
real backing creation, ID reservation, root-tag/tree/extras initialization and
live insertion. Managed storage and disabled diagnostics are explicit policies;
the root callback's success or error is not a premise. -/
theorem allocate {K U P : Type} [DecidableEq K]
    (config : PlaceMachine.AllocationConfig K (PointerMachine.User U))
    (extras : MemoryExtras.Hooks K (PointerMachine.User U) P)
    (before : MachineHooks.State K (PointerMachine.User U)) (tracker : MachineHooks.BorrowState)
    (size : Size) (kind : MemoryKind K) (bytes : Array UInt8)
    (managed : config.nativeStorage=none)
    (diagnostic : config.diagnostic=fun _ _ _=>pure ())
    (tail : config.allocationTail=fun id _ _=>MemoryExtras.initAllocation extras id false)
    (provided : config.zeroedStorage size Align.ONE=some bytes)
    (length : bytes.size=size.bytes.toNat) (zero : ∀ i (h : i<bytes.size),bytes[i]=0)
    (emptyMemory : before.machine.memory={}) (enabled : before.machine.borrowTracker=some tracker)
    (initial : tracker.global=GlobalState.new) (race : before.machine.dataRace=none)
    (noExtras : ((extras.get before.machine.user).allocations.any (fun row=>row.1==AllocationLifecycleFormation.id))=false)
    (bounded : size.bytes≤config.maximumObjectSize.bytes) :
    ∃ allocation : Allocation Provenance Unit,
      AllocationPointerFormation.Ready allocation size ∧
      ReallocationDriver.allocateConfigured config size Align.ONE kind .Zero before=
        finishRoot before (config.adjustRootAddress AllocationLifecycleFormation.id BorTag.one
          (insertedState extras before tracker kind allocation)) := by
  obtain ⟨allocation,created,ready⟩ := AllocationPointerFormation.backing size bytes config.zeroedStorage provided length zero
  have hook := AllocationRootHookFormation.init_extra extras (synchronize reservedMemory before.machine) tracker
    AllocationLifecycleFormation.id size Align.ONE enabled initial race noExtras
  have notLarge : ¬size.bytes>config.maximumObjectSize.bytes := by
    have b:=UInt64.le_iff_toNat_le.mp bounded
    intro greater
    have g:=UInt64.lt_iff_toNat_lt.mp greater
    omega
  have native : allocation.nativeBuffer=none := ready.2.2.2.2.2.2.2
  have cached : (AllocationRootHookFormation.global AllocationLifecycleFormation.id).rootTag? AllocationLifecycleFormation.id=some BorTag.one := by
    simp [AllocationRootHookFormation.global,GlobalState.rootTag?]
  refine ⟨allocation,ready,?_⟩
  unfold ReallocationDriver.allocateConfigured
  unfold_internal ".ReallocationDriver.machineAction"
  simp only [managed,created,notLarge,↓reduceIte,diagnostic,tail,emptyMemory,reserve,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  dsimp only [synchronize] at hook
  rw [hook]
  simp only [AllocationLifecycleFormation.initialized,AllocationRootHookFormation.rooted,MemoryExtras.putAllocation,
    cached,native,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  simp only [finishRoot,EStateM.tryCatch,EStateM.throw,insertedState,synchronize,AllocationLifecycleFormation.initialized,
    AllocationRootHookFormation.rooted,MemoryExtras.putAllocation,inserted,ready.1,reserved_live,Array.push_empty]
end DuplicatePrefix.AllocationConfiguredFormation
