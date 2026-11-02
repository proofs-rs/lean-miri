import duplicate_prefix.AllocationConfiguredFormation
import duplicate_prefix.AllocationEvalRootHookFormation
namespace DuplicatePrefix.AllocationEvalConfiguredFormation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.Input
open AllocationLifecycleFormation AllocationConfiguredFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Canonical Eval backend selection and actual production allocation prefix.
Only initial backend/registry/storage/numeric facts are required; the address
callback executes after the derived root/tree/global/live installation. -/
theorem allocate
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalBackendMachine.User Os R P H D O Aff B Host) P)
    (base : PlaceMachine.AllocationConfig MiriMemoryKind (EvalBackendMachine.User Os R P H D O Aff B Host))
    (before : EvalBackendMachine.State Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (size : Size) (kind : MemoryKind MiriMemoryKind) (bytes : Array UInt8)
    (managed : base.nativeStorage=none) (diagnostic : base.diagnostic=fun _ _ _=>pure ())
    (provided : base.zeroedStorage size Align.ONE=some bytes)
    (length : bytes.size=size.bytes.toNat) (zero : ∀ i (h : i<bytes.size),bytes[i]=0)
    (emptyMemory : before.machine.memory={}) (enabled : before.machine.borrowTracker=some tracker)
    (initial : tracker.global=GlobalState.new) (race : before.machine.dataRace=none)
    (noBackend : before.machine.user.payload.payload.user.backend=.none)
    (noExtras : ((extras.get before.machine.user).allocations.any (fun row=>row.1==AllocationLifecycleFormation.id))=false)
    (bounded : size.bytes≤base.maximumObjectSize.bytes) :
    let config:=EvalAllocationMachine.allocation pointers extras base
    ∃ allocation : Allocation Provenance Unit,
      AllocationPointerFormation.Ready allocation size ∧ allocation.align=Align.ONE ∧
      Allocation.tryNew size Align.ONE .Zero base.zeroedStorage=.ok allocation ∧
      ReallocationDriver.allocateConfigured config size Align.ONE kind .Zero before=
        finishRoot before (config.adjustRootAddress AllocationLifecycleFormation.id BorTag.one
          (insertedState extras before tracker kind allocation)) := by
  let config:=EvalAllocationMachine.allocation pointers extras base
  have managedConfig : (EvalAllocationMachine.allocation pointers extras base).nativeStorage=none := managed
  have diagnosticConfig : (EvalAllocationMachine.allocation pointers extras base).diagnostic=fun _ _ _=>pure () := diagnostic
  obtain ⟨allocation,created,ready⟩ := AllocationPointerFormation.backing size bytes config.zeroedStorage provided length zero
  have createdConfig : Allocation.tryNew size Align.ONE .Zero (EvalAllocationMachine.allocation pointers extras base).zeroedStorage=.ok allocation := created
  have hook := AllocationEvalRootHookFormation.init_extra pointers extras base (synchronize reservedMemory before.machine) tracker
    AllocationLifecycleFormation.id size Align.ONE enabled initial race noBackend noExtras
  have notLarge : ¬size.bytes>(EvalAllocationMachine.allocation pointers extras base).maximumObjectSize.bytes := by
    change ¬size.bytes>base.maximumObjectSize.bytes
    have b:=UInt64.le_iff_toNat_le.mp bounded
    intro greater
    have g:=UInt64.lt_iff_toNat_lt.mp greater
    omega
  have native : allocation.nativeBuffer=none := ready.2.2.2.2.2.2.2
  have cached : (AllocationRootHookFormation.global AllocationLifecycleFormation.id).rootTag? AllocationLifecycleFormation.id=some BorTag.one := by
    simp [AllocationRootHookFormation.global,GlobalState.rootTag?]
  obtain ⟨other,otherCreated,_,_,_,_,_,aligned,_⟩ :=
    AllocationStorageFormation.create (Prov:=Provenance) size .Zero bytes base.zeroedStorage provided length zero
  have same : allocation=other := Except.ok.inj (created.symm.trans otherCreated)
  subst other
  refine ⟨allocation,ready,aligned,created,?_⟩
  unfold ReallocationDriver.allocateConfigured
  unfold_internal ".ReallocationDriver.machineAction"
  simp only [managedConfig,createdConfig,notLarge,↓reduceIte,diagnosticConfig,emptyMemory,reserve,
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
end DuplicatePrefix.AllocationEvalConfiguredFormation
