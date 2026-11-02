import duplicate_prefix.AllocationEvalConfiguredFormation
import duplicate_prefix.AllocationEvalStackRootReady
namespace DuplicatePrefix.AllocationEvalStackFormation
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Concurrency
open Miri.TreeBorrows Miri.Interpreter Miri.Input
open GlobalAddressAlignedBumpFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Actual initialized managed stack allocation, including canonical root tag,
borrow tree, extras, legal tape consumption and source address/cache placement.
All semantic outcomes and inserted resources are derived from initial raw
storage/configuration/address resources and numeric room. -/
theorem allocate
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (onAccess : P→SyncObject.AccessKind→PlaceMachine.MachineM MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) Unit)
    (weakError : StoreBufferAllocError→StepError)
    (config : PlaceMachine.AllocationConfig MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host))
    (before : EvalCoreMachine.State Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (size : Size) (bytes : Array UInt8)
    (managed : config.nativeStorage=none) (diagnostic : config.diagnostic=fun _ _ _=>pure ())
    (provided : config.zeroedStorage size Align.ONE=some bytes)
    (length : bytes.size=size.bytes.toNat) (zero : ∀ i (h : i<bytes.size),bytes[i]=0)
    (emptyMemory : before.machine.memory={}) (enabled : before.machine.borrowTracker=some tracker)
    (initialGlobal : tracker.global=GlobalState.new) (race : before.machine.dataRace=none)
    (noBackend : before.machine.user.payload.payload.user.backend=.none)
    (noExtras : (((EvalCoreMachine.extras onAccess weakError).get before.machine.user).allocations.any
      (fun row=>row.1==AllocationLifecycleFormation.id))=false)
    (bounded : size.bytes≤config.maximumObjectSize.bytes)
    (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initialAddress : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes)
    (sizeEq : sizes AllocationLifecycleFormation.id=size)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==AllocationLifecycleFormation.id)=none)
    (slack : Fin 16)
    (supplied : (EvalAllocationMachine.tape.get before).inputs[(EvalAllocationMachine.tape.get before).cursor]?=
      some (.index .addressSlack slack.val))
    (room : Room generation.generator size Align.ONE slack) :
    ∃ allocation : Allocation Provenance Unit,
      AllocationPointerFormation.Ready allocation size ∧ allocation.align=Align.ONE ∧
      let extras:=EvalCoreMachine.extras onAccess weakError
      let final:=AllocationEvalStackRootReady.post onAccess weakError before tracker allocation generation slack
      ReallocationDriver.allocateConfigured (EvalAllocationMachine.allocation pointers extras config)
        size Align.ONE .stack .Zero before=
          .ok (Pointer.new (.concrete AllocationLifecycleFormation.id BorTag.one)
            (Size.ofBytes (base generation.generator Align.ONE slack))) final ∧
      final.machine.memory.live=#[
        (AllocationLifecycleFormation.id,⟨.stack,allocation.withExtra (BorrowTree.new BorTag.one size)⟩)] ∧
      final.machine.borrowTracker=some {tracker with global:=AllocationRootHookFormation.global AllocationLifecycleFormation.id} ∧
      final.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==AllocationLifecycleFormation.id)=
        some ⟨AllocationLifecycleFormation.id,base generation.generator Align.ONE slack⟩ ∧
      GlobalAddressReuseManagedResources.Post final.machine.memory final.machine.user.addresses sizes := by
  let extras:=EvalCoreMachine.extras onAccess weakError
  obtain ⟨allocation,ready,aligned,created,allocated⟩ := AllocationEvalConfiguredFormation.allocate pointers extras config before tracker size .stack bytes
    managed diagnostic provided length zero emptyMemory enabled initialGlobal race noBackend noExtras bounded
  have sameSize : sizes AllocationLifecycleFormation.id=allocation.byteSize := sizeEq.trans ready.1.symm
  have actual := AllocationEvalStackRootReady.root pointers onAccess weakError config before tracker allocation aligned generation sizes
    emptyMemory initialAddress sameSize uncached slack supplied (by rw [ready.1];exact room)
  refine ⟨allocation,ready,aligned,?_,?_,?_,actual.2.2.1,actual.2.1⟩
  · have callback:=actual.1
    dsimp only [AllocationEvalStackRootReady.pre] at callback
    dsimp only [extras] at allocated
    rw [allocated,callback,AllocationConfiguredFormation.finishRoot_ok]
  · rw [actual.2.2.2]
    change #[(AllocationLifecycleFormation.id,(⟨.stack,allocation.withExtra (BorrowTree.new BorTag.one allocation.byteSize)⟩ : LocalAllocation Provenance BorrowTree MiriMemoryKind))]=_
    rw [ready.1]
  · rfl
end DuplicatePrefix.AllocationEvalStackFormation
