import duplicate_prefix.AllocationConfiguredFormation
import duplicate_prefix.ExecutionStackRootAddressResources
import Miri.Input.EvalCoreMachine
namespace DuplicatePrefix.AllocationEvalAddressTransport
open Miri Miri.Input Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- No addressed/exposed allocation exists over empty source memory. Hence
installing the first physical allocation cannot invalidate previous size or
liveness suppliers; geometry/generation/reuse facts stay unchanged. -/
theorem empty_memory {K} (addresses : GlobalAddressState) (generation : AddressGenerationState) (sizes : AllocId→Size)
    (initial : GlobalAddressReuseResources.State ({} : MemoryState Provenance BorrowTree K) addresses generation sizes)
    (memory : MemoryState Provenance BorrowTree K) :
    GlobalAddressReuseResources.State memory addresses generation sizes := by
  have noLive : ∀id,( {} : MemoryState Provenance BorrowTree K).isAllocLive id=false := by
    intro id
    simp [MemoryState.isAllocLive,KeyedArray.contains,KeyedArray.empty]
  have noInverse : ∀row∈addresses.intToPtrMap,False := by
    intro row member
    have live:=initial.resources.recurring.live.1 row member
    dsimp only at live
    rw [noLive] at live
    cases live
  have noExposed : ∀id∈addresses.exposed,False := by
    intro id member
    have live:=initial.resources.recurring.live.2 id member
    dsimp only at live
    rw [noLive] at live
    cases live
  exact ⟨⟨⟨⟨fun row member=>False.elim (noInverse row member),fun id member=>False.elim (noExposed id member)⟩,
    initial.resources.recurring.ordered,initial.resources.recurring.unique⟩,initial.resources.apart,
    fun row member=>False.elim (noInverse row member)⟩,
    initial.generationEq,initial.managed,initial.cursor,initial.frontier,initial.holes,initial.bounded,initial.pairwise⟩

/-- Canonical extras writes only runtime.extras. Actual root/tree/global
initialization and insertion preserve the initial address map, tape and active
thread. These equalities come from the real nested source setters. -/
theorem frame
    (onAccess : P→SyncObject.AccessKind→PlaceMachine.MachineM MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) Unit)
    (weakError : StoreBufferAllocError→StepError)
    (before : EvalCoreMachine.State Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (allocation : Allocation Provenance Unit) :
    let extras:=EvalCoreMachine.extras onAccess weakError
    let after:=AllocationConfiguredFormation.insertedState extras before tracker .stack allocation
    after.machine.memory=AllocationLifecycleFormation.inserted .stack allocation ∧
    after.machine.user.addresses=before.machine.user.addresses ∧
    EvalAllocationMachine.tape.get after=EvalAllocationMachine.tape.get before ∧
    after.machine.threads=before.machine.threads := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Pre-callback managed resources are formed from INITIAL resources and the
actual canonical allocation prefix. They are not a final-state input. -/
theorem resources
    (onAccess : P→SyncObject.AccessKind→PlaceMachine.MachineM MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) Unit)
    (weakError : StoreBufferAllocError→StepError)
    (before : EvalCoreMachine.State Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (allocation : Allocation Provenance Unit) (generation : AddressGenerationState) (sizes : AllocId→Size)
    (empty : before.machine.memory={})
    (initial : GlobalAddressReuseResources.State before.machine.memory before.machine.user.addresses generation sizes) :
    let extras:=EvalCoreMachine.extras onAccess weakError
    let after:=AllocationConfiguredFormation.insertedState extras before tracker .stack allocation
    GlobalAddressReuseResources.State after.machine.memory after.machine.user.addresses generation sizes := by
  have previous : GlobalAddressReuseResources.State ({} : MemoryState Provenance BorrowTree MiriMemoryKind)
      before.machine.user.addresses generation sizes := by simpa only [empty] using initial
  exact empty_memory before.machine.user.addresses generation sizes previous _
end DuplicatePrefix.AllocationEvalAddressTransport
